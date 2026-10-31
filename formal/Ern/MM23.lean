import Ern.MM02
import Ern.MM03

/-!
# Refinement MM-03.3 v0.3 → MM-02 v0.4 (milestone 2, passes 1 and 2)

Representation of the abstract states of MM-03.3 (module `Ern.MM03`) by the states of the abstract
machine of MM-02 (module `Ern.MM02`), refinement of every operation of MM-03 (R6), and simulation
of an execution. Both modules are imported unchanged; a lemma they lack is proved here.

The arbitrages of the task are cited as `K1`…`K5` (pass 1) and `L1`…`L8` (pass 2, which replace
the K arbitrages where they say so). The rules of the specifications are cited as `MM-02.x`
(MM-02 v0.4) and `MM-03.3 …` (MM-03.3 v0.3 révisée). Out of scope: concurrency, finite addresses,
representation of the metadata of arenas, low-level translation. The decisions not dictated by the
texts are listed in the reports `formal/reports/MM23_v0.1.md` (pass 1) and
`formal/reports/MM23_v0.1_p2.md` (pass 2), section (c); the gaps between the drafts and their
texts, section (f) of the pass-1 report.
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

/-- K3, the decidable part of the relation of representation between an MM-03 state `s3` and an
MM-02 state `s2`, for the layout `L`, the frame tokens `tok`, the provider tokens `ptok` and the
ghost `provOf` (L4: a root allocated by `alloc` ↦ its provider):
- `lwf`: `LayoutWF` (K1);
- `inj`: two distinct root places are in distinct allocations (K2: a root corresponds to an
  allocation; a part to a sub-range of the allocation of its root, by `LayoutWF.sameAlloc`);
- `tokens`: the allocation of a root owned by the frame `f` has the token `tok f` (K2);
- `provTokens`: the allocation of a root allocated from the provider `pr` has the token `ptok pr`
  (L4);
- `live`: every usable root has its allocation live (K3);
- `init`: every `Init` leaf has all its bytes initialised (K3; L3: a `Moved` or `Uninit` leaf
  imposes nothing);
- `freed`: a root dead by `free` has its allocation dead (K3);
- `exited`: a root dead by the exit of its frame has its allocation dead (K3);
- `leaked`: a root owned by a place, not usable and not freed keeps its allocation live (K3 for a
  root dead by `endUse`; L5 for owned storage that dies with a freed root or with its frame).
It does not read the contracts `K` (L3). -/
structure ReprB (tok ptok : Nat → Nat) (provOf : Nat → Option Nat) (L : Layout) (s3 : S3)
    (s2 : MM02.State) : Prop where
  lwf : LayoutWF L s3 s2
  inj : ∀ r < s3.P.length, ∀ r' < s3.P.length, RootPlace s3.P r → RootPlace s3.P r' → r ≠ r' →
    ∀ l ∈ footprint s3.P r, ∀ l' ∈ footprint s3.P r', (L l).alloc ≠ (L l').alloc
  tokens : ∀ r < s3.P.length, RootPlace s3.P r → OptP (s3.P[r]?) (fun pl =>
    OptP (tokOf tok pl.owner) (fun d => ∀ l ∈ footprint s3.P r,
      AllocP s2 (L l).alloc (·.freeAuth = some d)) True) True
  provTokens : ∀ r < s3.P.length, RootPlace s3.P r → OptP (provOf r) (fun pr =>
    ∀ l ∈ footprint s3.P r, AllocP s2 (L l).alloc (·.freeAuth = some (ptok pr))) True
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

set_option synthInstance.maxSize 8192 in
instance (tok ptok : Nat → Nat) (provOf : Nat → Option Nat) (L : Layout) (s3 : S3)
    (s2 : MM02.State) : Decidable (ReprB tok ptok provOf L s3 s2) :=
  decidable_of_iff
    (LayoutWF L s3 s2 ∧
     (∀ r < s3.P.length, ∀ r' < s3.P.length, RootPlace s3.P r → RootPlace s3.P r' → r ≠ r' →
      ∀ l ∈ footprint s3.P r, ∀ l' ∈ footprint s3.P r', (L l).alloc ≠ (L l').alloc) ∧
     (∀ r < s3.P.length, RootPlace s3.P r → OptP (s3.P[r]?) (fun pl =>
      OptP (tokOf tok pl.owner) (fun d => ∀ l ∈ footprint s3.P r,
        AllocP s2 (L l).alloc (·.freeAuth = some d)) True) True) ∧
     (∀ r < s3.P.length, RootPlace s3.P r → OptP (provOf r) (fun pr =>
      ∀ l ∈ footprint s3.P r, AllocP s2 (L l).alloc (·.freeAuth = some (ptok pr))) True) ∧
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
    ⟨fun ⟨a, b, c, c', d, e, f, g, h⟩ => ⟨a, b, c, c', d, e, f, g, h⟩,
     fun ⟨a, b, c, c', d, e, f, g, h⟩ => ⟨a, b, c, c', d, e, f, g, h⟩⟩

/-- K3, L3: relation of representation `Repr`: `ReprB`, and the MM-02 state has fresh identities
(`MM02.WF`, MM-02.A). Not decidable (`WF` quantifies over every identity); `ReprB` is. -/
structure Repr (tok ptok : Nat → Nat) (provOf : Nat → Option Nat) (L : Layout) (s3 : S3)
    (s2 : MM02.State) : Prop extends ReprB tok ptok provOf L s3 s2 where
  wf2 : MM02.WF s2

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

theorem exec_wf : ∀ (ops : List Op2) (s : MM02.State), MM02.WF s → MM02.WF (exec s ops)
  | [], _, h => h
  | o :: os, _, h => exec_wf os _ (by
      cases o
      · exact h
      · exact MM02.write_wf h _ _
      · exact MM02.dealloc_wf h _
      · exact MM02.alloc_wf h _ _ _ _ _)

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

/-- `ReprB` carries over when the MM-02 state only keeps its allocations (`Dom`) and the MM-03 state
keeps its places, stack, `dead` and `freed` marks, every leaf that becomes `Init` having its range
initialised (K3). -/
theorem ReprB.change {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 s2' : MM02.State}
    (hR : ReprB tok ptok provOf L s3 s2) (hd : Dom s2 s2') (hP : s3'.P = s3.P) (hF : s3'.F = s3.F)
    (hdead : s3'.dead = s3.dead) (hfr : s3'.freed = s3.freed)
    (hI : ∀ l < s3.P.length, isLeaf s3.P l → s3'.I l = .init →
      s3.I l = .init ∨ AllocP s2' (L l).alloc fun a => a.InitRange (L l).off (L l).len) :
    ReprB tok ptok provOf L s3' s2' := by
  have hU : ∀ q, s3'.Usable q ↔ s3.Usable q := fun q => S3.Usable.congr hP hF hdead
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hP, hF, hfr, hU]
  · exact hR.lwf.sameAlloc
  · exact hR.lwf.disjoint
  · exact fun l hl hlf => (hR.lwf.within l hl hlf).of_dom hd fun a a' _ e _ _ _ h => e ▸ h
  · exact hR.inj
  · exact fun r hr hrt => OptP.imp (hR.tokens r hr hrt) (fun _ h => OptP.imp h (fun _ h l hl =>
      (h l hl).of_dom hd fun _ _ _ _ _ e _ h => e ▸ h) id) id
  · exact fun r hr hrt => OptP.imp (hR.provTokens r hr hrt) (fun _ h l hl =>
      (h l hl).of_dom hd fun _ _ _ _ _ e _ h => e ▸ h) id
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
    {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {w : Nat → Nat → UInt8 × Option Nat}
    (hstat : ∀ s ac w, ObW.stat s ac w) :
    ∀ (ls : List Nat) (s3 : S3) (s2 : MM02.State), ReprB tok ptok provOf L s3 s2 →
      (∀ l ∈ ls, l < s3.P.length ∧ isLeaf s3.P l ∧ LiveAlloc s2 (L l).alloc) →
      DecAlong ObR ObW s2 (writeOps s2 L w ls) →
      AllOk C ObR ObW s2 (writeOps s2 L w ls) ∧
        ReprB tok ptok provOf L (write3Eff s3 ls) (exec s2 (writeOps s2 L w ls))
  | [], s3, s2, hR, _, _ => by
    refine ⟨trivial, hR.change (Dom.refl _) rfl rfl rfl rfl fun l _ _ h => .inl ?_⟩
    simpa [write3Eff] using h
  | l :: ls, s3, s2, hR, hls, hdec => by
    obtain ⟨hl, hlf, hlive⟩ := hls l (List.mem_cons_self ..)
    have hw := (hR.lwf.within l hl hlf)
    have hex : AllocP s2 (L l).alloc fun _ => True := hw.mono fun _ _ => trivial
    obtain ⟨s2₁, hs2₁⟩ : ∃ x, x = s2.write (leafAcc s2 L .write l) (w l) := ⟨_, rfl⟩
    have hd₁ : Dom s2 s2₁ := hs2₁ ▸ Dom.write _ _ _
    have hR₁ : ReprB tok ptok provOf L (write3Eff s3 [l]) s2₁ := by
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
    · show ReprB tok ptok provOf L _ (exec (Op2.eff _ s2) _); rw [e₁]; exact this.2

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

/-- K2, K3, L4: `ReprB` carries over when new places, a shape appended after the old ones, receive
one fresh allocation per new root (`allocOps`), laid out by `NewLayout`: the old places keep their
usability, `freed` marks and frame; the new places are usable and not freed; no leaf becomes
`Init`; a new root owned by the frame `f` has the token `tok f`; a new root allocated from the
provider `pr` (`provOf`) has the token `ptok pr`. -/
theorem repr_extend {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {hd : Holder}
    {ls : List (Option Nat × Option Nat × Nat)} {pl : Placement} {g : Nat → Geom}
    {fa : Option Nat} (hR : ReprB tok ptok provOf L s3 s2) (hwf : MM02.WF s2)
    (hP : s3'.P = shapeP s3.P hd ls) (hsh : ShapeOK s3.P.length ls)
    (hUold : ∀ q < s3.P.length, s3'.Usable q → s3.Usable q)
    (hUold' : ∀ q < s3.P.length, s3.Usable q → s3'.Usable q)
    (hUnew : ∀ i < ls.length, s3'.Usable (s3.P.length + i))
    (hfr : ∀ q, s3'.freed q = if s3.P.length ≤ q then false else s3.freed q)
    (hI : ∀ l, s3'.I l = .init → l < s3.P.length ∧ s3.I l = .init)
    (hgone : ∀ q < s3.P.length, ∀ pl : Place, s3.P[q]? = some pl → FrameGone s3'.F pl.owner →
      FrameGone s3.F pl.owner)
    (htok : ∀ f, hd = .frame f → fa = some (tok f))
    (hprov : ∀ i ∈ rootIdx ls, OptP (provOf (s3.P.length + i)) (fun pr => fa = some (ptok pr)) True)
    (hNL : NewLayout L s3'.P s3.P.length s2.next g (rootIdx ls)) :
    ReprB tok ptok provOf L s3' (exec s2 (allocOps pl g fa s2 (rootIdx ls))) := by
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
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · -- L4: provider tokens
    intro r hr hrt
    by_cases ho : r < s3.P.length
    · exact OptP.imp (hR.provTokens r ho ((hroot r ho).1 hrt)) (fun _ h l hl => by
        have h1 := h l ((hfp r ho l).1 hl)
        exact h1.of_eq (hold _ (h1.lt hwf))) id
    · obtain ⟨j, i, hj, rfl⟩ := hnr r hr hrt ho
      exact OptP.imp (hprov i (List.mem_of_getElem? hj)) (fun _ e l hl => by
        obtain ⟨-, -, b, hb⟩ := hna j i hj l hl
        exact ⟨_, hb, e⟩) id
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
theorem repr_of_nil {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 : S3} {s2 : MM02.State}
    (h : s3.P.length = 0) : ReprB tok ptok provOf L s3 s2 :=
  ⟨⟨fun _ hr => absurd hr (by omega), fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega)⟩, fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega), fun _ hr => absurd hr (by omega),
    fun _ hr => absurd hr (by omega),
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
statics in the fresh allocations (`NewLayout`, K1); no static root allocated by `alloc` in the
ghost `provOf` (L4); `dec` along the sequence and `stat` (K5). -/
theorem repr_init {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {statics : Statics} (hsh : ShapeOK 0 (statics.map (·.1))) {pl : Placement}
    (hpl : PlacementOK pl) {g : Nat → Geom}
    (hg : ∀ i ∈ rootIdx (statics.map (·.1)), 0 < (g i).align ∧ MM02.Pow2 (g i).align)
    {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout}
    (hNL : NewLayout L (S3.init statics).P 0 0 g (rootIdx (statics.map (·.1))))
    (hprov : ∀ i ∈ rootIdx (statics.map (·.1)), provOf i = none)
    {w : Nat → Nat → UInt8 × Option Nat} (hstat : ∀ s ac w, ObW.stat s ac w)
    (hdec : DecAlong ObR ObW MM02.State.empty (initOps pl g tok L w statics)) :
    AllOk C ObR ObW MM02.State.empty (initOps pl g tok L w statics) ∧
      Repr tok ptok provOf L (S3.init statics)
        (exec MM02.State.empty (initOps pl g tok L w statics)) := by
  -- the statics with every leaf `Uninit`
  let st0 : Statics := statics.map fun e => (e.1, false)
  have hmap : st0.map (·.1) = statics.map (·.1) := by simp [st0, List.map_map, Function.comp_def]
  have hP0 : (S3.init st0).P = (S3.init statics).P := by simp only [S3.init, hmap]
  have hsh0 : ShapeOK 0 (st0.map (·.1)) := hmap ▸ hsh
  have hnil : (S3.init ([] : Statics)).P.length = 0 := rfl
  -- allocations
  have hR1 : ReprB tok ptok provOf L (S3.init st0)
      (exec MM02.State.empty (allocOps pl g (some (tok 0)) MM02.State.empty
        (rootIdx (statics.map (·.1))))) := by
    refine repr_extend (s3 := S3.init []) (hd := .frame 0) (repr_of_nil hnil)
      (fun _ _ => rfl) ?_ (by rw [hnil]; exact hsh) (fun q hq => absurd hq (by omega))
      (fun q hq => absurd hq (by omega)) ?_ ?_ ?_ (fun q hq => absurd hq (by omega)) ?_ ?_ ?_
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
    · intro i hi; rw [hnil, Nat.zero_add, hprov i (hmap ▸ hi)]; trivial
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
  refine ⟨along_append.2 ⟨hok1, hw.1⟩, ⟨?_, exec_wf _ _ fun _ _ => rfl⟩⟩
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

/-! ## Leaves covered by active authorities -/

/-- MM-03.3 §2.1, clause 4 of `WF3`: the footprints of the authorities are made of leaves. The
`WF3` of the draft `Ern.MM03` only asks existing places (report, (f)). -/
def FpLeaves (s : S3) : Prop :=
  ∀ (a : Nat) (y : Authority), s.A[a]? = some y → ∀ l ∈ y.footprint, isLeaf s.P l

/-- K3, MM-03.3 §2.6 (`NoDangling`): under `WF3` and `FpLeaves`, a leaf covered by an active
authority belongs to a usable root, so its allocation is live. -/
theorem covered_live {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 : S3} {s2 : MM02.State} (hwf : WF3 s3)
    (hnd : NoDangling s3) (hfl : FpLeaves s3) (hR : ReprB tok ptok provOf L s3 s2) {a : Nat} {y : Authority}
    (hy : s3.A[a]? = some y) (ya : y.active = true) {l : Nat} (hl : l ∈ y.footprint) :
    l < s3.P.length ∧ isLeaf s3.P l ∧ LiveAlloc s2 (L l).alloc := by
  have hlP := hwf.fp a y hy l hl
  have hlf := hfl a y hy l hl
  obtain ⟨r, hr, hlr⟩ := exists_rootPlace hwf (l + 1) l (Nat.lt_succ_self l) hlP
  have hlfp : l ∈ footprint s3.P r := mem_footprint.2 ⟨hlP, hlf, hlr⟩
  have hu : s3.Usable r := Decidable.byContradiction fun hu => hnd a y hy ya r hu l hlfp hl
  exact ⟨hlP, hlf, hR.live r hr.1 hr hu l hlfp⟩

theorem covered_of_effective {s : S3} {a l : Nat} (h : effective s a l ≠ none) :
    ∃ y, s.A[a]? = some y ∧ y.active = true ∧ l ∈ y.footprint := by
  cases he : effective s a l with
  | none => exact absurd he h
  | some m => obtain ⟨y, hy, ya, hl, -⟩ := effective_some he; exact ⟨y, hy, ya, hl⟩

/-! ## R1, R2 (MM-03.3 §9.2; K4) -/

/-- R1 (MM-03.3 §9.2; K4: `read3` ↦ `ReadStep` on each range read, provenance the allocation of
the root, authority `read`): under `Repr`, `WF3`, `NoDangling` and `FpLeaves`, an `ok` read of
MM-03 gives, for each leaf read, a read of MM-02 of outcome `ok`, never `ub`, whose value is the
bytes of the range of the leaf, all initialised. Hypotheses on MM-02 (K5): `dec` for each access,
`stat`. -/
theorem r1_read3 {ObR : MM02.ReadOblSpec} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3}
    {s2 : MM02.State} {a : Nat} {ls : List Nat} (hwf : WF3 s3) (hnd : NoDangling s3)
    (hfl : FpLeaves s3) (hR : Repr tok ptok provOf L s3 s2) (h : Read3Step a ls s3 (.ok s3'))
    (hstat : ∀ s ac, ObR.stat s ac) (hdec : ∀ l ∈ ls, ObR.dec s2 (leafAcc s2 L .read l)) :
    ∀ l ∈ ls, ∃ al, s2.allocs (L l).alloc = some al ∧ al.InitRange (L l).off (L l).len ∧
      MM02.ReadStep ObR (leafAcc s2 L .read l) s2 (.ok (al.bytesAt (L l).off (L l).len)) ∧
      ¬ MM02.ReadStep ObR (leafAcc s2 L .read l) s2 .ub := by
  obtain ⟨⟨-, hc⟩, -⟩ := Guarded.ok_iff.1 h
  intro l hl
  obtain ⟨he, hi, -⟩ := hc l hl
  obtain ⟨y, hy, ya, hly⟩ := covered_of_effective he
  obtain ⟨hlP, hlf, hlive⟩ := covered_live hwf hnd hfl hR.toReprB hy ya hly
  obtain ⟨al, hal, ⟨hla, hsz⟩, hin⟩ :=
    (hlive.and (hR.lwf.within l hlP hlf)).and (hR.init l hlP hlf hi)
  have e : al.base + (L l).off - al.base = (L l).off := Nat.add_sub_cancel_left _ _
  have hread : MM02.Read s2 (leafAcc s2 L .read l) := by
    rw [leafAcc_of hal]
    exact ⟨al, hal, hla, ⟨Nat.le_add_right _ _, by simp only; omega⟩, by simp only [e]; exact hin,
      .inl rfl⟩
  have hok := MM02.ReadStep.ok (ObR := ObR) hal ⟨hread, hdec l hl, hstat _ _⟩
  rw [leafAcc_of hal] at hok ⊢
  simp only [e] at hok
  refine ⟨al, hal, hin, hok, fun hub => ?_⟩
  cases hub with
  | ub hn => rw [← leafAcc_of hal] at hn; exact hn ⟨hread, hdec l hl, hstat _ _⟩

/-- R2 for `write3` (MM-03.3 §9.2; K4: `write3` ↦ `WriteStep` on each range written, authority
`write`): under `Repr`, `WF3`, `NoDangling` and `FpLeaves`, an `ok` write of MM-03 gives writes of
MM-02 of outcome `ok`, and the arrival states are in `Repr`, whatever the bytes `w` written.
Hypotheses on MM-02 (K5): `dec` along the writes, `stat`. -/
theorem r2_write3 {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {a : Nat} {ls : List Nat}
    {w : Nat → Nat → UInt8 × Option Nat} (hwf : WF3 s3) (hnd : NoDangling s3) (hfl : FpLeaves s3)
    (hR : Repr tok ptok provOf L s3 s2) (h : Write3Step a ls s3 (.ok s3'))
    (hstat : ∀ s ac w, ObW.stat s ac w) (hdec : DecAlong ObR ObW s2 (writeOps s2 L w ls)) :
    AllOk C ObR ObW s2 (writeOps s2 L w ls) ∧
      Repr tok ptok provOf L s3' (exec s2 (writeOps s2 L w ls)) := by
  obtain ⟨⟨-, hc⟩, rfl⟩ := Guarded.ok_iff.1 h
  have := repr_writes (C := C) (ObR := ObR) hstat ls s3 s2 hR.toReprB (fun l hl => by
    obtain ⟨y, hy, ya, hly⟩ := covered_of_effective (by rw [(hc l hl).1]; exact fun h => by cases h)
    exact covered_live hwf hnd hfl hR.toReprB hy ya hly) hdec
  exact ⟨this.1, this.2, exec_wf _ _ hR.wf2⟩

/-- R2 for `writeShared` (MM-03.3 §9.2; O11; K4: `writeShared` ↦ `WriteStep`, authority `write`):
as `r2_write3`; the effective mode of the access may be `Observe` (O11.2). -/
theorem r2_writeShared {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {a : Nat}
    {ls : List Nat} {w : Nat → Nat → UInt8 × Option Nat} (hwf : WF3 s3) (hnd : NoDangling s3)
    (hfl : FpLeaves s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : WriteSharedStep k a ls s3 (.ok s3')) (hstat : ∀ s ac w, ObW.stat s ac w)
    (hdec : DecAlong ObR ObW s2 (writeOps s2 L w ls)) :
    AllOk C ObR ObW s2 (writeOps s2 L w ls) ∧
      Repr tok ptok provOf L s3' (exec s2 (writeOps s2 L w ls)) := by
  obtain ⟨⟨-, hc⟩, rfl⟩ := Guarded.ok_iff.1 h
  have := repr_writes (C := C) (ObR := ObR) hstat ls s3 s2 hR.toReprB (fun l hl => by
    obtain ⟨y, hy, ya, hly⟩ := covered_of_effective (hc l hl).1
    exact covered_live hwf hnd hfl hR.toReprB hy ya hly) hdec
  exact ⟨this.1, this.2, exec_wf _ _ hR.wf2⟩

/-! ## Two invariants of the reached states missing from the draft -/

/-- A place owned by a frame is not marked dead (MM-03.3.2: `endUse` and `free` mark dead only
storage owned by a value, O12, O13; a local of a frame dies by the exit of the frame, O7). -/
def FrameOwnedLive (s : S3) : Prop :=
  ∀ (q : Nat) (pl : Place) (f : Nat), s.P[q]? = some pl → pl.owner = .frame f → s.dead q = false

/-- `FpLeaves` carries over when the old leaves stay leaves and every leaf covered after the step
is covered before it or is a leaf of a place after it. -/
theorem FpLeaves.step {s s' : S3} (hwf : WF3 s) (h : FpLeaves s)
    (hleaf : ∀ l < s.P.length, isLeaf s.P l → isLeaf s'.P l)
    (hA : ∀ (j : Nat) (z : Authority), s'.A[j]? = some z → ∀ l ∈ z.footprint,
      (∃ (y : Authority) (j' : Nat), s.A[j']? = some y ∧ l ∈ y.footprint) ∨
        ∃ q, l ∈ footprint s'.P q) :
    FpLeaves s' := by
  intro j z hz l hl
  rcases hA j z hz l hl with ⟨y, j', hy, hly⟩ | ⟨q, hq⟩
  · exact hleaf l (hwf.fp j' y hy l hly) (h j' y hy l hly)
  · exact (mem_footprint.1 hq).2.1

/-- `FrameOwnedLive` carries over when every place owned by a frame after the step was owned by
that frame with the same `dead` mark before it, or is alive. -/
theorem FrameOwnedLive.step {s s' : S3} (h : FrameOwnedLive s)
    (hP : ∀ (q : Nat) (pl : Place) (f : Nat), s'.P[q]? = some pl → pl.owner = .frame f →
      (∃ pl' : Place, s.P[q]? = some pl' ∧ pl'.owner = .frame f ∧ s'.dead q = s.dead q) ∨
        s'.dead q = false) : FrameOwnedLive s' := by
  intro q pl f hq ho
  rcases hP q pl f hq ho with ⟨pl', hq', ho', e⟩ | e
  · rw [e]; exact h q pl' f hq' ho'
  · exact e

theorem isLeaf_of_parentOf {P P' : List Place} (hlen : P'.length = P.length)
    (hpar : parentOf P' = parentOf P) {l : Nat} (h : isLeaf P l) : isLeaf P' l := by
  simp only [isLeaf, hlen, hpar]; exact h

/-- `FpLeaves` and `FrameOwnedLive` are preserved by every step of `Reachable` (`Step`), under
`WF3`. -/
theorem step_fpLeaves_frameOwnedLive {k : K} {s s' : S3} (hwf : WF3 s)
    (h : FpLeaves s ∧ FrameOwnedLive s) (hs : Step k s s') :
    FpLeaves s' ∧ FrameOwnedLive s' := by
  obtain ⟨hfl, hfo⟩ := h
  -- steps changing no place and keeping each footprint
  have same : ∀ {s'' : S3}, s''.P = s.P → s''.dead = s.dead →
      (∀ (j : Nat) (z : Authority), s''.A[j]? = some z →
        ∃ y : Authority, s.A[j]? = some y ∧ z.footprint = y.footprint) →
      FpLeaves s'' ∧ FrameOwnedLive s'' := fun hP hd hA =>
    ⟨FpLeaves.step hwf hfl (fun l _ h => hP ▸ h) fun j z hz l hl => by
      obtain ⟨y, hy, e⟩ := hA j z hz; exact .inl ⟨y, j, hy, e ▸ hl⟩,
     FrameOwnedLive.step hfo fun q pl f hq ho => .inl ⟨pl, hP ▸ hq, ho, by rw [hd]⟩⟩
  have sameA : ∀ {s'' : S3}, s''.P = s.P → s''.dead = s.dead → s''.A = s.A →
      FpLeaves s'' ∧ FrameOwnedLive s'' := fun hP hd hA =>
    same hP hd fun j z hz => ⟨z, hA ▸ hz, rfl⟩
  -- steps appending authorities to `A`, places unchanged
  have app : ∀ {s'' : S3} (extra : List Authority), s''.P = s.P → s''.dead = s.dead →
      s''.A = s.A ++ extra → (∀ z ∈ extra, ∀ l ∈ z.footprint,
        (∃ (y : Authority) (j' : Nat), s.A[j']? = some y ∧ l ∈ y.footprint) ∨
          ∃ q, l ∈ footprint s.P q) →
      FpLeaves s'' ∧ FrameOwnedLive s'' := fun _ hP hd hA hx =>
    ⟨FpLeaves.step hwf hfl (fun l _ h => hP ▸ h) fun j z hz l hl => by
      rw [hA] at hz
      by_cases hj : j < s.A.length
      · rw [List.getElem?_append_left hj] at hz; exact .inl ⟨z, j, hz, hl⟩
      · rw [List.getElem?_append_right (by omega)] at hz
        rcases hx z (List.mem_of_getElem? hz) l hl with h | ⟨q, hq⟩
        · exact .inl h
        · exact .inr ⟨q, hP ▸ hq⟩,
     FrameOwnedLive.step hfo fun q pl f hq ho => .inl ⟨pl, hP ▸ hq, ho, by rw [hd]⟩⟩
  cases hs with
  | kernel hk =>
    cases hk with
    | derive hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      exact app [_] rfl rfl rfl fun z hz l hl => by
        rw [List.mem_singleton.1 hz] at hl; exact .inr ⟨_, hl⟩
    | split hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      refine app _ rfl rfl rfl fun z hz l hl => .inl ?_
      obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hz
      have := (hpre.2.2.2.1 r hr l hl).1
      unfold S3.afp at this; split at this
      · exact ⟨_, _, ‹_›, this⟩
      · cases this
    | release hs =>
      rename_i a
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      cases hy : s.A[a]? with
      | none => exact sameA (by simp [releaseEff, hy]) (by simp [releaseEff, hy]) (by simp [releaseEff, hy])
      | some y =>
        refine same (by simp [releaseEff, hy]) (by simp [releaseEff, hy]) fun j z hz => ?_
        rw [release_get hy] at hz; split at hz
        · rename_i e; subst e; cases hz; exact ⟨y, hy, rfl⟩
        · exact ⟨z, hz, rfl⟩
    | transfer hs =>
      rename_i src dst
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      have hlen : (transferEff s src dst).P.length = s.P.length := by simp [transferEff]
      have hpar : parentOf (transferEff s src dst).P = parentOf s.P := by
        funext i; simp only [parentOf, transferEff, List.getElem?_map]
        cases s.P[i]? with
        | none => rfl
        | some pl => simp only [Option.map_some, Option.bind_some]; split <;> rfl
      refine ⟨FpLeaves.step hwf hfl (fun l _ h => isLeaf_of_parentOf hlen hpar h) fun j z hz l hl => ?_,
        FrameOwnedLive.step hfo fun q pl f hq ho => ?_⟩
      · simp only [transferEff, List.getElem?_map] at hz
        cases hy : s.A[j]? with
        | none => rw [hy] at hz; cases hz
        | some y =>
          rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz
          refine .inl ⟨y, j, hy, ?_⟩
          split at hz <;> (subst hz; exact hl)
      · simp only [transferEff, List.getElem?_map] at hq
        cases hp : s.P[q]? with
        | none => rw [hp] at hq; cases hq
        | some pl' =>
          rw [hp] at hq; simp only [Option.map_some, Option.some.injEq] at hq
          split at hq
          · subst hq
            rename_i hh
            cases ho' : pl'.owner with
            | frame f' => rw [ho'] at hh; exact hh.elim
            | place r => rw [ho'] at ho; simp [mvTo] at ho
          · subst hq; exact .inl ⟨_, rfl, ho, rfl⟩
    | depend hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
    | enter hs =>
      rename_i ps ls
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      have hsh := enterPre_shapeOK hpre.1
      refine ⟨FpLeaves.step hwf hfl (fun l hl h => (shape_isLeaf_old hsh hl).2 h) fun j z hz l hl => ?_,
        FrameOwnedLive.step hfo fun q pl f hq ho => ?_⟩
      · rcases enter_get hz with ⟨-, y, hy, rfl⟩ | ⟨-, i, -, rfl⟩
        · refine .inl ⟨y, j, hy, ?_⟩
          split at hl <;> exact hl
        · exact .inr ⟨_, hl⟩
      · by_cases hqn : q < s.P.length
        · have : (enterEff s ps ls).P[q]? = s.P[q]? := enterP_lt hqn
          refine .inl ⟨pl, this ▸ hq, ho, ?_⟩
          simp [enterEff, Nat.not_le.2 hqn]
        · exact .inr (by simp [enterEff, Nat.le_of_not_lt hqn])
    | exit hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      unfold exitEff; split
      · rename_i F₀ _
        refine same rfl rfl fun j z hz => ?_
        rw [getElem?_mapI] at hz
        cases hy : s.A[j]? with
        | none => rw [hy] at hz; cases hz
        | some y =>
          rw [hy] at hz; simp only [Option.map_some, Option.some.injEq] at hz; subst hz
          refine ⟨y, rfl, ?_⟩
          unfold exitG; split
          · split <;> rfl
          · rfl
      · exact sameA rfl rfl rfl
    | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
    | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
    | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
    | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
    | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
    | endUse hs =>
      rename_i p
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      have hor := (endUseS_releases s p).trans cleanup_releases
      refine ⟨FpLeaves.step hwf hfl (fun l _ h => h) fun j z hz l hl => ?_, FrameOwnedLive.step hfo fun q pl f hq ho => ?_⟩
      · obtain ⟨y, hy, -, -, e, -⟩ := hor.2 j z hz; exact .inl ⟨y, j, hy, e ▸ hl⟩
      · refine .inl ⟨pl, hq, ho, ?_⟩
        simp only [endUseEff, cleanup, endUseS]
        have hq' : s.P[q]? = some pl := hq
        rw [hq']; simp [heldIn, ho]
    | free hs =>
      rename_i p auth
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      have hor := (freeS_releases s p).trans cleanup_releases
      refine ⟨FpLeaves.step hwf hfl (fun l _ h => h) fun j z hz l hl => ?_, FrameOwnedLive.step hfo fun q pl f hq ho => ?_⟩
      · obtain ⟨y, hy, -, -, e, -⟩ := hor.2 j z hz; exact .inl ⟨y, j, hy, e ▸ hl⟩
      · refine .inl ⟨pl, hq, ho, ?_⟩
        have hq' : s.P[q]? = some pl := hq
        have hnp : ¬ partOf s.P q p := fun hpart => by
          obtain ⟨pl₁, pr, h1, h2, e⟩ := hwf.ownerOf hpart
          have hor := hpre.2.2.2.1
          unfold OwnedRoot at hor; rw [h2] at hor
          rw [hq'] at h1; cases h1; rw [ho] at e
          obtain ⟨-, hpl⟩ := hor; rw [← e] at hpl; cases hpl
        simp [freeEff, cleanup, freeS, hnp]
    | alloc hs =>
      rename_i pr ow ls
      cases hs with
      | ok hst _ =>
        have hsh := hst.2.2.2.2.2.1
        refine ⟨FpLeaves.step hwf hfl (fun l hl h => (shape_isLeaf_old hsh hl).2 h) fun j z hz l hl => ?_,
          FrameOwnedLive.step hfo fun q pl f hq ho => ?_⟩
        · rcases alloc_get hz with ⟨-, hy⟩ | ⟨-, i, -, rfl⟩
          · exact .inl ⟨z, j, hy, hl⟩
          · exact .inr ⟨_, hl⟩
        · by_cases hqn : q < s.P.length
          · have : (allocEff s pr ow ls).P[q]? = s.P[q]? := allocP_lt hqn
            refine .inl ⟨pl, this ▸ hq, ho, ?_⟩
            simp [allocEff, Nat.not_le.2 hqn]
          · exact .inr (by simp [allocEff, Nat.le_of_not_lt hqn])
    | store hs =>
      rename_i a p
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      obtain ⟨y, hy, -⟩ := store_pre_auth hpre.1
      refine same (by rw [storeEff_eq hy]) (by rw [storeEff_eq hy]) fun j z hz => ?_
      rw [store_get hy] at hz; split at hz
      · rename_i e; subst e; cases hz; exact ⟨y, hy, rfl⟩
      · exact ⟨z, hz, rfl⟩
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact sameA rfl rfl rfl
  | issue hs =>
    cases hs with
    | ok har hst =>
      cases hst with
      | ok hstat _ _ _ =>
        refine app [_] rfl rfl rfl fun z hz l hl => .inl ?_
        rw [List.mem_singleton.1 hz] at hl
        have := hstat.2.2.1 l hl
        unfold S3.afp at this; split at this
        · exact ⟨_, _, ‹_›, this⟩
        · cases this
  | reset hs =>
    rename_i i via
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold resetAtEff; split
    · exact sameA rfl rfl rfl
    · exact sameA rfl rfl rfl

/-- `FpLeaves` and `FrameOwnedLive` hold on every reached state (MM-03.3 §2.1, §10), under
`DDSound k`, the hypothesis under which `WF3` is proved on reached states. -/
theorem reachable_fpLeaves_frameOwnedLive {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : Reachable k statics s) : FpLeaves s ∧ FrameOwnedLive s := by
  have st : ∀ {s s' : S3}, Reachable k statics s → FpLeaves s ∧ FrameOwnedLive s → Step k s s' →
      FpLeaves s' ∧ FrameOwnedLive s' := fun hr ih hs =>
    step_fpLeaves_frameOwnedLive (reachable_invariants hdd hr).1 ih hs
  induction h with
  | init _ =>
    refine ⟨fun j z hz l hl => ?_, fun _ _ _ _ _ => rfl⟩
    obtain ⟨i, -, rfl⟩ := init_get hz
    exact (mem_footprint.1 hl).2.1
  | derive hr hs ih => exact st hr ih (.kernel (.derive hs))
  | split hr hs ih => exact st hr ih (.kernel (.split hs))
  | release hr hs ih => exact st hr ih (.kernel (.release hs))
  | transfer hr hs ih => exact st hr ih (.kernel (.transfer hs))
  | depend hr hs ih => exact st hr ih (.kernel (.depend hs))
  | enter hr hs ih => exact st hr ih (.kernel (.enter hs))
  | exit hr hs ih => exact st hr ih (.kernel (.exit hs))
  | read hr hs ih => exact st hr ih (.kernel (.read hs))
  | write hr hs ih => exact st hr ih (.kernel (.write hs))
  | writeShared hr hs ih => exact st hr ih (.kernel (.writeShared hs))
  | pin hr hs ih => exact st hr ih (.kernel (.pin hs))
  | unpin hr hs ih => exact st hr ih (.kernel (.unpin hs))
  | endUse hr hs ih => exact st hr ih (.kernel (.endUse hs))
  | free hr hs ih => exact st hr ih (.kernel (.free hs))
  | alloc hr hs ih => exact st hr ih (.kernel (.alloc hs))
  | newArena hr hs ih => exact st hr ih (.newArena hs)
  | issue hr hs ih => exact st hr ih (.issue hs)
  | reset hr hs ih => exact st hr ih (.reset hs)
  | store hr hs ih => exact st hr ih (.kernel (.store hs))

/-! ## R1, R2 on reached states -/

/-- R1 on the reached states (MM-03.3 §9.2, §10), under `DDSound k`: `WF3`, `NoDangling` and
`FpLeaves` hold there. -/
theorem r1_read3_reachable {k : K} {statics : Statics} {ObR : MM02.ReadOblSpec} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {a : Nat} {ls : List Nat} (hdd : DDSound k)
    (hr : Reachable k statics s3) (hR : Repr tok ptok provOf L s3 s2) (h : Read3Step a ls s3 (.ok s3'))
    (hstat : ∀ s ac, ObR.stat s ac) (hdec : ∀ l ∈ ls, ObR.dec s2 (leafAcc s2 L .read l)) :
    ∀ l ∈ ls, ∃ al, s2.allocs (L l).alloc = some al ∧ al.InitRange (L l).off (L l).len ∧
      MM02.ReadStep ObR (leafAcc s2 L .read l) s2 (.ok (al.bytesAt (L l).off (L l).len)) ∧
      ¬ MM02.ReadStep ObR (leafAcc s2 L .read l) s2 .ub :=
  r1_read3 (reachable_invariants hdd hr).1 (reachable_invariants hdd hr).2.1.nd
    (reachable_fpLeaves_frameOwnedLive hdd hr).1 hR h hstat hdec

/-- R2 for `write3` on the reached states (MM-03.3 §9.2, §10), under `DDSound k`. -/
theorem r2_write3_reachable {k : K} {statics : Statics} {C : Nat → Nat → Prop}
    {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout}
    {s3 s3' : S3} {s2 : MM02.State} {a : Nat} {ls : List Nat} {w : Nat → Nat → UInt8 × Option Nat}
    (hdd : DDSound k) (hr : Reachable k statics s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : Write3Step a ls s3 (.ok s3')) (hstat : ∀ s ac w, ObW.stat s ac w)
    (hdec : DecAlong ObR ObW s2 (writeOps s2 L w ls)) :
    AllOk C ObR ObW s2 (writeOps s2 L w ls) ∧ Repr tok ptok provOf L s3' (exec s2 (writeOps s2 L w ls)) :=
  r2_write3 (reachable_invariants hdd hr).1 (reachable_invariants hdd hr).2.1.nd
    (reachable_fpLeaves_frameOwnedLive hdd hr).1 hR h hstat hdec

/-- R2 for `writeShared` on the reached states (MM-03.3 §9.2, §10), under `DDSound k`. -/
theorem r2_writeShared_reachable {k : K} {statics : Statics} {C : Nat → Nat → Prop}
    {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout}
    {s3 s3' : S3} {s2 : MM02.State} {a : Nat} {ls : List Nat} {w : Nat → Nat → UInt8 × Option Nat}
    (hdd : DDSound k) (hr : Reachable k statics s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : WriteSharedStep k a ls s3 (.ok s3')) (hstat : ∀ s ac w, ObW.stat s ac w)
    (hdec : DecAlong ObR ObW s2 (writeOps s2 L w ls)) :
    AllOk C ObR ObW s2 (writeOps s2 L w ls) ∧ Repr tok ptok provOf L s3' (exec s2 (writeOps s2 L w ls)) :=
  r2_writeShared (reachable_invariants hdd hr).1 (reachable_invariants hdd hr).2.1.nd
    (reachable_fpLeaves_frameOwnedLive hdd hr).1 hR h hstat hdec

/-! ## Allocation of a root place (K2) -/

/-- Every place has a leaf (MM-03.3.2), under `WF3`: a part comes after its parent. -/
theorem exists_leaf {s : S3} (hwf : WF3 s) : ∀ m q, s.P.length ≤ q + m → q < s.P.length →
    ∃ l, l ∈ footprint s.P q
  | 0, q, hm, hq => absurd hq (by omega)
  | m + 1, q, hm, hq => by
    by_cases h : ∃ r, r < s.P.length ∧ parentOf s.P r = some q
    · obtain ⟨r, hr, hp⟩ := h
      have hlt := (hwf.parent_lt hp).1
      obtain ⟨l, hl⟩ := exists_leaf hwf m r (by omega) hr
      exact ⟨l, footprint_sub hwf ⟨hr, .inr (by rw [chain_cons hp hlt]; exact List.mem_cons_self ..)⟩
        hl⟩
    · exact ⟨q, mem_footprint.2 ⟨hq, fun r hr e => h ⟨r, hr, e⟩, hq, .inl rfl⟩⟩

/-- K2: the allocation of the root place `r`, read on the first leaf of its footprint. -/
def rootAlloc (L : Layout) (P : List Place) (r : Nat) : Nat := (L ((footprint P r).headD r)).alloc

theorem headD_mem_footprint {s : S3} (hwf : WF3 s) {r : Nat} (hr : r < s.P.length) :
    (footprint s.P r).headD r ∈ footprint s.P r := by
  obtain ⟨l, hl⟩ := exists_leaf hwf s.P.length r (by omega) hr
  cases h : footprint s.P r with
  | nil => rw [h] at hl; cases hl
  | cons x xs => exact List.mem_cons_self ..

/-- K1 (a), K2: every leaf of a root place is in the allocation of the root. -/
theorem rootAlloc_eq {L : Layout} {s3 : S3} {s2 : MM02.State} (hwf : WF3 s3)
    (hlw : LayoutWF L s3 s2) {r : Nat} (hr : RootPlace s3.P r) {l : Nat}
    (hl : l ∈ footprint s3.P r) : (L l).alloc = rootAlloc L s3.P r :=
  hlw.sameAlloc r hr.1 hr l hl _ (headD_mem_footprint hwf hr.1)

/-! ## Deallocations (K4: `free`, `exitFrame`) -/

/-- K4 (`free`, `exitFrame`): one deallocation of each allocation of `ids`, with the
deallocation authority `au` (MM-02.D). -/
def deallocOps (ids : List Nat) (au : Nat) : List Op2 := ids.map fun i => .dealloc i au

theorem dealloc_allocs (s : MM02.State) (id i : Nat) :
    (s.dealloc id).allocs i =
      if i = id then (s.allocs i).map (fun a => { a with live := false }) else s.allocs i := rfl

theorem exec_deallocOps (au : Nat) : ∀ (ids : List Nat) (s : MM02.State) (j : Nat),
    (exec s (deallocOps ids au)).allocs j =
      if j ∈ ids then (s.allocs j).map (fun a => { a with live := false }) else s.allocs j
  | [], s, j => by simp [deallocOps, exec]
  | i :: is, s, j => by
    show (exec (s.dealloc i) (deallocOps is au)).allocs j = _
    rw [exec_deallocOps au is, dealloc_allocs]
    by_cases h2 : j = i
    · subst h2
      have hm : j ∈ j :: is := List.mem_cons_self ..
      by_cases h1 : j ∈ is
      · simp only [h1, hm, ↓reduceIte]; cases s.allocs j <;> rfl
      · simp only [h1, hm, ↓reduceIte]
    · have hm : j ∈ i :: is ↔ j ∈ is := by simp [h2]
      by_cases h1 : j ∈ is
      · simp only [hm, h1, h2, ↓reduceIte]
      · simp only [hm, h1, h2, ↓reduceIte]

/-- K4: the deallocations of distinct live allocations whose token is compatible with `au` have
the outcome `ok` (MM-02.D). -/
theorem deallocOps_ok {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {au : Nat} : ∀ (ids : List Nat) (s : MM02.State), ids.Pairwise (· ≠ ·) →
      (∀ i ∈ ids, AllocP s i fun a => a.live = true ∧ ∃ d, a.freeAuth = some d ∧ C au d) →
      AllOk C ObR ObW s (deallocOps ids au)
  | [], _, _, _ => trivial
  | i :: is, s, hp, h => by
    obtain ⟨hne, hp⟩ := List.pairwise_cons.1 hp
    obtain ⟨a, ha, hl, d, hd, hc⟩ := h i (List.mem_cons_self ..)
    refine ⟨.ok ⟨a, ha, hl, d, hd, hc⟩, deallocOps_ok is _ hp fun j hj => ?_⟩
    have hji : j ≠ i := fun e => hne j hj e.symm
    exact (h j (List.mem_cons_of_mem _ hj)).of_eq (by
      show (s.dealloc i).allocs j = s.allocs j
      rw [dealloc_allocs]; simp only [hji, ↓reduceIte])

/-- K3: `ReprB` carries over when the places, the stack and the `freed` marks do not change, no
place becomes usable and no leaf becomes `Init` (`endUse` and the steps without MM-02 step). -/
theorem ReprB.shrink {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State}
    (hR : ReprB tok ptok provOf L s3 s2) (hP : s3'.P = s3.P) (hF : s3'.F = s3.F) (hfr : s3'.freed = s3.freed)
    (hU : ∀ q, s3'.Usable q → s3.Usable q) (hI : ∀ l, s3'.I l = .init → s3.I l = .init) :
    ReprB tok ptok provOf L s3' s2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hP, hF, hfr]
  · exact hR.lwf.sameAlloc
  · exact hR.lwf.disjoint
  · exact hR.lwf.within
  · exact hR.inj
  · exact hR.tokens
  · exact hR.provTokens
  · exact fun r hr hrt hu => hR.live r hr hrt (hU r hu)
  · exact fun l hl hlf hi => hR.init l hl hlf (hI l hi)
  · exact hR.freed
  · exact hR.exited
  · intro r hr hrt hu hf ho
    by_cases hu' : s3.Usable r
    · exact hR.live r hr hrt hu'
    · exact hR.leaked r hr hrt hu' hf ho

/-- K3, K4: `Repr` carries over to the deallocation of the allocations `ids` when the places do
not change, no leaf becomes `Init`, a root usable after was usable before and keeps its
allocation, a root freed or exited after was so before or has its allocation deallocated, and a
leaked root after was usable or not freed before and keeps its allocation. -/
theorem repr_deallocs {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State}
    (hR : ReprB tok ptok provOf L s3 s2) (ids : List Nat) (au : Nat) (hP : s3'.P = s3.P)
    (hI : ∀ l, s3'.I l = .init → s3.I l = .init)
    (hlive : ∀ r < s3.P.length, RootPlace s3.P r → s3'.Usable r →
      s3.Usable r ∧ ∀ l ∈ footprint s3.P r, (L l).alloc ∉ ids)
    (hfreed : ∀ r < s3.P.length, RootPlace s3.P r → s3'.freed r = true →
      s3.freed r = true ∨ ∀ l ∈ footprint s3.P r, (L l).alloc ∈ ids)
    (hexit : ∀ r < s3.P.length, RootPlace s3.P r →
      OptP (s3.P[r]?) (fun pl => FrameGone s3'.F pl.owner) False →
      OptP (s3.P[r]?) (fun pl => FrameGone s3.F pl.owner) False ∨
        ∀ l ∈ footprint s3.P r, (L l).alloc ∈ ids)
    (hleak : ∀ r < s3.P.length, RootPlace s3.P r → ¬ s3'.Usable r → s3'.freed r = false →
      OptP (s3.P[r]?) (fun pl => pl.owner.isPlace = true) False →
      (s3.Usable r ∨ s3.freed r = false) ∧ ∀ l ∈ footprint s3.P r, (L l).alloc ∉ ids) :
    ReprB tok ptok provOf L s3' (exec s2 (deallocOps ids au)) := by
  have hall := exec_deallocOps au ids s2
  have hkeep : ∀ j (p : MM02.Alloc → Prop), AllocP s2 j p → j ∉ ids →
      AllocP (exec s2 (deallocOps ids au)) j p := fun j p h hj =>
    h.of_eq (by rw [hall]; simp only [hj, ↓reduceIte])
  have hmeta : ∀ j (p : MM02.Alloc → Prop), AllocP s2 j p →
      (∀ a : MM02.Alloc, p a → p { a with live := false }) →
      AllocP (exec s2 (deallocOps ids au)) j p := fun j p h hp => by
    obtain ⟨a, ha, hpa⟩ := h
    by_cases hj : j ∈ ids
    · exact ⟨_, by rw [hall]; simp only [hj, ↓reduceIte, ha, Option.map_some], hp a hpa⟩
    · exact ⟨a, by rw [hall]; simp only [hj, ↓reduceIte, ha], hpa⟩
  have hdead : ∀ j (p : MM02.Alloc → Prop), AllocP s2 j p → j ∈ ids →
      DeadAlloc (exec s2 (deallocOps ids au)) j := fun j p h hj => by
    obtain ⟨a, ha, -⟩ := h
    exact ⟨{ a with live := false }, by rw [hall]; simp only [hj, ↓reduceIte, ha, Option.map_some],
      rfl⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hP]
  · exact hR.lwf.sameAlloc
  · exact hR.lwf.disjoint
  · exact fun l hl hlf => hmeta _ _ (hR.lwf.within l hl hlf) fun _ h => h
  · exact hR.inj
  · exact fun r hr hrt => OptP.imp (hR.tokens r hr hrt) (fun _ h => OptP.imp h
      (fun _ h l hl => hmeta _ _ (h l hl) fun _ h => h) id) id
  · exact fun r hr hrt => OptP.imp (hR.provTokens r hr hrt)
      (fun _ h l hl => hmeta _ _ (h l hl) fun _ h => h) id
  · intro r hr hrt hu l hl
    obtain ⟨hu', hn⟩ := hlive r hr hrt hu
    exact hkeep _ _ (hR.live r hr hrt hu' l hl) (hn l hl)
  · exact fun l hl hlf hi => hmeta _ _ (hR.init l hl hlf (hI l hi)) fun _ h => h
  · intro r hr hrt hf l hl
    rcases hfreed r hr hrt hf with h | h
    · exact hmeta _ _ (hR.freed r hr hrt h l hl) fun _ _ => rfl
    · exact hdead _ _ (hR.lwf.within l (mem_footprint.1 hl).1 (mem_footprint.1 hl).2.1) (h l hl)
  · intro r hr hrt hg l hl
    rcases hexit r hr hrt hg with h | h
    · exact hmeta _ _ (hR.exited r hr hrt h l hl) fun _ _ => rfl
    · exact hdead _ _ (hR.lwf.within l (mem_footprint.1 hl).1 (mem_footprint.1 hl).2.1) (h l hl)
  · intro r hr hrt hu hf ho l hl
    obtain ⟨h, hn⟩ := hleak r hr hrt hu hf ho
    have hl' : LiveAlloc s2 (L l).alloc := by
      by_cases hu' : s3.Usable r
      · exact hR.live r hr hrt hu' l hl
      · exact hR.leaked r hr hrt hu' (h.resolve_left hu') ho l hl
    exact hkeep _ _ hl' (hn l hl)

/-! ## Leaves of a transfer under `SameShape` (MM-03.3 O4.2, J1 ordered isomorphism) -/

theorem posIn_cons_eq {a r : Nat} {l : List Nat} (h : a = r) : posIn r (a :: l) = 0 := by
  simp only [posIn, h, ↓reduceIte]

theorem posIn_cons_ne {a r : Nat} {l : List Nat} (h : ¬ a = r) :
    posIn r (a :: l) = posIn r l + 1 := by
  simp only [posIn, h, ↓reduceIte]

/-- A position in a list determines the member it was computed for (MM-03.3 O4.2: the identity
of a structural field is its position). -/
theorem posIn_inj : ∀ {l : List Nat} {r₁ r₂ : Nat}, r₁ ∈ l → r₂ ∈ l →
    posIn r₁ l = posIn r₂ l → r₁ = r₂
  | [], _, _, h, _, _ => absurd h List.not_mem_nil
  | a :: l, r₁, r₂, h₁, h₂, e => by
    by_cases e₁ : a = r₁ <;> by_cases e₂ : a = r₂
    · exact e₁.symm.trans e₂
    · rw [posIn_cons_eq e₁, posIn_cons_ne e₂] at e; exact absurd e.symm (Nat.succ_ne_zero _)
    · rw [posIn_cons_ne e₁, posIn_cons_eq e₂] at e; exact absurd e (Nat.succ_ne_zero _)
    · rw [posIn_cons_ne e₁, posIn_cons_ne e₂] at e
      have h₁' : r₁ ∈ l := (List.mem_cons.1 h₁).resolve_left (Ne.symm e₁)
      have h₂' : r₂ ∈ l := (List.mem_cons.1 h₂).resolve_left (Ne.symm e₂)
      exact posIn_inj h₁' h₂' (Nat.succ.inj e)

/-- In a strictly increasing list, a value occurs at one index only. -/
theorem index_inj_of_lt : ∀ {l : List Nat}, l.Pairwise (· < ·) → ∀ {i j x : Nat},
    l[i]? = some x → l[j]? = some x → i = j
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, hp, 0, 0, _, _, _ => rfl
  | a :: l, hp, 0, j + 1, x, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₁; subst h₁
    simp only [List.getElem?_cons_succ] at h₂
    exact absurd ((List.pairwise_cons.1 hp).1 _ (List.mem_of_getElem? h₂)) (Nat.lt_irrefl a)
  | a :: l, hp, i + 1, 0, x, h₁, h₂ => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h₂; subst h₂
    simp only [List.getElem?_cons_succ] at h₁
    exact absurd ((List.pairwise_cons.1 hp).1 _ (List.mem_of_getElem? h₁)) (Nat.lt_irrefl a)
  | _ :: _, hp, i + 1, j + 1, _, h₁, h₂ => by
    simp only [List.getElem?_cons_succ] at h₁ h₂
    exact congrArg (· + 1) (index_inj_of_lt (List.pairwise_cons.1 hp).2 h₁ h₂)

/-- The children of a place are in strictly increasing index order (J1: children are ordered by
index). -/
theorem kids_lt (P : List Place) (x : Nat) : (kids P x).Pairwise (· < ·) :=
  (pairwise_lt_range P.length).filter _

/-- A strict part of `src` has a parent that is a part of `src` (MM-03.3.2, composition). -/
theorem partOf_parent_of_ne {P : List Place} {r src p : Nat} (hr : partOf P r src)
    (hne : r ≠ src) (hp : parentOf P r = some p) (hlt : p < r) : partOf P p src := by
  have hc := hr.2.resolve_left hne
  rw [chain_cons hp hlt] at hc
  refine ⟨Nat.lt_trans hlt hr.1, ?_⟩
  rcases List.mem_cons.1 hc with h | h
  · exact .inl h.symm
  · exact .inr h

/-- One step of `corr` on a strict part `r` of `src` (J1): `r` has a parent `p`, a part of `src`,
and the image of `r` is the child, at the position of `r`, of the image of `p`. -/
theorem corr_parent {s : S3} (hw : WF3 s) {src dst r x : Nat} (hr : partOf s.P r src)
    (hne : r ≠ src) (h : corr s.P src dst r = some x) :
    ∃ p p', parentOf s.P r = some p ∧ partOf s.P p src ∧ corr s.P src dst p = some p' ∧
      (kids s.P p')[posIn r (kids s.P p)]? = some x ∧ parentOf s.P x = some p' := by
  cases hp : parentOf s.P r with
  | none =>
    have hc := hr.2.resolve_left hne
    rw [chain_none hp] at hc; exact absurd hc List.not_mem_nil
  | some p =>
    have hlt := (hw.parent_lt hp).1
    rw [corr_step hne hp hlt] at h
    cases hc : corr s.P src dst p with
    | none => rw [hc] at h; cases h
    | some p' =>
      rw [hc] at h; simp only [Option.bind_some] at h
      exact ⟨p, p', rfl, partOf_parent_of_ne hr hne hp hlt, hc, h,
        (mem_kids.1 (getElem?_mem h)).2⟩

/-- `dst` is the image of no strict part of `src` (J1): the image of a strict part has as parent
a part of `dst`, which cannot be a parent of `dst`. -/
theorem corr_ne_dst {s : S3} (hw : WF3 s) {src dst r : Nat} (hd : dst < s.P.length)
    (hr : partOf s.P r src) (hne : r ≠ src) : corr s.P src dst r ≠ some dst := by
  intro h
  obtain ⟨p, p', -, -, hc, -, hx⟩ := corr_parent hw hr hne h
  have hlt := (hw.parent_lt hx).1
  rcases (corr_partOf hw hd (p + 1) p p' (Nat.lt_succ_self p) hc).2 with rfl | hch
  · exact Nat.lt_irrefl _ hlt
  · exact Nat.lt_asymm hlt (chain_lt hch)

/-- `corr` is injective on the parts of `src` (MM-03.3 O4.2, J1: all nodes are matched by
position, so two parts of `src` have the same image only if they are equal). -/
theorem corr_inj_aux {s : S3} (hw : WF3 s) {src dst : Nat} (hd : dst < s.P.length) :
    ∀ n r₁ r₂ x, r₁ + r₂ < n → partOf s.P r₁ src → partOf s.P r₂ src →
      corr s.P src dst r₁ = some x → corr s.P src dst r₂ = some x → r₁ = r₂
  | 0, _, _, _, h, _, _, _, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, r₁, r₂, x, hn, h₁, h₂, e₁, e₂ => by
    by_cases s₁ : r₁ = src <;> by_cases s₂ : r₂ = src
    · exact s₁.trans s₂.symm
    · subst s₁; rw [corr_src] at e₁; cases e₁
      exact absurd e₂ (corr_ne_dst hw hd h₂ s₂)
    · subst s₂; rw [corr_src] at e₂; cases e₂
      exact absurd e₁ (corr_ne_dst hw hd h₁ s₁)
    · obtain ⟨p₁, p₁', hp₁, hq₁, hc₁, hk₁, hx₁⟩ := corr_parent hw h₁ s₁ e₁
      obtain ⟨p₂, p₂', hp₂, hq₂, hc₂, hk₂, hx₂⟩ := corr_parent hw h₂ s₂ e₂
      rw [hx₁] at hx₂; cases hx₂
      have l₁ := (hw.parent_lt hp₁).1
      have l₂ := (hw.parent_lt hp₂).1
      obtain rfl := corr_inj_aux hw hd n p₁ p₂ p₁' (by omega) hq₁ hq₂ hc₁ hc₂
      exact posIn_inj (mem_kids.2 ⟨h₁.1, hp₁⟩) (mem_kids.2 ⟨h₂.1, hp₂⟩)
        (index_inj_of_lt (kids_lt _ _) hk₁ hk₂)

/-- The leaves of the source of a transfer correspond to leaves of the destination
(MM-03.3 O4.2, J1 ordered isomorphism `SameShape`). -/
theorem corr_leaf_fwd {s : S3} (hw : WF3 s) {src dst : Nat} (hd : dst < s.P.length)
    (hsh : SameShape s.P src dst) {l : Nat} (hl : l ∈ footprint s.P src) :
    ∃ l', corr s.P src dst l = some l' ∧ l' ∈ footprint s.P dst := by
  obtain ⟨hlt, hleaf, hpart⟩ := mem_footprint.1 hl
  have h1 := hsh.1 l (List.mem_range.2 hlt) hpart
  cases hc : corr s.P src dst l with
  | none => rw [hc] at h1; exact (h1 : False).elim
  | some l' =>
    rw [hc] at h1
    have h1 : (kids s.P l').length = (kids s.P l).length := h1
    rw [kids_nil_iff.2 hleaf] at h1
    have hp := corr_partOf hw hd (l + 1) l l' (Nat.lt_succ_self l) hc
    exact ⟨l', rfl,
      mem_footprint.2 ⟨hp.1, kids_nil_iff.1 (List.eq_nil_of_length_eq_zero h1), hp⟩⟩

/-- Every leaf of the destination of a transfer is the image of a leaf of the source
(MM-03.3 O4.2, J1 ordered isomorphism `SameShape`: all nodes are matched). -/
theorem corr_leaf_back {s : S3} {src dst : Nat} (hsh : SameShape s.P src dst)
    {l' : Nat} (hl' : l' ∈ footprint s.P dst) :
    ∃ l ∈ footprint s.P src, corr s.P src dst l = some l' := by
  obtain ⟨hlt', hleaf', hpart'⟩ := mem_footprint.1 hl'
  obtain ⟨r, hr, hrs, hc⟩ := hsh.2 l' (List.mem_range.2 hlt') hpart'
  have h1 := hsh.1 r hr hrs
  rw [hc] at h1
  have h1 : (kids s.P l').length = (kids s.P r).length := h1
  rw [kids_nil_iff.2 hleaf'] at h1
  exact ⟨r, mem_footprint.2 ⟨List.mem_range.1 hr,
    kids_nil_iff.1 (List.eq_nil_of_length_eq_zero h1.symm), hrs⟩, hc⟩

/-- `corr` is injective on the parts of the source of a transfer (MM-03.3 O4.2, J1 ordered
isomorphism: the `i`-th child corresponds to the `i`-th child). -/
theorem corr_inj {s : S3} (hw : WF3 s) {src dst : Nat} (hd : dst < s.P.length)
    {r₁ r₂ x : Nat} (h₁ : partOf s.P r₁ src) (h₂ : partOf s.P r₂ src)
    (e₁ : corr s.P src dst r₁ = some x) (e₂ : corr s.P src dst r₂ = some x) : r₁ = r₂ :=
  corr_inj_aux hw hd (r₁ + r₂ + 1) r₁ r₂ x (Nat.lt_succ_self _) h₁ h₂ e₁ e₂

/-! ## R6 (MM-03.3 §9.2; K4) -/

/-- MM-03.3.8 (`Deallocable`, `FreeCompat`) and K4 ("`free` ↦ `DeallocStep`, autorité
`Compatible` issue de `FreeCompat`"): obligation of the contracts towards MM-02 for `free p auth` in
the state `s2`: when the contracts permit it, every leaf of `p` is in an allocation with a token
compatible with `auth` (MM-02.D). -/
def FreeSound (k : K) (C : Nat → Nat → Prop) (L : Layout) (s3 : S3) (s2 : MM02.State)
    (p auth : Nat) : Prop :=
  k.Deallocable p → k.FreeCompat p auth → ∀ l ∈ footprint s3.P p,
    AllocP s2 (L l).alloc fun a => ∃ d, a.freeAuth = some d ∧ C auth d

/-- K2: the token proper to each frame is compatible with itself (MM-02.D): the authority that
`exitFrame` presents for an automatic allocation of the frame `f` is `tok f`, compatible by
construction. -/
def TokCompat (C : Nat → Nat → Prop) (tok : Nat → Nat) : Prop := ∀ f, C (tok f) (tok f)

theorem exec_readOps (s2 s2' : MM02.State) (L : Layout) :
    ∀ ls : List Nat, exec s2 (readOps s2' L ls) = s2
  | [] => rfl
  | _ :: ls => exec_readOps s2 s2' L ls

/-- R6 for `read3` (MM-03.3 §9.2; K4): the reads of MM-02 have the outcome `ok` and the arrival
states are in `Repr`; hypotheses of `r1_read3`. -/
theorem r6_read3 {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {a : Nat} {ls : List Nat}
    (hwf : WF3 s3) (hnd : NoDangling s3) (hfl : FpLeaves s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : Read3Step a ls s3 (.ok s3')) (hstat : ∀ s ac, ObR.stat s ac)
    (hdec : ∀ l ∈ ls, ObR.dec s2 (leafAcc s2 L .read l)) :
    AllOk C ObR ObW s2 (readOps s2 L ls) ∧ Repr tok ptok provOf L s3' (exec s2 (readOps s2 L ls)) := by
  have h1 := r1_read3 hwf hnd hfl hR h hstat hdec
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
  refine ⟨?_, by rw [exec_readOps]; exact hR⟩
  have : ∀ ls', (∀ l ∈ ls', l ∈ ls) → AllOk C ObR ObW s2 (readOps s2 L ls') := fun ls' => by
    induction ls' with
    | nil => exact fun _ => trivial
    | cons l ls' ih =>
      intro hs
      obtain ⟨al, -, -, hok, -⟩ := h1 l (hs l (List.mem_cons_self ..))
      exact ⟨⟨_, hok⟩, ih fun l' hl' => hs l' (List.mem_cons_of_mem _ hl')⟩
  exact this ls fun _ h => h

/-- R6 for `alloc` of outcome `ok` (MM-03.3 §9.2, O14; K4: `alloc` `ok` ↦ `AllocStep`; L2: the
shape has one root; L4: the token of the allocation is the token `ptok pr` of the provider, and the
ghost `provOf` maps the new root to `pr`): the allocation of MM-02, at the base chosen by the
placement, has the outcome `ok`, and the arrival states are in `Repr`, for every geometry of valid
alignment and every layout of the new leaves in the fresh allocation (`NewLayout`). -/
theorem r6_alloc {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout} {s3 s3' : S3}
    {s2 : MM02.State} {pr ow : Nat} {ls : List (Option Nat × Option Nat × Nat)} {pl : Placement}
    {g : Nat → Geom} {i : Nat} (hwf : WF3 s3) (hR : Repr tok ptok provOf L s3 s2)
    (hpl : PlacementOK pl) (hg : 0 < (g i).align ∧ MM02.Pow2 (g i).align)
    (h : MM03.AllocStep k pr ow ls s3 (.ok s3')) (hone : rootIdx ls = [i])
    (hprov : provOf (s3.P.length + i) = some pr)
    (hNL : NewLayout L s3'.P s3.P.length s2.next g [i]) :
    AllOk C ObR ObW s2 [.alloc (g i).space (pl s2 (g i)) (g i).size (g i).align (some (ptok pr))] ∧
      Repr tok ptok provOf L s3'
        (exec s2 [.alloc (g i).space (pl s2 (g i)) (g i).size (g i).align (some (ptok pr))]) := by
  cases h with
  | ok hst _ =>
    have e : allocOps pl g (some (ptok pr)) s2 [i] =
        [.alloc (g i).space (pl s2 (g i)) (g i).size (g i).align (some (ptok pr))] := rfl
    rw [← e, ← hone]
    refine ⟨allocOps_ok hpl _ _ hR.wf2 (by
        rw [hone]; intro j hj; rw [List.mem_singleton.1 hj]; exact hg),
      repr_extend (hd := .place ow) hR.toReprB hR.wf2 rfl hst.2.2.2.2.2.1
        (fun q hq hu => alloc_usable_back hwf hu hq) (fun _ _ hu => alloc_usable_old hu)
        (fun i hi => alloc_usable_new hst (i + 1) i (Nat.lt_succ_self i) hi) (fun _ => rfl)
        (fun l hl => ?_) (fun _ _ _ _ h => h) (fun _ h => by cases h)
        (fun j hj => by rw [hone, List.mem_singleton] at hj; subst hj; rw [hprov]; rfl)
        (by rw [hone]; exact hNL), exec_wf _ _ hR.wf2⟩
    simp only [allocEff] at hl
    split at hl
    · cases hl
    · rename_i hn
      refine ⟨by omega, ?_⟩
      split at hl
      · exact hst.2.2.2.2.1 l ‹_›
      · exact hl

/-- R6 for `alloc` of outcome `fail` (MM-03.3 §9.2, O14; K4: `alloc` `fail` ↦ no step): the state
is unchanged and stays in `Repr`. -/
theorem r6_alloc_fail {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {pr ow : Nat}
    {ls : List (Option Nat × Option Nat × Nat)} (hR : Repr tok ptok provOf L s3 s2)
    (h : MM03.AllocStep k pr ow ls s3 (.fail s3')) :
    AllOk C ObR ObW s2 [] ∧ Repr tok ptok provOf L s3' (exec s2 []) := by
  obtain ⟨rfl, -⟩ := alloc_fail_unchanged h; exact ⟨trivial, hR⟩

/-- L4: `FreeCompat p auth` instantiated by `Compatible auth (ptok (provOf p))`: `p` is a root
allocated from a provider `pr`, and `auth` is compatible with the token of `pr`. -/
def FreeCompatInst (C : Nat → Nat → Prop) (ptok : Nat → Nat) (provOf : Nat → Option Nat)
    (p auth : Nat) : Prop :=
  ∃ pr, provOf p = some pr ∧ C auth (ptok pr)

/-- `freeSound_derived` (L4, replaces the hypothesis `FreeSound` of pass 1): under `ReprB`, when
the contracts instantiate `FreeCompat` by `Compatible auth (ptok (provOf p))`, the obligation
`FreeSound` of `free p auth` holds for the root `p`. The content is the clause `provTokens` of
`Repr`: the MM-02 allocation of an allocated root keeps the token of its provider, a clause that
every step preserves (`r6_*`, `simulation`). -/
theorem freeSound_derived {k : K} {C : Nat → Nat → Prop} {tok ptok : Nat → Nat}
    {provOf : Nat → Option Nat} {L : Layout} {s3 : S3} {s2 : MM02.State} {p auth : Nat}
    (hR : ReprB tok ptok provOf L s3 s2) (hp : RootPlace s3.P p)
    (hfc : k.FreeCompat p auth → FreeCompatInst C ptok provOf p auth) :
    FreeSound k C L s3 s2 p auth := by
  intro _ hf l hl
  obtain ⟨pr, hpr, hc⟩ := hfc hf
  have := hR.provTokens p hp.1 hp
  rw [hpr] at this
  exact (this l hl).mono fun _ h => ⟨_, h, hc⟩

/-- R6 for `free` (MM-03.3 §9.2, O13; K4: `free` ↦ `DeallocStep` of the allocation of the root,
authority `auth`; L4: `FreeCompat` instantiated by `Compatible auth (ptok (provOf p))`; L5: one
`DeallocStep`, the storage owned by `p` keeps its allocation live): under `WF3`, the deallocation
has the outcome `ok` and the arrival states are in `Repr`. -/
theorem r6_free {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout} {s3 s3' : S3}
    {s2 : MM02.State} {p auth : Nat} (hwf : WF3 s3) (hR : Repr tok ptok provOf L s3 s2)
    (hfc : k.FreeCompat p auth → FreeCompatInst C ptok provOf p auth)
    (h : FreeStep k p auth s3 (.ok s3')) :
    AllOk C ObR ObW s2 (deallocOps [rootAlloc L s3.P p] auth) ∧
      Repr tok ptok provOf L s3' (exec s2 (deallocOps [rootAlloc L s3.P p] auth)) := by
  obtain ⟨⟨hdl, hfc', hu, hor, -⟩, rfl⟩ := Guarded.ok_iff.1 h
  have hpr : RootPlace s3.P p := by
    refine ⟨hu.lt, ?_⟩
    unfold OwnedRoot at hor; unfold parentOf
    cases hpl : s3.P[p]? with
    | none => rw [hpl] at hor; exact hor.elim
    | some pl => rw [hpl] at hor; exact hor.1
  have hfs := freeSound_derived (k := k) (C := C) hR.toReprB hpr hfc
  have hl0 := headD_mem_footprint hwf hpr.1
  have hnu : ¬ (freeEff s3 p).Usable p := fun h' => by
    have := h'.dead_false
    simp [freeEff, cleanup, freeS, partOf, hpr.1] at this
  have hne : ∀ r, (freeEff s3 p).Usable r → r ≠ p := fun r h' e => hnu (e ▸ h')
  have hUb : ∀ r, (freeEff s3 p).Usable r → s3.Usable r := fun r h' =>
    S3.Usable.mono (s := s3) (s' := freeEff s3 p) rfl (fun _ h => h) (fun q hq => by
      simp only [freeEff, cleanup, freeS, Bool.or_eq_false_iff] at hq; exact hq.1) h'
  have hdiff : ∀ r, RootPlace s3.P r → r ≠ p → ∀ l ∈ footprint s3.P r,
      (L l).alloc ∉ [rootAlloc L s3.P p] := fun r hr hrp l hl hm => by
    rw [List.mem_singleton] at hm
    exact hR.inj r hr.1 p hpr.1 hr hpr hrp l hl _ hl0 hm
  refine ⟨deallocOps_ok _ _ (List.pairwise_singleton _ _) fun i hi => ?_, ?_⟩
  · rw [List.mem_singleton.1 hi]
    exact (hR.live p hpr.1 hpr hu _ hl0).and (hfs hdl hfc' _ hl0)
  · refine ⟨?_, exec_wf _ _ hR.wf2⟩
    refine repr_deallocs hR.toReprB _ _ rfl (fun _ h => h) (fun r _ hrt hu' => ⟨hUb r hu',
      hdiff r hrt (hne r hu')⟩) (fun r _ hrt hf => ?_) (fun _ _ _ h => .inl h)
      (fun r _ hrt _ hf _ => ?_)
    · simp only [freeEff, cleanup, freeS, Bool.or_eq_true, decide_eq_true_eq] at hf
      rcases hf with hf | rfl
      · exact .inl hf
      · exact .inr fun l hl => List.mem_singleton.2 (rootAlloc_eq hwf hR.lwf hpr hl)
    · simp only [freeEff, cleanup, freeS, Bool.or_eq_false_iff, decide_eq_false_iff_not] at hf
      exact ⟨.inr hf.1, hdiff r hrt hf.2⟩

/-- R6 for `enterFrame` (MM-03.3 §9.2, O6; K4: `enterFrame` ↦ one `AllocStep` per root local):
under `WF3`, the allocations of the root locals, with the token of the new frame (K2), at the bases
chosen by the placement, have the outcome `ok`, and the arrival states are in `Repr`, for every
geometry of valid alignment and every layout of the new leaves (`NewLayout`); the new roots are not
allocated roots in the ghost `provOf` (L4). The theorem does not need L1: a local owned by a local
is covered too. -/
theorem r6_enter {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {ps : List Nat}
    {ls : List (Option Nat × Option Nat × Nat)} {pl : Placement} {g : Nat → Geom}
    (hwf : WF3 s3) (hR : Repr tok ptok provOf L s3 s2) (hpl : PlacementOK pl)
    (hg : ∀ i ∈ rootIdx ls, 0 < (g i).align ∧ MM02.Pow2 (g i).align)
    (h : EnterStep ps ls s3 (.ok s3'))
    (hprov : ∀ i ∈ rootIdx ls, provOf (s3.P.length + i) = none)
    (hNL : NewLayout L s3'.P s3.P.length s2.next g (rootIdx ls)) :
    AllOk C ObR ObW s2 (allocOps pl g (some (tok s3.nF)) s2 (rootIdx ls)) ∧
      Repr tok ptok provOf L s3' (exec s2 (allocOps pl g (some (tok s3.nF)) s2 (rootIdx ls))) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine ⟨allocOps_ok hpl _ _ hR.wf2 hg, ⟨repr_extend (hd := .frame s3.nF) hR.toReprB hR.wf2 rfl
    (enterPre_shapeOK hpre.1) (fun q hq hu => enter_usable_back hwf hu hq)
    (fun _ _ hu => enter_usable_old hu)
    (fun i hi => enter_usable_new hpre.1 (i + 1) i (Nat.lt_succ_self i) hi) (fun _ => rfl)
    (fun l hl => ?_) (fun q _ pl _ hg => ?_) (fun f e => by cases e; rfl)
    (fun i hi => by rw [hprov i hi]; trivial) hNL, exec_wf _ _ hR.wf2⟩⟩
  · simp only [enterEff] at hl
    split at hl
    · cases hl
    · exact ⟨by omega, hl⟩
  · cases ho : pl.owner with
    | place _ => rw [ho] at hg; exact hg
    | frame f => rw [ho] at hg; exact fun h => hg (List.mem_cons_of_mem _ h)

/-- K4 (`exitFrame`): the root places owned by the frame `f`, the roots of its automatic
allocations. -/
def frameRoots (s3 : S3) (f : Nat) : List Nat :=
  (List.range s3.P.length).filter fun r =>
    decide (RootPlace s3.P r) && decide (OptP (s3.P[r]?) (fun pl => pl.owner = .frame f) False)

theorem mem_frameRoots {s3 : S3} {f r : Nat} :
    r ∈ frameRoots s3 f ↔ RootPlace s3.P r ∧ OptP (s3.P[r]?) (fun pl => pl.owner = .frame f) False := by
  simp only [frameRoots, List.mem_filter, List.mem_range, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.1.1, h.1, h.2⟩⟩

/-- K4 (`exitFrame` ↦ one `DeallocStep` per automatic allocation of the frame, none for the owned
storage that dies with it): the deallocations of the allocations of the root places owned by the
current frame, with its token (K2). A local owned by another local is read as owned storage: no
deallocation (report, (c) 3 and (e) 1; witness `CaseOwnedLocal`). -/
def exitOps (L : Layout) (tok : Nat → Nat) (s3 : S3) : List Op2 :=
  deallocOps ((frameRoots s3 s3.top).map (rootAlloc L s3.P)) (tok s3.top)

/-- R6 for `exitFrame` (MM-03.3 §9.2, O7; K4): under `WF3`, `FrameOwnedLive` and the compatibility
of the frame tokens (K2), the deallocations of the automatic allocations of the exited frame have
the outcome `ok`, and the arrival states are in `Repr`: owned storage that dies with the frame
keeps its allocation live (leak). -/
theorem r6_exit {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} (hwf : WF3 s3)
    (hfo : FrameOwnedLive s3) (hR : Repr tok ptok provOf L s3 s2) (htc : TokCompat C tok)
    (h : ExitStep k s3 (.ok s3')) :
    AllOk C ObR ObW s2 (exitOps L tok s3) ∧
      Repr tok ptok provOf L s3' (exec s2 (exitOps L tok s3)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨f, F₀, hF⟩ : ∃ f F₀, s3.F = f :: F₀ := by
    unfold ExitPre at hpre; split at hpre
    · exact ⟨_, _, ‹_›⟩
    · exact hpre.elim
  have htop : s3.top = f := by simp [S3.top, hF]
  have hfF₀ : f ∉ F₀ := by have := hwf.nodup; rw [hF] at this; exact (List.nodup_cons.1 this).1
  have e := exitEff_eq hF
  have hhead : ∀ r ∈ frameRoots s3 f, (footprint s3.P r).headD r ∈ footprint s3.P r := fun r hr =>
    headD_mem_footprint hwf (mem_frameRoots.1 hr).1.1
  -- the allocations of two distinct roots differ
  have hinj : ∀ r r', RootPlace s3.P r → RootPlace s3.P r' → r ≠ r' → ∀ l ∈ footprint s3.P r,
      (L l).alloc ≠ rootAlloc L s3.P r' := fun r r' hr hr' hne l hl =>
    hR.inj r hr.1 r' hr'.1 hr hr' hne l hl _ (headD_mem_footprint hwf hr'.1)
  -- a root owned by the frame `f` is not another root
  have hnotin : ∀ r, RootPlace s3.P r → r ∉ frameRoots s3 f → ∀ l ∈ footprint s3.P r,
      (L l).alloc ∉ (frameRoots s3 f).map (rootAlloc L s3.P) := fun r hr hn l hl hm => by
    obtain ⟨r', hr', he⟩ := List.mem_map.1 hm
    exact hinj r r' hr (mem_frameRoots.1 hr').1 (fun e => hn (e ▸ hr')) l hl he.symm
  have howner : ∀ r, r ∈ frameRoots s3 f → ∃ pl, s3.P[r]? = some pl ∧ pl.owner = .frame f :=
    fun r hr => by
      have := (mem_frameRoots.1 hr).2
      unfold OptP at this; split at this
      · exact ⟨_, ‹_›, this⟩
      · exact this.elim
  unfold exitOps; rw [htop]
  refine ⟨deallocOps_ok _ _ ?_ fun i hi => ?_, ?_⟩
  · refine List.pairwise_map.2 (((pairwise_lt_range _).filter _).imp_of_mem
      fun ha hb hlt => ?_)
    exact hinj _ _ (mem_frameRoots.1 ha).1 (mem_frameRoots.1 hb).1 (Nat.ne_of_lt hlt) _ (hhead _ ha)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hi
    obtain ⟨pl, hpl, ho⟩ := howner r hr
    have hrt := (mem_frameRoots.1 hr).1
    have hu : s3.Usable r := .frame hpl (hfo r pl f hpl ho) ho (by rw [hF]; exact List.mem_cons_self ..)
    have ht := hR.tokens r hrt.1 hrt
    rw [hpl] at ht; simp only [OptP] at ht; rw [ho] at ht
    exact ((hR.live r hrt.1 hrt hu _ (hhead r hr)).and (ht _ (hhead r hr))).mono
      fun a ⟨h1, h2⟩ => ⟨h1, _, h2, htc f⟩
  · refine ⟨?_, exec_wf _ _ hR.wf2⟩
    refine repr_deallocs hR.toReprB _ _ (by rw [e]) (fun _ h => by rw [e] at h; exact h)
      (fun r _ hrt hu => ?_) (fun r _ _ hf => .inl (by rw [e] at hf; exact hf))
      (fun r _ hrt hg => ?_) (fun r _ hrt hu hf ho => ?_)
    · have hu' : ({ s3 with F := F₀ } : S3).Usable r :=
        (S3.Usable.congr (s := ({ s3 with F := F₀ } : S3)) (by rw [e]) (by rw [e]) (by rw [e])).1 hu
      refine ⟨S3.Usable.mono (s := s3) (s' := { s3 with F := F₀ }) rfl
        (fun g hg => by rw [hF]; exact List.mem_cons_of_mem _ hg) (fun _ h => h) hu',
        hnotin r hrt fun hm => ?_⟩
      obtain ⟨pl, hpl, ho⟩ := howner r hm
      cases hu' with
      | frame hpl' _ ho' hf' => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'; exact hfF₀ hf'
      | place hpl' _ ho' _ => rw [hpl] at hpl'; cases hpl'; rw [ho] at ho'; cases ho'
    · rw [e] at hg
      cases hpl : s3.P[r]? with
      | none => rw [hpl] at hg; exact hg.elim
      | some pl =>
        rw [hpl] at hg; simp only [OptP] at hg ⊢
        cases ho : pl.owner with
        | place _ => rw [ho] at hg; exact hg.elim
        | frame g =>
          rw [ho] at hg; simp only [FrameGone] at hg ⊢
          by_cases hgf : g = f
          · subst hgf
            refine .inr fun l hl => List.mem_map.2 ⟨r, mem_frameRoots.2 ⟨hrt, ?_⟩,
              (rootAlloc_eq hwf hR.lwf hrt hl).symm⟩
            rw [hpl]; exact ho
          · exact .inl fun hm => by rw [hF] at hm; exact (List.mem_cons.1 hm).elim hgf hg
    · refine ⟨.inr (by rw [e] at hf; exact hf), hnotin r hrt fun hm => ?_⟩
      obtain ⟨pl, hpl, ho'⟩ := howner r hm
      rw [hpl] at ho; simp only [OptP] at ho; rw [ho'] at ho; cases ho

/-- K4: the `ok` steps of MM-03 to which no MM-02 step corresponds: `derive`, `split`, `release`,
`depend`, `endUse`, `pin`, `unpin`, `newArena`, `reset`. -/
inductive NoStep (k : K) : S3 → S3 → Prop where
  | derive {s s' : S3} {src q : Nat} {m : Mode} : DeriveStep src q m s (.ok s') → NoStep k s s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      SplitStep k src rs s (.ok s') → NoStep k s s'
  | release {s s' : S3} {a : Nat} : ReleaseStep a s (.ok s') → NoStep k s s'
  | depend {s s' : S3} {q x : Nat} : DependStep q x s (.ok s') → NoStep k s s'
  | endUse {s s' : S3} {p : Nat} : EndUseStep k p s (.ok s') → NoStep k s s'
  | pin {s s' : S3} {p : Nat} : PinStep p s (.ok s') → NoStep k s s'
  | unpin {s s' : S3} {p : Nat} : UnpinStep k p s (.ok s') → NoStep k s s'
  | newArena {s s' : S3} {st i : Nat} : NewArenaStep st i s (.ok s') → NoStep k s s'
  | reset {s s' : S3} {i via : Nat} : ResetAtStep k i via s (.ok s') → NoStep k s s'

/-- R6 for the steps without MM-02 step (MM-03.3 §9.2; K4): the empty sequence, and the arrival
states are in `Repr`. -/
theorem r6_noStep {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State}
    (hR : Repr tok ptok provOf L s3 s2) (h : NoStep k s3 s3') :
    AllOk C ObR ObW s2 [] ∧ Repr tok ptok provOf L s3' (exec s2 []) := by
  refine ⟨trivial, ?_, hR.wf2⟩
  have same : ∀ {s' : S3}, s'.P = s3.P → s'.F = s3.F → s'.dead = s3.dead → s'.freed = s3.freed →
      s'.I = s3.I → ReprB tok ptok provOf L s' s2 := fun hP hF hd hfr hI =>
    hR.toReprB.shrink hP hF hfr (fun _ h => h.of_eqs hP hF hd) (fun _ h => by rw [← hI]; exact h)
  cases h with
  | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl rfl rfl
  | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl rfl rfl
  | release hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold releaseEff; split <;> exact same rfl rfl rfl rfl rfl
  | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl rfl rfl
  | endUse hs =>
    rename_i p
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    refine hR.toReprB.shrink rfl rfl rfl (fun q hq => S3.Usable.mono (s := s3) (s' := endUseEff s3 p) rfl
      (fun _ h => h) (fun q' hq' => ?_) hq)
      (fun l hl => ?_)
    · simp only [endUseEff, cleanup, endUseS, Bool.or_eq_false_iff] at hq'; exact hq'.1
    · simp only [endUseEff, cleanup, endUseS] at hl; split at hl
      · cases hl
      · exact hl
  | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl rfl rfl
  | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl rfl rfl
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl rfl rfl
  | reset hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold resetAtEff; split
    · exact same rfl rfl rfl rfl rfl
    · exact same rfl rfl rfl rfl rfl

/-- R6 for `exitFrame` on the reached states (MM-03.3 §9.2, §10), under `DDSound k`: `WF3` and
`FrameOwnedLive` hold there. -/
theorem r6_exit_reachable {k : K} {statics : Statics} {C : Nat → Nat → Prop}
    {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout}
    {s3 s3' : S3} {s2 : MM02.State} (hdd : DDSound k) (hr : Reachable k statics s3)
    (hR : Repr tok ptok provOf L s3 s2) (htc : TokCompat C tok) (h : ExitStep k s3 (.ok s3')) :
    AllOk C ObR ObW s2 (exitOps L tok s3) ∧
      Repr tok ptok provOf L s3' (exec s2 (exitOps L tok s3)) :=
  r6_exit (reachable_invariants hdd hr).1 (reachable_fpLeaves_frameOwnedLive hdd hr).2 hR htc h

/-! ## Copies and pointers (L6: `transfer`, `store`, `issue`) -/

/-- The bytes of the range of the leaf `l` in `s2`, if its allocation is registered. -/
def rangeBytes (s2 : MM02.State) (L : Layout) (l : Nat) : Option (List MM02.AByte) :=
  (s2.allocs (L l).alloc).map fun a => a.bytesAt (L l).off (L l).len

/-- L6: the bytes of the range of the leaf `l` in `s2` as the argument of a write, value and
provenance of each initialised byte ("avec les octets lus, provenance comprise"). -/
def bytesOf (s2 : MM02.State) (L : Layout) (l : Nat) : Nat → UInt8 × Option Nat := fun i =>
  match (s2.allocs (L l).alloc).map fun a => a.bytes ((L l).off + i) with
  | some (MM02.AByte.init v p) => (v, p)
  | _ => (0, none)

/-- L6: the pairs of corresponding leaves of `transfer src dst` (`corr`, the ordered isomorphism
of O4.2), in the order of the leaves of the source. -/
def transferPairs (P : List Place) (src dst : Nat) : List (Nat × Nat) :=
  (footprint P src).filterMap fun l => (corr P src dst l).map fun l' => (l, l')

/-- L6 (`transfer`): for each pair `(l, l')`, a read of the range of `l` (`ReadStep`), then a write
of the range of `l'` (`WriteStep`) with the bytes of the range of `l`. Held authorities and owned
storage give no step. -/
def copyOps (s2 : MM02.State) (L : Layout) : List (Nat × Nat) → List Op2
  | [] => []
  | (l, l') :: ps => .read (leafAcc s2 L .read l) :: .write (leafAcc s2 L .write l') (bytesOf s2 L l) ::
      copyOps s2 L ps

/-- L6 (`transfer src dst`): the copy of the corresponding leaves. -/
def transferOps (s2 : MM02.State) (L : Layout) (P : List Place) (src dst : Nat) : List Op2 :=
  copyOps s2 L (transferPairs P src dst)

/-- L6, hypothesis `SameSizeAlong` (types, spec 4): two corresponding leaves have the same size. -/
def SameSizeAlong (L : Layout) (P : List Place) (src dst : Nat) : Prop :=
  ∀ l l', (l, l') ∈ transferPairs P src dst → (L l).len = (L l').len

theorem mem_transferPairs {P : List Place} {src dst l l' : Nat} :
    (l, l') ∈ transferPairs P src dst ↔ l ∈ footprint P src ∧ corr P src dst l = some l' := by
  simp only [transferPairs, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, e⟩
    cases hc : corr P src dst x with
    | none => rw [hc] at e; cases e
    | some y => rw [hc] at e; cases e; exact ⟨hx, hc⟩
  · rintro ⟨h, e⟩; exact ⟨l, h, by rw [e]; rfl⟩

/-- L6: after the write of the range of a leaf in a state that keeps the allocations of `s2`, the
range holds the bytes written, all initialised. -/
theorem rangeBytes_write {s2 t : MM02.State} (hd : Dom s2 t) {L : Layout} {l : Nat}
    {w : Nat → UInt8 × Option Nat} (h : AllocP s2 (L l).alloc fun _ => True) :
    rangeBytes (t.write (leafAcc s2 L .write l) w) L l =
      some ((List.range (L l).len).map fun i => .init (w i).1 (w i).2) := by
  obtain ⟨a, ha, -⟩ := h
  obtain ⟨b, hb, -, e, -⟩ := hd _ a ha
  have hacc : leafAcc s2 L .write l = leafAcc t L .write l := by rw [leafAcc_of ha, leafAcc_of hb, e]
  rw [hacc, rangeBytes, write_allocs, leafAcc_of hb]
  simp only [↓reduceIte, hb, Option.map_some, Nat.add_sub_cancel_left, Option.some.injEq,
    MM02.Alloc.bytesAt, MM02.Alloc.write, List.map_inj_left, List.mem_range]
  intro i hi
  have hr : (L l).off ≤ (L l).off + i ∧ (L l).off + i < (L l).off + (L l).len :=
    ⟨Nat.le_add_right _ _, by omega⟩
  simp only [hr, and_self, ↓reduceIte]

/-- L6: the run of the copies of a transfer, from a state `t` that keeps the allocations of the
state `s2` where the sequence was computed: every read and write has the outcome `ok` when the
source ranges are live and initialised and the destination ranges live, under `dec` along the run
and `stat` (K5); the run keeps the allocations; every destination range ends initialised. -/
theorem copyOps_run {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {s2 : MM02.State} {L : Layout} (hstatR : ∀ s ac, ObR.stat s ac)
    (hstatW : ∀ s ac w, ObW.stat s ac w) :
    ∀ (ps : List (Nat × Nat)) (t : MM02.State), Dom s2 t →
      (∀ l l', (l, l') ∈ ps →
        (AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size ∧
          a.InitRange (L l).off (L l).len) ∧
        AllocP s2 (L l').alloc fun a => a.live = true ∧ (L l').off + (L l').len ≤ a.size) →
      DecAlong ObR ObW t (copyOps s2 L ps) →
      AllOk C ObR ObW t (copyOps s2 L ps) ∧ Dom t (exec t (copyOps s2 L ps)) ∧
        ∀ l l', (l, l') ∈ ps →
          AllocP (exec t (copyOps s2 L ps)) (L l').alloc fun a => a.InitRange (L l').off (L l').len
  | [], t, _, _, _ => ⟨trivial, Dom.refl _, fun _ _ h => by cases h⟩
  | (l, l') :: ps, t, hd, hps, hdec => by
    obtain ⟨hsrc, hdst⟩ := hps l l' (List.mem_cons_self ..)
    -- the source and destination in `t`
    have hsrc' : AllocP t (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size ∧
        a.InitRange (L l).off (L l).len :=
      hsrc.of_dom hd fun a a' _ e2 e3 _ hb ⟨h1, h2, h3⟩ =>
        ⟨e3 ▸ h1, e2 ▸ h2, fun i hi => hb _ (h3 i hi)⟩
    have hdst' : AllocP t (L l').alloc fun a => a.live = true ∧ (L l').off + (L l').len ≤ a.size :=
      hdst.of_dom hd fun a a' _ e2 e3 _ _ ⟨h1, h2⟩ => ⟨e3 ▸ h1, e2 ▸ h2⟩
    have eR : leafAcc s2 L .read l = leafAcc t L .read l :=
      (leafAcc_dom hd (hsrc.mono fun _ _ => trivial)).symm
    have eW : leafAcc s2 L .write l' = leafAcc t L .write l' :=
      (leafAcc_dom hd (hdst.mono fun _ _ => trivial)).symm
    obtain ⟨hdecR, hdecW, hdec⟩ := hdec
    -- the read
    obtain ⟨a, ha, hla, hsz, hin⟩ := hsrc'
    have hread : MM02.Read t (leafAcc s2 L .read l) := by
      rw [eR, leafAcc_of ha]
      have e : a.base + (L l).off - a.base = (L l).off := Nat.add_sub_cancel_left _ _
      exact ⟨a, ha, hla, ⟨Nat.le_add_right _ _, by simp only; omega⟩, by simp only [e]; exact hin,
        .inl rfl⟩
    have hok := MM02.ReadStep.ok (ObR := ObR) (by rw [eR, leafAcc_of ha]; exact ha)
      ⟨hread, hdecR, hstatR _ _⟩
    -- the write
    have hw := write_leaf_ok (ObW := ObW) (w := bytesOf s2 L l) hstatW hdst' (by rw [← eW]; exact hdecW)
    rw [← eW] at hw
    have hd₁ : Dom t (t.write (leafAcc s2 L .write l') (bytesOf s2 L l)) := Dom.write _ _ _
    have ih := copyOps_run (C := C) hstatR hstatW ps _ (hd.trans hd₁)
      (fun m m' hm => hps m m' (List.mem_cons_of_mem _ hm)) hdec
    refine ⟨⟨⟨_, hok⟩, hw, ih.1⟩, hd₁.trans ih.2.1, fun m m' hm => ?_⟩
    rcases List.mem_cons.1 hm with e | hm
    · cases e
      have := rangeBytes_write (w := bytesOf s2 L l) (hd.trans (Dom.refl _))
        (L := L) (l := l') (hdst.mono fun _ _ => trivial)
      obtain ⟨b, hb, -⟩ := hdst'
      have hinit : AllocP (t.write (leafAcc s2 L .write l') (bytesOf s2 L l)) (L l').alloc
          fun a => a.InitRange (L l').off (L l').len := by
        rw [eW]; exact write_leaf_init ⟨b, hb, trivial⟩
      exact hinit.of_dom ih.2.1 fun _ _ _ _ _ _ hb h i hi => hb _ (h i hi)
    · exact ih.2.2 m m' hm

/-- A leaf of a usable place has its allocation live and its range within it (K1 (c), K3). -/
theorem live_of_usable_part {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout}
    {s3 : S3} {s2 : MM02.State} (hwf : WF3 s3) (hR : ReprB tok ptok provOf L s3 s2) {q l : Nat}
    (hu : s3.Usable q) (hl : l ∈ footprint s3.P q) :
    AllocP s2 (L l).alloc fun a => a.live = true ∧ (L l).off + (L l).len ≤ a.size := by
  obtain ⟨hlP, hlf, hlq⟩ := mem_footprint.1 hl
  have hul : s3.Usable l := usable_of_partOf hwf (l + 1) l q (Nat.lt_succ_self l) hlq hu
  obtain ⟨r, hr, hlr⟩ := exists_rootPlace hwf (l + 1) l (Nat.lt_succ_self l) hlP
  exact (hR.live r hr.1 hr (usable_of_part hwf hlr hul) l (mem_footprint.2 ⟨hlP, hlf, hlr⟩)).and
    (hR.lwf.within l hlP hlf)

/-- `ReprB` carries over when the places keep their parents and only change owners between places,
the MM-02 state keeps its allocations, usability, stack and `freed` marks are unchanged, and every
leaf that becomes `Init` has its range initialised (L6: `transfer` moves the owners of the owned
storage, A5). -/
theorem ReprB.transport {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout}
    {s3 s3' : S3} {s2 s2' : MM02.State} (hR : ReprB tok ptok provOf L s3 s2) (hd : Dom s2 s2')
    (hlen : s3'.P.length = s3.P.length) (hpar : parentOf s3'.P = parentOf s3.P)
    (hown : ∀ (q : Nat) (pl' : Place), s3'.P[q]? = some pl' → ∃ pl : Place, s3.P[q]? = some pl ∧
      (pl'.owner = pl.owner ∨ (pl'.owner.isPlace = true ∧ pl.owner.isPlace = true)))
    (hF : s3'.F = s3.F) (hfr : s3'.freed = s3.freed) (hU : ∀ q, s3'.Usable q ↔ s3.Usable q)
    (hI : ∀ l < s3.P.length, isLeaf s3.P l → s3'.I l = .init →
      s3.I l = .init ∨ AllocP s2' (L l).alloc fun a => a.InitRange (L l).off (L l).len) :
    ReprB tok ptok provOf L s3' s2' := by
  have hfp : ∀ q, footprint s3'.P q = footprint s3.P q := footprint_congr hlen hpar
  have hleaf : ∀ l, isLeaf s3'.P l ↔ isLeaf s3.P l := fun l => by simp only [isLeaf, hlen, hpar]
  have hroot : ∀ r, RootPlace s3'.P r ↔ RootPlace s3.P r := fun r => by
    simp only [RootPlace, hlen, hpar]
  -- the owner of a root, read in `s3'`
  have hfr' : ∀ r (pl' : Place), s3'.P[r]? = some pl' → ∃ pl : Place, s3.P[r]? = some pl ∧
      (∀ f, pl'.owner = .frame f → pl.owner = .frame f) ∧
      (pl'.owner.isPlace = true → pl.owner.isPlace = true) := fun r pl' h => by
    obtain ⟨pl, hpl, e⟩ := hown r pl' h
    refine ⟨pl, hpl, fun f hf => ?_, fun hp => ?_⟩
    · rcases e with e | ⟨h1, -⟩
      · rw [← e, hf]
      · rw [hf] at h1; cases h1
    · rcases e with e | ⟨-, h2⟩
      · rw [← e]; exact hp
      · exact h2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [hlen, hfp, hleaf, hroot, hF, hfr, hU]
  · exact hR.lwf.sameAlloc
  · exact hR.lwf.disjoint
  · exact fun l hl hlf => (hR.lwf.within l hl hlf).of_dom hd fun a a' _ e _ _ _ h => e ▸ h
  · exact hR.inj
  · intro r hr hrt
    cases hpl' : s3'.P[r]? with
    | none => trivial
    | some pl' =>
      obtain ⟨pl, hpl, hfrm, -⟩ := hfr' r pl' hpl'
      have := hR.tokens r hr hrt
      rw [hpl] at this
      show OptP (tokOf tok pl'.owner) _ True
      cases ho' : pl'.owner with
      | place _ => trivial
      | frame f =>
        have e := hfrm f ho'
        simp only [OptP, e, tokOf] at this
        exact fun l hl => (this l hl).of_dom hd fun _ _ _ _ _ e _ h => e ▸ h
  · exact fun r hr hrt => OptP.imp (hR.provTokens r hr hrt) (fun _ h l hl =>
      (h l hl).of_dom hd fun _ _ _ _ _ e _ h => e ▸ h) id
  · exact fun r hr hrt hu l hl => (hR.live r hr hrt hu l hl).of_dom hd fun a a' _ _ e _ _ h => e ▸ h
  · intro l hl hlf hi
    rcases hI l hl hlf hi with h | h
    · exact (hR.init l hl hlf h).of_dom hd fun a a' _ _ _ _ hb h i hi => hb _ (h i hi)
    · exact h
  · exact fun r hr hrt hf l hl => (hR.freed r hr hrt hf l hl).of_dom hd fun a a' _ _ e _ _ h => e ▸ h
  · intro r hr hrt hg l hl
    have hg' : OptP (s3.P[r]?) (fun pl => FrameGone s3.F pl.owner) False := by
      cases hpl' : s3'.P[r]? with
      | none => rw [hpl'] at hg; exact hg.elim
      | some pl' =>
        rw [hpl'] at hg
        obtain ⟨pl, hpl, hfrm, -⟩ := hfr' r pl' hpl'
        rw [hpl]
        show FrameGone s3.F pl.owner
        have hg2 : FrameGone s3.F pl'.owner := hg
        cases ho' : pl'.owner with
        | place _ => rw [ho'] at hg2; exact hg2.elim
        | frame f => rw [ho'] at hg2; rw [hfrm f ho']; exact hg2
    exact (hR.exited r hr hrt hg' l hl).of_dom hd fun a a' _ _ e _ _ h => e ▸ h
  · intro r hr hrt hu hf ho l hl
    have ho' : OptP (s3.P[r]?) (fun pl => pl.owner.isPlace = true) False := by
      cases hpl' : s3'.P[r]? with
      | none => rw [hpl'] at ho; exact ho.elim
      | some pl' =>
        rw [hpl'] at ho
        obtain ⟨pl, hpl, -, hplc⟩ := hfr' r pl' hpl'
        rw [hpl]; exact hplc ho
    exact (hR.leaked r hr hrt hu hf ho' l hl).of_dom hd fun a a' _ _ e _ _ h => e ▸ h

/-- R6 for `transfer` (MM-03.3 §9.2, O4; L6: for each pair of corresponding leaves, a `ReadStep` of
the source range then a `WriteStep` of the destination range with the bytes of the source range
(`bytesOf`), provenance included; held authorities and owned storage give no step): under `WF3`,
`dec` along the run and `stat` (K5), every read and write has the outcome `ok` and the arrival
states are in `Repr`. The theorem does not take `SameSizeAlong` (L6, spec 4): without it, the
write is not the copy of the bytes read (it reads past the source range, or copies a part of it);
`transfer_copies`, which takes it, states the copy. The source ranges stay initialised in MM-02;
MM-03 makes them unreadable (`Moved`). -/
theorem r6_transfer {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout} {s3 s3' : S3}
    {s2 : MM02.State} {src dst : Nat} (hwf : WF3 s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : TransferStep k src dst s3 (.ok s3')) (hstatR : ∀ s ac, ObR.stat s ac)
    (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hdec : DecAlong ObR ObW s2 (transferOps s2 L s3.P src dst)) :
    AllOk C ObR ObW s2 (transferOps s2 L s3.P src dst) ∧
      Repr tok ptok provOf L s3' (exec s2 (transferOps s2 L s3.P src dst)) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  have hsu := hpre.1
  have hinit := hpre.2.1
  have hdu := hpre.2.2.1
  have hdu' := hpre.2.2.2.2.2.2.2.1
  have hsh := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hdl : dst < s3.P.length := hdu.lt
  have hrun := copyOps_run (C := C) (L := L) (s2 := s2) hstatR hstatW (transferPairs s3.P src dst)
    s2 (Dom.refl _) (fun l l' hm => by
      obtain ⟨hl, hc⟩ := mem_transferPairs.1 hm
      obtain ⟨l'', hc', hl''⟩ := corr_leaf_fwd hwf hdl hsh hl
      rw [hc] at hc'; cases hc'
      obtain ⟨hlP, hlf, -⟩ := mem_footprint.1 hl
      exact ⟨(live_of_usable_part hwf hR.toReprB hsu hl).and (hR.init l hlP hlf (hinit l hl)) |>.mono
        fun _ ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩, live_of_usable_part hwf hR.toReprB hdu hl''⟩) hdec
  refine ⟨hrun.1, ReprB.transport hR.toReprB hrun.2.1 (by simp [transferEff]) ?_ ?_ rfl rfl
    (fun q => ⟨transfer_usable_back hwf hsu, transfer_usable_fwd hwf hdu'⟩) ?_,
    exec_wf _ _ hR.wf2⟩
  · funext i; simp only [parentOf, transferEff, List.getElem?_map]
    cases s3.P[i]? with
    | none => rfl
    | some pl => simp only [Option.map_some, Option.bind_some]; split <;> rfl
  · intro q pl' hq
    simp only [transferEff, List.getElem?_map] at hq
    cases hp : s3.P[q]? with
    | none => rw [hp] at hq; cases hq
    | some pl =>
      rw [hp] at hq; simp only [Option.map_some, Option.some.injEq] at hq
      refine ⟨pl, rfl, ?_⟩
      split at hq
      · rename_i hh
        subst hq
        right
        cases ho : pl.owner with
        | frame _ => rw [ho] at hh; exact hh.elim
        | place r => exact ⟨by simp only [mvTo]; rfl, rfl⟩
      · subst hq; exact .inl rfl
  · intro l _ _ hi
    simp only [transferEff] at hi
    split at hi
    · rename_i hld
      obtain ⟨m, hm, hc⟩ := corr_leaf_back hsh hld
      exact .inr (hrun.2.2 m l (mem_transferPairs.2 ⟨hm, hc⟩))
    · split at hi
      · cases hi
      · exact .inl hi

/-- A write of the range of the leaf `l'` leaves the range of a leaf `x` in another allocation, or
disjoint from it, unchanged (MM-02.C, non-interference). -/
theorem rangeBytes_write_other {s2 t : MM02.State} (hd : Dom s2 t) {L : Layout} {l' x : Nat}
    {w : Nat → UInt8 × Option Nat} (h : AllocP s2 (L l').alloc fun _ => True)
    (hne : (L x).alloc ≠ (L l').alloc ∨
      MM02.RangeDisjoint (L x).off (L x).len (L l').off (L l').len) :
    rangeBytes (t.write (leafAcc s2 L .write l') w) L x = rangeBytes t L x := by
  obtain ⟨a, ha, -⟩ := h
  obtain ⟨b, hb, -, e, -⟩ := hd _ a ha
  have hacc : leafAcc s2 L .write l' = leafAcc t L .write l' := by
    rw [leafAcc_of ha, leafAcc_of hb, e]
  rw [hacc, rangeBytes, rangeBytes, write_allocs, leafAcc_of hb]
  by_cases hx : (L x).alloc = (L l').alloc
  · simp only [hx, ↓reduceIte, hb, Option.map_some, Nat.add_sub_cancel_left, Option.some.injEq,
      MM02.Alloc.bytesAt, MM02.Alloc.write, List.map_inj_left, List.mem_range]
    intro i hi
    have hd' := hne.resolve_left (by rw [hx]; exact fun h => h rfl)
    have : ¬ ((L l').off ≤ (L x).off + i ∧ (L x).off + i < (L l').off + (L l').len) :=
      fun ⟨h1, h2⟩ => hd' _ (Nat.le_add_right _ _) (by omega) h1 h2
    simp only [this, ↓reduceIte]
  · simp only [hx, ↓reduceIte]

/-- L6: writing the range of `l'` with the bytes of the range of an initialised leaf `l` of the same
size copies them, value and provenance. -/
theorem rangeBytes_copy {s2 t : MM02.State} (hd : Dom s2 t) {L : Layout} {l l' : Nat}
    (hsrc : AllocP s2 (L l).alloc fun a => a.InitRange (L l).off (L l).len)
    (hdst : AllocP s2 (L l').alloc fun _ => True) (hsz : (L l).len = (L l').len) :
    rangeBytes (t.write (leafAcc s2 L .write l') (bytesOf s2 L l)) L l' = rangeBytes s2 L l := by
  rw [rangeBytes_write hd hdst]
  obtain ⟨a, ha, hin⟩ := hsrc
  simp only [rangeBytes, ha, Option.map_some, Option.some.injEq, MM02.Alloc.bytesAt, ← hsz,
    List.map_inj_left, List.mem_range]
  intro i hi
  have hb := hin i hi
  simp only [bytesOf, ha, Option.map_some]
  revert hb
  cases a.bytes ((L l).off + i) with
  | uninit => exact fun h => absurd rfl h
  | init v p => exact fun _ => rfl

/-- L6: the run of the copies of a transfer copies each source range into its destination range,
provenance included, when the sources are initialised, the sizes are equal, the destinations are
distinct, and the ranges of the destinations are disjoint from those of the sources and of each
other; a range disjoint from every destination range is unchanged. -/
theorem copyOps_bytes {s2 : MM02.State} {L : Layout} :
    ∀ (ps : List (Nat × Nat)) (t : MM02.State), Dom s2 t →
      (∀ l l', (l, l') ∈ ps → (AllocP s2 (L l).alloc fun a => a.InitRange (L l).off (L l).len) ∧
        (AllocP s2 (L l').alloc fun _ => True) ∧ (L l).len = (L l').len ∧
        rangeBytes t L l = rangeBytes s2 L l) →
      (∀ l l' m m', (l, l') ∈ ps → (m, m') ∈ ps → (L l).alloc ≠ (L m').alloc ∨
        MM02.RangeDisjoint (L l).off (L l).len (L m').off (L m').len) →
      (∀ l l' m m', (l, l') ∈ ps → (m, m') ∈ ps → l' ≠ m' → (L l').alloc ≠ (L m').alloc ∨
        MM02.RangeDisjoint (L l').off (L l').len (L m').off (L m').len) →
      ps.Pairwise (fun p q => p.2 ≠ q.2) →
      (∀ x, (∀ m m', (m, m') ∈ ps → (L x).alloc ≠ (L m').alloc ∨
          MM02.RangeDisjoint (L x).off (L x).len (L m').off (L m').len) →
        rangeBytes (exec t (copyOps s2 L ps)) L x = rangeBytes t L x) ∧
      ∀ l l', (l, l') ∈ ps → rangeBytes (exec t (copyOps s2 L ps)) L l' = rangeBytes s2 L l
  | [], _, _, _, _, _, _ => ⟨fun _ _ => rfl, fun _ _ h => by cases h⟩
  | (l₀, l₀') :: ps, t, hd, hps, hsd, hdd, hnd => by
    obtain ⟨hsrc, hdst, hsz, -⟩ := hps l₀ l₀' (List.mem_cons_self ..)
    obtain ⟨hnd₀, hnd⟩ := List.pairwise_cons.1 hnd
    have hd₁ : Dom s2 (t.write (leafAcc s2 L .write l₀') (bytesOf s2 L l₀)) :=
      hd.trans (Dom.write _ _ _)
    have ih := copyOps_bytes ps (t.write (leafAcc s2 L .write l₀') (bytesOf s2 L l₀)) hd₁
      (fun l l' hm => by
        obtain ⟨h1, h2, h3, h4⟩ := hps l l' (List.mem_cons_of_mem _ hm)
        refine ⟨h1, h2, h3, ?_⟩
        rw [rangeBytes_write_other hd hdst (hsd l l' l₀ l₀' (List.mem_cons_of_mem _ hm)
          (List.mem_cons_self ..)), h4])
      (fun l l' m m' hm hm' => hsd l l' m m' (List.mem_cons_of_mem _ hm)
        (List.mem_cons_of_mem _ hm'))
      (fun l l' m m' hm hm' => hdd l l' m m' (List.mem_cons_of_mem _ hm)
        (List.mem_cons_of_mem _ hm')) hnd
    refine ⟨fun x hx => ?_, fun l l' hm => ?_⟩
    · show rangeBytes (exec (t.write (leafAcc s2 L .write l₀') (bytesOf s2 L l₀))
        (copyOps s2 L ps)) L x = _
      rw [ih.1 x fun m m' hm => hx m m' (List.mem_cons_of_mem _ hm)]
      exact rangeBytes_write_other hd hdst (hx l₀ l₀' (List.mem_cons_self ..))
    · show rangeBytes (exec (t.write (leafAcc s2 L .write l₀') (bytesOf s2 L l₀))
        (copyOps s2 L ps)) L l' = _
      rcases List.mem_cons.1 hm with e | hm
      · cases e
        rw [ih.1 l₀' fun m m' hm => hdd l₀ l₀' m m' (List.mem_cons_self ..)
          (List.mem_cons_of_mem _ hm) (hnd₀ (m, m') hm)]
        exact rangeBytes_copy hd hsrc hdst hsz
      · exact ih.2 l l' hm

/-- L6, `transfer_copies`: after the run of a transfer, under `WF3` and `SameSizeAlong` (spec 4),
the range of each destination leaf holds exactly the bytes of the range of the corresponding
source leaf, value and provenance, and the source ranges are unchanged: the copy loses and
fabricates no provenance and no address. -/
theorem transfer_copies {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout}
    {s3 s3' : S3} {s2 : MM02.State} {src dst : Nat} (hwf : WF3 s3)
    (hR : Repr tok ptok provOf L s3 s2) (h : TransferStep k src dst s3 (.ok s3'))
    (hsize : SameSizeAlong L s3.P src dst) :
    ∀ l l', (l, l') ∈ transferPairs s3.P src dst →
      rangeBytes (exec s2 (transferOps s2 L s3.P src dst)) L l' = rangeBytes s2 L l ∧
      rangeBytes (exec s2 (transferOps s2 L s3.P src dst)) L l = rangeBytes s2 L l := by
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  have hinit := hpre.2.1
  have hdu := hpre.2.2.1
  have hno := hpre.2.2.2.2.1
  have hsh := hpre.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hdl : dst < s3.P.length := hdu.lt
  -- the pairs: a source leaf and its destination leaf
  have hpair : ∀ l l', (l, l') ∈ transferPairs s3.P src dst →
      l ∈ footprint s3.P src ∧ l' ∈ footprint s3.P dst := fun l l' hm => by
    obtain ⟨hl, hc⟩ := mem_transferPairs.1 hm
    obtain ⟨l'', hc', hl''⟩ := corr_leaf_fwd hwf hdl hsh hl
    rw [hc] at hc'; cases hc'; exact ⟨hl, hl''⟩
  -- two distinct leaves have disjoint ranges or distinct allocations
  have hlw : ∀ x y, x ∈ footprint s3.P src ∨ x ∈ footprint s3.P dst →
      y ∈ footprint s3.P src ∨ y ∈ footprint s3.P dst → x ≠ y →
      (L x).alloc ≠ (L y).alloc ∨ MM02.RangeDisjoint (L x).off (L x).len (L y).off (L y).len :=
    fun x y hx hy hne => by
      have hx' : x < s3.P.length ∧ isLeaf s3.P x := by
        rcases hx with hx | hx <;> exact ⟨(mem_footprint.1 hx).1, (mem_footprint.1 hx).2.1⟩
      have hy' : y < s3.P.length ∧ isLeaf s3.P y := by
        rcases hy with hy | hy <;> exact ⟨(mem_footprint.1 hy).1, (mem_footprint.1 hy).2.1⟩
      by_cases e : (L x).alloc = (L y).alloc
      · exact .inr (hR.lwf.disjoint x hx'.1 y hy'.1 hx'.2 hy'.2 hne e)
      · exact .inl e
  have hsrcdst : ∀ l m', l ∈ footprint s3.P src → m' ∈ footprint s3.P dst → l ≠ m' :=
    fun l m' hl hm' e => hno ⟨l, hl, e ▸ hm'⟩
  have hnd : (transferPairs s3.P src dst).Pairwise (fun p q => p.2 ≠ q.2) := by
    unfold transferPairs
    refine List.Pairwise.filterMap
      (R := fun a b => a < b ∧ partOf s3.P a src ∧ partOf s3.P b src) _ ?_ ?_
    · intro a b ⟨hab, ha, hb⟩ x hx y hy e
      simp only [Option.map_eq_some_iff] at hx hy
      obtain ⟨a', ha', rfl⟩ := hx
      obtain ⟨b', hb', rfl⟩ := hy
      simp only at e; subst e
      exact absurd (corr_inj hwf hdl ha hb ha' hb') (Nat.ne_of_lt hab)
    · exact ((pairwise_lt_range _).filter _).imp_of_mem fun ha hb hab =>
        ⟨hab, (mem_footprint.1 ha).2.2, (mem_footprint.1 hb).2.2⟩
  have := copyOps_bytes (s2 := s2) (L := L) (transferPairs s3.P src dst) s2 (Dom.refl _)
    (fun l l' hm => by
      obtain ⟨hl, hl'⟩ := hpair l l' hm
      obtain ⟨hlP, hlf, -⟩ := mem_footprint.1 hl
      obtain ⟨hl'P, hl'f, -⟩ := mem_footprint.1 hl'
      exact ⟨hR.init l hlP hlf (hinit l hl), (hR.lwf.within l' hl'P hl'f).mono fun _ _ => trivial,
        hsize l l' hm, rfl⟩)
    (fun l l' m m' hm hm' => hlw l m' (.inl (hpair l l' hm).1) (.inr (hpair m m' hm').2)
      (hsrcdst l m' (hpair l l' hm).1 (hpair m m' hm').2))
    (fun l l' m m' hm hm' hne => hlw l' m' (.inr (hpair l l' hm).2) (.inr (hpair m m' hm').2) hne)
    hnd
  exact fun l l' hm => ⟨this.2 l l' hm, this.1 l fun m m' hm' =>
    hlw l m' (.inl (hpair l l' hm).1) (.inr (hpair m m' hm').2)
      (hsrcdst l m' (hpair l l' hm).1 (hpair m m' hm').2)⟩

/-- L6: parametric encoding of pointers into bytes (spec 11): `enc addr prov i` is the `i`-th byte
of a pointer to the address `addr` with provenance `prov`; `decode` reads an address back. -/
structure PtrEnc where
  enc : Nat → Option Nat → Nat → UInt8 × Option Nat
  decode : (Nat → UInt8 × Option Nat) → Nat

/-- L6, obligation of the encoding for a pointer to the address `addr` with provenance `prov`:
`decode (enc addr prov)` is `addr`, and every byte carries the provenance `prov`. Stated per
pointer: a `decode` that reads finitely many bytes cannot invert every natural address (finite
addresses, spec 11). -/
def PtrEncAt (pe : PtrEnc) (addr : Nat) (prov : Option Nat) : Prop :=
  pe.decode (pe.enc addr prov) = addr ∧ ∀ i, (pe.enc addr prov i).2 = prov

/-- L6 ("base + off of first leaf"): address of the pointer to the region `rg`: base of the
allocation of the first leaf of the list plus the offset of that leaf. It is the first byte of the
region when that leaf has the lowest offset; K1 fixes no order of fields (pass-2 report,
(e) 3). -/
def regionAddr (s2 : MM02.State) (L : Layout) (rg : List Nat) : Nat :=
  match rg.head? with
  | some l => (((s2.allocs (L l).alloc).map (·.base)).getD 0) + (L l).off
  | none => 0

/-- L6: provenance of the region `rg`: the allocation of its first leaf (none for an empty
region). -/
def regionProv (L : Layout) (rg : List Nat) : Option Nat := rg.head?.map fun l => (L l).alloc

/-- L6, `ptrBytes`: the bytes of a pointer to the region `rg`. -/
def ptrBytes (pe : PtrEnc) (s2 : MM02.State) (L : Layout) (rg : List Nat) :
    Nat → UInt8 × Option Nat :=
  pe.enc (regionAddr s2 L rg) (regionProv L rg)

/-- L6 (`store a p`): one write of the range of the leaf `p` with the bytes of a pointer to the
region covered by `a`. -/
def storeOps (pe : PtrEnc) (s2 : MM02.State) (L : Layout) (s3 : S3) (a p : Nat) : List Op2 :=
  [.write (leafAcc s2 L .write p) (ptrBytes pe s2 L (s3.afp a))]

/-- L6 (`issue`, "prov: allocation of arena storage"): the provenance of a block of the arena entry
`i` of `s3`: the allocation of the storage of the arena, read on its first leaf (as `rootAlloc`
reads a root); none for a missing entry. -/
def arenaProv (L : Layout) (s3 : S3) (i : Nat) : Option Nat :=
  (s3.arenas[i]?).map fun ar => (L ((footprint s3.P ar.storage).headD ar.storage)).alloc

/-- L6, the bytes of the pointer to the block `region` of the arena entry `i`: the address of the
region (`regionAddr`) and the provenance of the storage of the arena (`arenaProv`). -/
def issueBytes (pe : PtrEnc) (s2 : MM02.State) (L : Layout) (s3 : S3) (i : Nat)
    (region : List Nat) : Nat → UInt8 × Option Nat :=
  pe.enc (regionAddr s2 L region) (arenaProv L s3 i)

/-- L6 (`issue` on the arena entry `i`): one write of the range of the destination with the bytes of
the pointer to the block; `available` and `issued` are abstract state of the arena entry (library
obligation). -/
def issueOps (pe : PtrEnc) (s2 : MM02.State) (L : Layout) (s3 : S3) (i : Nat) (region : List Nat)
    (dst : Nat) : List Op2 :=
  [.write (leafAcc s2 L .write dst) (issueBytes pe s2 L s3 i region)]

/-- L6: the pointer to a region whose first leaf `l` is covered by an active authority is neither
lost nor fabricated: its provenance is the allocation of `l`, which is live, and its address is
the address of `l`, within that allocation. -/
theorem ptr_target {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout} {s3 : S3}
    {s2 : MM02.State} (hwf : WF3 s3) (hnd : NoDangling s3) (hfl : FpLeaves s3)
    (hR : ReprB tok ptok provOf L s3 s2) {a : Nat} {y : Authority} (hy : s3.A[a]? = some y)
    (ya : y.active = true) {rg : List Nat} (hrg : ∀ l ∈ rg, l ∈ y.footprint) {l : Nat}
    (hl : rg.head? = some l) :
    regionProv L rg = some (L l).alloc ∧ ∃ al, s2.allocs (L l).alloc = some al ∧ al.live = true ∧
      regionAddr s2 L rg = al.base + (L l).off ∧ (L l).off + (L l).len ≤ al.size := by
  have hlr : l ∈ rg := List.mem_of_getElem? (by rw [List.head?_eq_getElem?] at hl; exact hl)
  obtain ⟨hlP, hlf, hlive⟩ := covered_live hwf hnd hfl hR hy ya (hrg l hlr)
  obtain ⟨al, hal, hla, hsz⟩ := hlive.and (hR.lwf.within l hlP hlf)
  refine ⟨by simp [regionProv, hl], al, hal, hla, ?_, hsz⟩
  simp [regionAddr, hl, hal]

/-- R6 for `store a p` (MM-03.3 §9.2, O8; L6: `WriteStep` of the range of `p` with `ptrBytes` of the
region of `a`): under `WF3`, `dec` and `stat` (K5), the write has the outcome `ok`, the arrival
states are in `Repr`, and the range of `p` holds the bytes of the pointer. -/
theorem r6_store {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout} {s3 s3' : S3}
    {s2 : MM02.State} {pe : PtrEnc} {a p : Nat} (hwf : WF3 s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : StoreStep a p s3 (.ok s3')) (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hdec : ObW.dec s2 (leafAcc s2 L .write p) (ptrBytes pe s2 L (s3.afp a))) :
    AllOk C ObR ObW s2 (storeOps pe s2 L s3 a p) ∧
      Repr tok ptok provOf L s3' (exec s2 (storeOps pe s2 L s3 a p)) ∧
      rangeBytes (exec s2 (storeOps pe s2 L s3 a p)) L p = some ((List.range (L p).len).map
        fun i => .init (ptrBytes pe s2 L (s3.afp a) i).1 (ptrBytes pe s2 L (s3.afp a) i).2) := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, -⟩ := store_pre_auth hpre.1
  have hpu : s3.Usable p := hpre.2.1
  have hpleaf : isLeaf s3.P p := by
    have := hpre; unfold StorePre at this; exact this.2.2.2.2.2.1
  have hpf : p ∈ footprint s3.P p := mem_footprint.2 ⟨hpu.lt, hpleaf, hpu.lt, .inl rfl⟩
  have hlive := live_of_usable_part hwf hR.toReprB hpu hpf
  have hex : AllocP s2 (L p).alloc fun _ => True := hlive.mono fun _ _ => trivial
  refine ⟨⟨write_leaf_ok hstatW hlive hdec, trivial⟩, ⟨?_, exec_wf _ _ hR.wf2⟩,
    rangeBytes_write (Dom.refl _) hex⟩
  refine hR.toReprB.change (Dom.write _ _ _) (by rw [storeEff_eq hy]) (by rw [storeEff_eq hy])
    (by rw [storeEff_eq hy]) (by rw [storeEff_eq hy]) fun l _ _ hi => ?_
  rw [storeEff_eq hy] at hi; simp only at hi
  split at hi
  · rename_i e; subst e; exact .inr (write_leaf_init hex)
  · exact .inl hi

/-- R6 for `issue` (MM-03.3 §9.2, O18; L6: `WriteStep` of the range of the destination with
`ptrBytes` of the block; `available` and `issued` are abstract state of the arena entry): under
`WF3`, `dec` and `stat` (K5), the write has the outcome `ok`, the arrival states are in `Repr`, and
the range of the destination holds the bytes of the pointer. -/
theorem r6_issue {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout} {s3 s3' : S3}
    {s2 : MM02.State} {pe : PtrEnc} {i via dst : Nat} {region : List Nat} (hwf : WF3 s3)
    (hR : Repr tok ptok provOf L s3 s2) (h : IssueAt k i via region dst s3 (.ok s3'))
    (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hdec : ObW.dec s2 (leafAcc s2 L .write dst) (issueBytes pe s2 L s3 i region)) :
    AllOk C ObR ObW s2 (issueOps pe s2 L s3 i region dst) ∧
      Repr tok ptok provOf L s3' (exec s2 (issueOps pe s2 L s3 i region dst)) ∧
      rangeBytes (exec s2 (issueOps pe s2 L s3 i region dst)) L dst =
        some ((List.range (L dst).len).map fun j =>
          .init (issueBytes pe s2 L s3 i region j).1 (issueBytes pe s2 L s3 i region j).2) := by
  cases h with
  | ok har hst =>
    cases hst with
    | ok hstat _ _ _ =>
      have hdu : s3.Usable dst := hstat.2.2.2.1
      have hdleaf : isLeaf s3.P dst := hstat.2.2.2.2.2.2.1
      have hdf : dst ∈ footprint s3.P dst := mem_footprint.2 ⟨hdu.lt, hdleaf, hdu.lt, .inl rfl⟩
      have hlive := live_of_usable_part hwf hR.toReprB hdu hdf
      have hex : AllocP s2 (L dst).alloc fun _ => True := hlive.mono fun _ _ => trivial
      refine ⟨⟨write_leaf_ok hstatW hlive hdec, trivial⟩, ⟨?_, exec_wf _ _ hR.wf2⟩,
        rangeBytes_write (Dom.refl _) hex⟩
      refine hR.toReprB.change (Dom.write _ _ _) rfl rfl rfl rfl fun l _ _ hi => ?_
      simp only [arenaSet, issueEff, S3.addAuth] at hi
      split at hi
      · rename_i e; subst e; exact .inr (write_leaf_init hex)
      · exact .inl hi

/-- L6, `pointer_sound` for `store a p`: under the obligation of the encoding for the pointer
written (`PtrEncAt`), the bytes of the pointer (`ptrBytes`) decode to the address of the first leaf
`l` of the list of the region of `a` (base + offset), and each carries the provenance of the
allocation of `l`, which is live and contains the range of `l`; the range of `p` receives the first
`(L p).len` of these bytes. Whether they are enough to decode the address depends on the size of
`p` (pass-2 report, (e) 4); whether `l` holds the first byte of the region, on the layout
(pass-2 report, (e) 3). -/
theorem pointer_sound_store {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec}
    {ObW : MM02.WriteOblSpec} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat} {L : Layout}
    {s3 s3' : S3} {s2 : MM02.State} {pe : PtrEnc} {a p : Nat} (hwf : WF3 s3)
    (hnd : NoDangling s3) (hfl : FpLeaves s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : StoreStep a p s3 (.ok s3')) (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hdec : ObW.dec s2 (leafAcc s2 L .write p) (ptrBytes pe s2 L (s3.afp a)))
    {l : Nat} (hl : (s3.afp a).head? = some l)
    (hpe : PtrEncAt pe (regionAddr s2 L (s3.afp a)) (regionProv L (s3.afp a))) :
    pe.decode (ptrBytes pe s2 L (s3.afp a)) = regionAddr s2 L (s3.afp a) ∧
      (∀ i, (ptrBytes pe s2 L (s3.afp a) i).2 = some (L l).alloc) ∧
      (∃ al, s2.allocs (L l).alloc = some al ∧ al.live = true ∧
        regionAddr s2 L (s3.afp a) = al.base + (L l).off ∧ (L l).off + (L l).len ≤ al.size) ∧
      rangeBytes (exec s2 (storeOps pe s2 L s3 a p)) L p = some ((List.range (L p).len).map
        fun i => .init (ptrBytes pe s2 L (s3.afp a) i).1 (ptrBytes pe s2 L (s3.afp a) i).2) := by
  have hst := (r6_store (C := C) (ObR := ObR) hwf hR h hstatW hdec).2.2
  obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
  obtain ⟨y, hy, ya, -, -⟩ := store_pre_auth hpre.1
  have hrg : ∀ x ∈ s3.afp a, x ∈ y.footprint := fun x hx => by simpa [S3.afp, hy] using hx
  obtain ⟨hprov, hta⟩ := ptr_target hwf hnd hfl hR.toReprB hy ya hrg hl
  refine ⟨hpe.1, fun i => ?_, hta, hst⟩
  rw [← hprov]; exact hpe.2 i

/-- L6, provenance of `issue` ("prov: allocation of arena storage"): under `WF3`, `LayoutWF` and the
invariant of the arenas of MM-03 (`ArenasInv`, true on the reached states), every leaf `l` of the
block of an `ok` `issue` is in the allocation of every leaf of the storage of the arena, and
`arenaProv` is that allocation. -/
theorem issue_prov_storage {k : K} {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {i via dst : Nat}
    {region : List Nat} (hwf : WF3 s3) (hlw : LayoutWF L s3 s2) (hai : ArenasInv s3)
    (h : IssueAt k i via region dst s3 (.ok s3')) {l : Nat} (hl : l ∈ region) :
    arenaProv L s3 i = some (L l).alloc ∧ ∃ ar, s3.arenas[i]? = some ar ∧
      ∀ l' ∈ footprint s3.P ar.storage, (L l').alloc = (L l).alloc := by
  cases h with
  | @ok ar _ _ har hst =>
    cases hst with
    | ok hstat _ _ _ =>
      have hA := hai ar (List.mem_of_getElem? har) hstat.2.1
      have hsl : ar.storage < s3.P.length := hA.2.2.2.2.2.1
      obtain ⟨r, hr, hsr⟩ :=
        exists_rootPlace hwf (ar.storage + 1) ar.storage (Nat.lt_succ_self _) hsl
      have hlS : l ∈ footprint s3.P ar.storage := (hA.2.2.2.2.2.2.2 l).1 (hstat.2.2.1 l hl)
      have key : ∀ l' ∈ footprint s3.P ar.storage, (L l').alloc = (L l).alloc := fun l' hl' =>
        hlw.sameAlloc r hr.1 hr l' (footprint_sub hwf hsr hl') l (footprint_sub hwf hsr hlS)
      refine ⟨?_, ar, har, key⟩
      simp only [arenaProv, har, Option.map_some, key _ (headD_mem_footprint hwf hsl)]

/-- L6, `pointer_sound` for `issue`: under the obligation of the encoding for the pointer written
(`PtrEncAt`), the bytes of the pointer (`issueBytes`) decode to the address of the first leaf `l` of
the list of the block (base + offset), and each carries the provenance of the storage of the arena
(L6), the allocation of `l` and of every leaf of the storage, which is live and contains the range
of `l`; the range of the destination receives the first `(L dst).len` of these bytes (pass-2
report, (e) 3 and (e) 4). -/
theorem pointer_sound_issue {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec}
    {ObW : MM02.WriteOblSpec} {k : K} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 s3' : S3} {s2 : MM02.State} {pe : PtrEnc} {i via dst : Nat}
    {region : List Nat} (hwf : WF3 s3) (hnd : NoDangling s3) (hfl : FpLeaves s3)
    (hai : ArenasInv s3) (hR : Repr tok ptok provOf L s3 s2)
    (h : IssueAt k i via region dst s3 (.ok s3')) (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hdec : ObW.dec s2 (leafAcc s2 L .write dst) (issueBytes pe s2 L s3 i region))
    {l : Nat} (hl : region.head? = some l)
    (hpe : PtrEncAt pe (regionAddr s2 L region) (arenaProv L s3 i)) :
    pe.decode (issueBytes pe s2 L s3 i region) = regionAddr s2 L region ∧
      (∀ j, (issueBytes pe s2 L s3 i region j).2 = some (L l).alloc) ∧
      (∃ ar, s3.arenas[i]? = some ar ∧
        ∀ l' ∈ footprint s3.P ar.storage, (L l').alloc = (L l).alloc) ∧
      (∃ al, s2.allocs (L l).alloc = some al ∧ al.live = true ∧
        regionAddr s2 L region = al.base + (L l).off ∧ (L l).off + (L l).len ≤ al.size) ∧
      rangeBytes (exec s2 (issueOps pe s2 L s3 i region dst)) L dst =
        some ((List.range (L dst).len).map fun j =>
          .init (issueBytes pe s2 L s3 i region j).1 (issueBytes pe s2 L s3 i region j).2) := by
  have hst := (r6_issue (C := C) (ObR := ObR) hwf hR h hstatW hdec).2.2
  have hlm : l ∈ region :=
    List.mem_of_getElem? (by rw [List.head?_eq_getElem?] at hl; exact hl)
  obtain ⟨hprov, hsto⟩ := issue_prov_storage hwf hR.lwf hai h hlm
  cases h with
  | ok har hstep =>
    cases hstep with
    | ok hstat _ _ _ =>
      obtain ⟨y, hy, ya⟩ := hstat.2.1
      have hrg : ∀ x ∈ region, x ∈ y.footprint := fun x hx => by
        have := hstat.2.2.1 x hx; simpa [S3.afp, hy] using this
      obtain ⟨-, hta⟩ := ptr_target hwf hnd hfl hR.toReprB hy ya hrg hl
      refine ⟨hpe.1, fun j => ?_, hsto, hta, hst⟩
      rw [← hprov]; exact hpe.2 j

/-! ## Real `DDSound` (L7) -/

/-- L7: instantiation of `K.DeclaredDisjoint` by the disjointness of the byte ranges of the leaves
of the two regions: every leaf of `r` and every leaf of `r'` are in different allocations or in
disjoint ranges (MM-02.2, `RangeDisjoint`). -/
def ByteDisjoint (L : Layout) (r r' : List Nat) : Prop :=
  ∀ l ∈ r, ∀ l' ∈ r', (L l).alloc ≠ (L l').alloc ∨
    MM02.RangeDisjoint (L l).off (L l).len (L l').off (L l').len

/-- `ddSound_of_layout` (L7; MM-03.3.8, `DDSound`): when every declaration of disjointness of `K`
implies the byte disjointness of the leaves of the two regions (an obligation of the library that
declares it), and the leaves of a declared region have non-empty ranges, `DDSound` holds. The
non-empty ranges are needed: a leaf of size zero (K1 (d)) is byte-disjoint from itself
(`ddSound_of_layout_needs_size`). -/
theorem ddSound_of_layout {k : K} {L : Layout}
    (h : ∀ r r', k.DeclaredDisjoint r r' → ByteDisjoint L r r')
    (hpos : ∀ r r', k.DeclaredDisjoint r r' → ∀ l ∈ r, 0 < (L l).len) : DDSound k := by
  intro r r' hd l hl hl'
  rcases h r r' hd l hl l hl' with e | e
  · exact e rfl
  · exact e (L l).off (Nat.le_refl _) (by have := hpos r r' hd l hl; omega) (Nat.le_refl _)
      (by have := hpos r r' hd l hl; omega)

/-- L7: the instantiation itself, `K.DeclaredDisjoint := ByteDisjoint L`, satisfies `DDSound` when
every range is non-empty. -/
theorem ddSound_instance (k : K) {L : Layout} (hpos : ∀ l, 0 < (L l).len) :
    DDSound { k with DeclaredDisjoint := ByteDisjoint L } :=
  ddSound_of_layout (fun _ _ h => h) fun _ _ _ l _ => hpos l

/-- Counterexample kept (pass-2 report, (e) 1): with a leaf of size zero, allowed by K1 (d), the
instantiation of L7 declares a region disjoint from itself, and `DDSound` fails. -/
theorem ddSound_of_layout_needs_size (k : K) :
    ¬ DDSound { k with DeclaredDisjoint := ByteDisjoint fun _ => ⟨0, 0, 0⟩ } := fun h =>
  h [0] [0] (fun _ _ _ _ => .inr fun _ h1 h2 _ _ => by simp only at h1 h2; omega) 0
    (List.mem_singleton_self _) (List.mem_singleton_self _)

/-- The layout of the counterexample satisfies `LayoutWF` on a state with one static leaf and an
allocation of size zero: the failure is under `LayoutWF`, as L7 states it. -/
example : LayoutWF (fun _ => ⟨0, 0, 0⟩) (S3.init [((none, none, 0), false)])
    (MM02.State.empty.alloc 0 0 0 1 none) := by decide

/-- L7, exactness of the instantiation under `LayoutWF` (K1 (b)): two lists of leaves without
common leaf are byte-disjoint, so an abstraction can declare every pair of regions that share no
leaf. -/
theorem byteDisjoint_of_leaves {L : Layout} {s3 : S3} {s2 : MM02.State} (hlw : LayoutWF L s3 s2)
    {r r' : List Nat} (hr : ∀ l ∈ r, l < s3.P.length ∧ isLeaf s3.P l)
    (hr' : ∀ l ∈ r', l < s3.P.length ∧ isLeaf s3.P l) (hd : ∀ l ∈ r, l ∉ r') :
    ByteDisjoint L r r' := by
  intro l hl l' hl'
  by_cases e : (L l).alloc = (L l').alloc
  · exact .inr (hlw.disjoint l (hr l hl).1 l' (hr' l' hl').1 (hr l hl).2 (hr' l' hl').2
      (fun h => hd l hl (h ▸ hl')) e)
  · exact .inl e

/-! ## Pinned addresses (L8) -/

/-- Pinned leaves stay live (MM-03.3 §3 O15; A8): every leaf of an existing place that is pinned,
dynamically (`pin`) or statically (`K.Pinned`, MM-03.3.8), is usable. -/
def PinnedLive (k : K) (s : S3) : Prop :=
  ∀ l < s.P.length, isLeaf s.P l → (s.pin l = true ∨ k.Pinned l) → s.Usable l

/-- A pinned usable leaf stays usable across every `ok` step (MM-03.3 §3 O15: `transfer`, `endUse`,
`free` and `exitFrame` are rejected on pinned leaves; O4.5, O12.4, O13.4, §4 O7.3 (B4)). The other
steps keep or extend the places, the stack and the `dead` flags. -/
theorem step_pinned_usable {k : K} {s s' : S3} (hw : WF3 s) (hp : PinnedLive k s)
    (h : Step k s s') : ∀ l < s.P.length, isLeaf s.P l → (s.pin l = true ∨ k.Pinned l) →
      s'.Usable l := by
  intro l hl hleaf hpin
  have hu := hp l hl hleaf hpin
  -- A step that keeps places, stack and `dead` flags keeps usability.
  have same : ∀ {t : S3}, t.P = s.P → t.F = s.F → t.dead = s.dead → t.Usable l :=
    fun hP hF hd => (S3.Usable.congr hP hF hd).2 hu
  -- A leaf that stops being usable must not be pinned.
  have unpinned : ∀ {t : S3}, (¬ t.Usable l → s.pin l = false ∧ ¬ k.Pinned l) → t.Usable l :=
    fun hc => Decidable.byContradiction fun hn => by
      obtain ⟨h1, h2⟩ := hc hn
      rcases hpin with h3 | h3
      · rw [h1] at h3; cases h3
      · exact h2 h3
  cases h with
  | kernel h =>
    cases h with
    | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | release hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      unfold releaseEff; split <;> exact same rfl rfl rfl
    | transfer hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      exact transfer_usable_fwd hw hpre.2.2.2.2.2.2.2.1 hu
    | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | enter hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact enter_usable_old hu
    | exit hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      unfold ExitPre at hpre
      split at hpre
      · rename_i f F₀ hF
        -- A leaf is in its own footprint.
        have hu' : ({ s with F := F₀ } : S3).Usable l := unpinned fun hn =>
          hpre.2.2.2.1 l (List.mem_range.2 hl) hu hn l (mem_footprint.2 ⟨hl, hleaf, hl, .inl rfl⟩)
        rw [exitEff_eq hF]; exact S3.Usable.of_eqs (s' := { s with F := F₀ }) hu' rfl rfl rfl
      · exact hpre.elim
    | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hu
    | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
    | @endUse p hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      -- `cleanup` changes only authorities.
      refine (S3.Usable.congr (s := endUseS s p) (s' := endUseEff s p) rfl rfl rfl).2
        (unpinned fun hn => ?_)
      exact hpre.2.2.2.2 l (List.mem_range.2 hl) (.inr ⟨hu, hn⟩)
    | @free p _ hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      refine (S3.Usable.congr (s := freeS s p) (s' := freeEff s p) rfl rfl rfl).2
        (unpinned fun hn => ?_)
      exact hpre.2.2.2.2.2.2.2 l (List.mem_range.2 hl) (.inr ⟨hu, hn⟩)
    | alloc hs => cases hs with | ok _ _ => exact alloc_usable_old hu
    | store hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      unfold storeEff; split <;> exact same rfl rfl rfl
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact same rfl rfl rfl
  | issue hs => cases hs with | ok _ hst => cases hst with | ok => exact same rfl rfl rfl
  | reset hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold resetAtEff; split <;> exact same rfl rfl rfl

/-- What a step does to the places and pins of `s` (MM-03.3 §3–6; A5, A8): it keeps the existing
places and their parents, appends new usable places (`enterFrame` O6, `alloc` O14), and pins
an unpinned leaf only through `pin` (O15), which pins leaves of a usable place. -/
theorem step_extends {k : K} {s s' : S3} (hw : WF3 s) (h : Step k s s') :
    s.P.length ≤ s'.P.length ∧ (∀ r < s.P.length, parentOf s'.P r = parentOf s.P r) ∧
    (∀ l < s.P.length, s'.pin l = true → s.pin l = true ∨ s'.Usable l) ∧
    (∀ q < s'.P.length, s.P.length ≤ q → s'.Usable q) := by
  have frozen : ∀ {t : S3}, t.P.length = s.P.length → parentOf t.P = parentOf s.P →
      t.pin = s.pin →
      s.P.length ≤ t.P.length ∧ (∀ r < s.P.length, parentOf t.P r = parentOf s.P r) ∧
      (∀ l < s.P.length, t.pin l = true → s.pin l = true ∨ t.Usable l) ∧
      (∀ q < t.P.length, s.P.length ≤ q → t.Usable q) :=
    fun hlen hpar hpin => ⟨Nat.le_of_eq hlen.symm, fun r _ => by rw [hpar],
      fun l _ hl => .inl (hpin ▸ hl), fun q hq hge => absurd (hlen ▸ hq) (Nat.not_lt.2 hge)⟩
  cases h with
  | kernel h =>
    cases h with
    | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | release hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      unfold releaseEff; split <;> exact frozen rfl rfl rfl
    | transfer hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      exact frozen (transfer_len s _ _) (transfer_parentOf s _ _) rfl
    | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | @enter ps ls hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      have hlen : (enterEff s ps ls).P.length = s.P.length + ls.length := enterP_len s ls
      refine ⟨by rw [hlen]; exact Nat.le_add_right _ _, fun r hr => ?_, fun l hl hpl => ?_,
        fun q hq hge => ?_⟩
      · show parentOf (shapeP s.P (.frame s.nF) ls) r = _
        exact shape_parentOf_lt hr
      · simp only [enterEff, Nat.not_le.2 hl, ↓reduceIte] at hpl
        exact .inl hpl
      · rw [hlen] at hq
        have := enter_usable_new hpre.1 (q - s.P.length + 1) (q - s.P.length)
          (Nat.lt_succ_self _) (by omega)
        rwa [Nat.add_sub_cancel' hge] at this
    | exit hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      unfold ExitPre at hpre
      split at hpre
      · rename_i f F₀ hF
        rw [exitEff_eq hF]; exact frozen rfl rfl rfl
      · exact hpre.elim
    | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | @pin p hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      refine ⟨Nat.le_refl _, fun _ _ => rfl, fun l _ hpl => ?_,
        fun q hq hge => absurd hq (Nat.not_lt.2 hge)⟩
      by_cases hm : l ∈ footprint s.P p
      · -- A leaf of the usable place `p` is usable (A5).
        exact .inr ((S3.Usable.congr (s := s) (s' := pinEff s p true) rfl rfl rfl).2
          (usable_of_partOf hw (l + 1) l p (Nat.lt_succ_self l) (mem_footprint.1 hm).2.2 hpre.1))
      · simp only [pinEff, hm, ↓reduceIte] at hpl
        exact .inl hpl
    | @unpin p hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      refine ⟨Nat.le_refl _, fun _ _ => rfl, fun l _ hpl => ?_,
        fun q hq hge => absurd hq (Nat.not_lt.2 hge)⟩
      simp only [pinEff] at hpl
      split at hpl
      · cases hpl
      · exact .inl hpl
    | endUse hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | free hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
    | @alloc pr ow ls hs =>
      cases hs with
      | ok hst _ =>
        have hlen : (allocEff s pr ow ls).P.length = s.P.length + ls.length := allocP_len s ow ls
        refine ⟨by rw [hlen]; exact Nat.le_add_right _ _, fun r hr => ?_, fun l hl hpl => ?_,
          fun q hq hge => ?_⟩
        · exact shape_parentOf_lt hr
        · simp only [allocEff, Nat.not_le.2 hl, ↓reduceIte] at hpl
          exact .inl hpl
        · rw [hlen] at hq
          have := alloc_usable_new hst (q - s.P.length + 1) (q - s.P.length)
            (Nat.lt_succ_self _) (by omega)
          rwa [Nat.add_sub_cancel' hge] at this
    | store hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      unfold storeEff; split <;> exact frozen rfl rfl rfl
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact frozen rfl rfl rfl
  | issue hs => cases hs with | ok _ hst => cases hst with | ok => exact frozen rfl rfl rfl
  | reset hs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
    unfold resetAtEff; split <;> exact frozen rfl rfl rfl

/-- `PinnedLive` is preserved by every `ok` step (MM-03.3 §3 O15; O4.5, O12.4, O13.4, §4 O7.3
(B4)): old pinned leaves stay usable, a leaf pinned by `pin` is a leaf of a usable place, and new
places, unpinned, are usable. -/
theorem step_pinnedLive {k : K} {s s' : S3} (hw : WF3 s) (hp : PinnedLive k s) (h : Step k s s') :
    PinnedLive k s' := by
  obtain ⟨hlen, hpar, hpin, hnew⟩ := step_extends hw h
  intro l hl' hleaf' hpin'
  rcases Nat.lt_or_ge l s.P.length with hl | hl
  · have hleaf : isLeaf s.P l := fun r hr e =>
      hleaf' r (Nat.lt_of_lt_of_le hr hlen) ((hpar r hr).trans e)
    rcases hpin' with hd | hk
    · rcases hpin l hl hd with hd | hu
      · exact step_pinned_usable hw hp h l hl hleaf (.inl hd)
      · exact hu
    · exact step_pinned_usable hw hp h l hl hleaf (.inr hk)
  · exact hnew l hl' hl

/-- On reached states, pinned leaves are usable (MM-03.3 §3 O15; §10; D1: the static places are
usable in the initial state). Under `DDSound k` (MM-03.3.8), which gives `WF3`. -/
theorem reachable_pinnedLive {k : K} (hdd : DDSound k) {statics : Statics} {s : S3}
    (h : Reachable k statics s) : PinnedLive k s := by
  induction h with
  | init hsh =>
    intro l hl _ _
    exact init_usable hsh (l + 1) l (Nat.lt_succ_self l) (by rwa [init_len] at hl)
  | derive h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.derive hs))
  | split h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.split hs))
  | release h0 hs ih =>
    exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.release hs))
  | transfer h0 hs ih =>
    exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.transfer hs))
  | depend h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.depend hs))
  | enter h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.enter hs))
  | exit h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.exit hs))
  | read h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.read hs))
  | write h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.write hs))
  | writeShared h0 hs ih =>
    exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.writeShared hs))
  | pin h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.pin hs))
  | unpin h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.unpin hs))
  | endUse h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.endUse hs))
  | free h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.free hs))
  | alloc h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.alloc hs))
  | newArena h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.newArena hs)
  | issue h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.issue hs)
  | reset h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.reset hs)
  | store h0 hs ih => exact step_pinnedLive (reachable_invariants hdd h0).1 ih (.kernel (.store hs))

/-- An `ok` step keeps every leaf of the places of `s` a leaf (MM-03.3.2; C6: the places it creates
have new parents). -/
theorem step_isLeaf_old {k : K} {s s' : S3} (h : Step k s s') {l : Nat} (hl : l < s.P.length)
    (hlf : isLeaf s.P l) : isLeaf s'.P l := by
  cases h with
  | kernel hk =>
    cases hk with
    | enter hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      exact (shape_isLeaf_old (enterPre_shapeOK hpre.1) hl).2 hlf
    | alloc hs =>
      cases hs with
      | ok hst _ => exact (shape_isLeaf_old hst.2.2.2.2.2.1 hl).2 hlf
    | transfer hs =>
      rename_i src dst
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs
      refine isLeaf_of_parentOf (by simp [transferEff]) ?_ hlf
      funext i; simp only [parentOf, transferEff, List.getElem?_map]
      cases s.P[i]? with
      | none => rfl
      | some pl => simp only [Option.map_some, Option.bind_some]; split <;> rfl
    | release hs =>
      obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; unfold releaseEff; split <;> exact hlf
    | exit hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; unfold exitEff; split <;> exact hlf
    | store hs =>
      obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 hs
      obtain ⟨y, hy, -⟩ := store_pre_auth hpre.1
      rw [storeEff_eq hy]; exact hlf
    | derive hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | split hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | depend hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | read hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | write hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | writeShared hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | pin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | unpin hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | endUse hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
    | free hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
  | newArena hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; exact hlf
  | issue hs =>
    cases hs with
    | ok _ hst => cases hst with
      | ok _ _ _ _ => exact hlf
  | reset hs => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hs; unfold resetAtEff; split <;> exact hlf

/-- The bases of the registered allocations: a sequence of MM-02 operations from a state with fresh
identities changes the base of no registered allocation (MM-02.A: an allocation leaves the others
intact; MM-02.C, MM-02.D: a write and a deallocation keep the base). -/
theorem exec_keeps_base : ∀ (ops : List Op2) (s : MM02.State), MM02.WF s → ∀ i (a : MM02.Alloc),
    s.allocs i = some a → ∃ b, (exec s ops).allocs i = some b ∧ b.base = a.base
  | [], _, _, _, a, h => ⟨a, h, rfl⟩
  | o :: os, s, hwf, i, a, h => by
    obtain ⟨b, hb, e⟩ : ∃ b, (o.eff s).allocs i = some b ∧ b.base = a.base := by
      cases o with
      | read _ => exact ⟨a, h, rfl⟩
      | write ac w =>
        obtain ⟨b, hb, -, e, -⟩ := Dom.write s ac w i a h; exact ⟨b, hb, e⟩
      | dealloc id _ =>
        by_cases e : i = id
        · refine ⟨{ a with live := false }, ?_, rfl⟩
          show (s.dealloc id).allocs i = _
          rw [dealloc_allocs, h]; simp only [e, ↓reduceIte, Option.map_some]
        · refine ⟨a, ?_, rfl⟩
          show (s.dealloc id).allocs i = _
          rw [dealloc_allocs, h]; simp only [e, ↓reduceIte]
      | alloc sp b sz al fa =>
        obtain ⟨b', hb', -, e, -⟩ := Dom.alloc hwf sp b sz al fa i a h; exact ⟨b', hb', e⟩
    obtain ⟨c, hc, e'⟩ := exec_keeps_base os (o.eff s) (by
      cases o
      · exact hwf
      · exact MM02.write_wf hwf _ _
      · exact MM02.dealloc_wf hwf _
      · exact MM02.alloc_wf hwf _ _ _ _ _) i b hb
    exact ⟨c, hc, e'.trans e⟩

/-- MM-03.3 §10 (annex A.3: "théorème reliant tous les constructeurs `Reachable` à `Step`"): one
`Step` from a reached state reaches a state. -/
theorem Reachable.ofStep {k : K} {statics : Statics} {s s' : S3} (hr : Reachable k statics s)
    (h : Step k s s') : Reachable k statics s' := by
  cases h with
  | kernel hk =>
    cases hk with
    | derive hs => exact .derive hr hs
    | split hs => exact .split hr hs
    | release hs => exact .release hr hs
    | transfer hs => exact .transfer hr hs
    | depend hs => exact .depend hr hs
    | enter hs => exact .enter hr hs
    | exit hs => exact .exit hr hs
    | read hs => exact .read hr hs
    | write hs => exact .write hr hs
    | writeShared hs => exact .writeShared hr hs
    | pin hs => exact .pin hr hs
    | unpin hs => exact .unpin hr hs
    | endUse hs => exact .endUse hr hs
    | free hs => exact .free hr hs
    | alloc hs => exact .alloc hr hs
    | store hs => exact .store hr hs
  | newArena hs => exact .newArena hr hs
  | issue hs => exact .issue hr hs
  | reset hs => exact .reset hr hs

/-- L8, the address of a leaf in an MM-02 state: the base of its allocation plus its offset. -/
def leafAddr (s2 : MM02.State) (L : Layout) (l : Nat) : Nat :=
  (((s2.allocs (L l).alloc).map (·.base)).getD 0) + (L l).off

/-- `pinned_address_stable` (L8; MM-03.3 O15, §9.1.6): for an `ok` step of MM-03 from a reached
state and an MM-02 sequence after which the arrival states are in `Repr` (the sequence of the step,
`r6_*`), every leaf pinned before the step, dynamically or statically (`K.Pinned`), has a live
allocation before and after, and the same address (base + offset). The content is the liveness:
MM-02 models no physical move of an allocation, and the theorem claims nothing about moves. Under
`DDSound k`. -/
theorem pinned_address_stable {k : K} {statics : Statics} {tok ptok : Nat → Nat}
    {provOf provOf' : Nat → Option Nat} {L : Layout} {s3 s3' : S3} {s2 : MM02.State}
    {ops : List Op2} (hdd : DDSound k) (hr : Reachable k statics s3) (hs : Step k s3 s3')
    (hR : Repr tok ptok provOf L s3 s2) (hR' : Repr tok ptok provOf' L s3' (exec s2 ops)) {l : Nat}
    (hl : l < s3.P.length) (hlf : isLeaf s3.P l) (hpin : s3.pin l = true ∨ k.Pinned l) :
    LiveAlloc s2 (L l).alloc ∧ LiveAlloc (exec s2 ops) (L l).alloc ∧
      leafAddr (exec s2 ops) L l = leafAddr s2 L l := by
  have hwf := (reachable_invariants hdd hr).1
  have hp := reachable_pinnedLive hdd hr
  have hu := hp l hl hlf hpin
  have hu' := step_pinned_usable hwf hp hs l hl hlf hpin
  have hwf' : WF3 s3' := (reachable_invariants hdd (Reachable.ofStep hr hs)).1
  have hlf' := step_isLeaf_old hs hl hlf
  have hl' : l < s3'.P.length := Nat.lt_of_lt_of_le hl (step_extends hwf hs).1
  have hlive := (live_of_usable_part hwf hR.toReprB hu
    (mem_footprint.2 ⟨hl, hlf, hl, .inl rfl⟩)).mono fun _ h => h.1
  have hlive' := (live_of_usable_part hwf' hR'.toReprB hu'
    (mem_footprint.2 ⟨hl', hlf', hl', .inl rfl⟩)).mono fun _ h => h.1
  refine ⟨hlive, hlive', ?_⟩
  obtain ⟨a, ha, -⟩ := hlive
  obtain ⟨b, hb, e⟩ := exec_keeps_base ops s2 hR.wf2 _ a ha
  simp only [leafAddr, ha, hb, Option.map_some, Option.getD_some, e]

/-! ## R4 (MM-03.3 §9.2) -/

/-- R4 (MM-03.3 §9.2, from `NoDangling`, §2.6): on a reached state of MM-03 in `Repr` with an MM-02
state, no active authority covers a leaf whose MM-02 allocation is dead; the allocation of every
leaf it covers is registered and live. Under `DDSound k`, the hypothesis of the invariants of the
reached states. -/
theorem r4_no_dead_cover {k : K} {statics : Statics} {tok ptok : Nat → Nat} {provOf : Nat → Option Nat}
    {L : Layout} {s3 : S3}
    {s2 : MM02.State} (hdd : DDSound k) (hr : Reachable k statics s3)
    (hR : Repr tok ptok provOf L s3 s2) :
    ∀ (j : Nat) (y : Authority), s3.A[j]? = some y → y.active = true → ∀ l ∈ y.footprint,
      isLeaf s3.P l ∧ ¬ DeadAlloc s2 (L l).alloc ∧ LiveAlloc s2 (L l).alloc := by
  intro j y hy ya l hl
  obtain ⟨-, hlf, hlive⟩ := covered_live (reachable_invariants hdd hr).1
    (reachable_invariants hdd hr).2.1.nd (reachable_fpLeaves_frameOwnedLive hdd hr).1 hR.toReprB hy ya
    hl
  refine ⟨hlf, fun hd => ?_, hlive⟩
  obtain ⟨a, ha, hla⟩ := hlive
  obtain ⟨b, hb, hlb⟩ := hd
  rw [ha] at hb; cases hb; rw [hla] at hlb; cases hlb

/-! ## Exclusive bytes (MM-03.3 §9.1.8) -/

/-- `exclusive_bytes` (MM-03.3 §2.2, §9.1.8; K1 (b)): under I1 and `LayoutWF` (the clause `lwf` of
`Repr`), if an authority `a` has the effective mode `Modify` on a leaf `l`, no other authority `b`
has an effective mode on a leaf `l'` whose range overlaps the range of `l` (same allocation, ranges
not disjoint). The task asks it of the active authorities that do not descend from `a`; neither
condition is used: an active descendant of `a` covering `l` would remove the effective `Modify` of
`a` (MM-03.3.5), and an inactive authority has no effective mode. Memory justification of
non-aliasing, on the side of the kernel only. -/
theorem exclusive_bytes {L : Layout} {s3 : S3} {s2 : MM02.State} (hlw : LayoutWF L s3 s2)
    (hI1 : I1 s3) {a b l l' : Nat} (hl : l < s3.P.length) (hlf : isLeaf s3.P l)
    (hl' : l' < s3.P.length) (hlf' : isLeaf s3.P l') (ha : effective s3 a l = some .modify)
    (hab : a ≠ b) (hsame : (L l).alloc = (L l').alloc)
    (hover : ¬ MM02.RangeDisjoint (L l).off (L l).len (L l').off (L l').len) :
    effective s3 b l' = none := by
  by_cases e : l = l'
  · subst e; exact effective_exclusive hI1 hab ha
  · exact absurd (hlw.disjoint l hl l' hl' hlf hlf' e hsame) hover

/-! ## Simulation (step 5 of the task) -/

/-- An operation of MM-03 with its arguments (MM-03.3 §3–6), the bytes written by `write3` and
`writeShared` included: they are data of the program, not a choice of the refinement. -/
inductive Op3 where
  | derive (src q : Nat) (m : Mode)
  | split (src : Nat) (rs : List (List Nat))
  | release (a : Nat)
  | transfer (src dst : Nat)
  | depend (q x : Nat)
  | enter (ps : List Nat) (ls : List (Option Nat × Option Nat × Nat))
  | exit
  | read (a : Nat) (ls : List Nat)
  | write (a : Nat) (ls : List Nat) (w : Nat → Nat → UInt8 × Option Nat)
  | writeShared (a : Nat) (ls : List Nat) (w : Nat → Nat → UInt8 × Option Nat)
  | pin (p : Nat)
  | unpin (p : Nat)
  | endUse (p : Nat)
  | free (p auth : Nat)
  | alloc (pr ow : Nat) (ls : List (Option Nat × Option Nat × Nat))
  | newArena (st i : Nat)
  | issue (i via : Nat) (region : List Nat) (dst : Nat)
  | reset (i via : Nat)
  | store (a p : Nat)

/-- L1: the shape of an `enterFrame` has no owning element: its locals are owned by the frame. -/
def NoOwner (ls : List (Option Nat × Option Nat × Nat)) : Prop :=
  ∀ i < ls.length, (ls[i]?).bind (·.2.1) = none

instance (ls : List (Option Nat × Option Nat × Nat)) : Decidable (NoOwner ls) := by
  unfold NoOwner; infer_instance

/-- An `ok` step of MM-03 labelled by its operation, within the envelope of L1 (an `enterFrame`
whose shape has an owning element is outside the language) and L2 (the shape of `alloc` has exactly
one root). -/
def Step3 (k : K) : Op3 → S3 → S3 → Prop
  | .derive src q m, s, s' => DeriveStep src q m s (.ok s')
  | .split src rs, s, s' => SplitStep k src rs s (.ok s')
  | .release a, s, s' => ReleaseStep a s (.ok s')
  | .transfer src dst, s, s' => TransferStep k src dst s (.ok s')
  | .depend q x, s, s' => DependStep q x s (.ok s')
  | .enter ps ls, s, s' => NoOwner ls ∧ EnterStep ps ls s (.ok s')
  | .exit, s, s' => ExitStep k s (.ok s')
  | .read a ls, s, s' => Read3Step a ls s (.ok s')
  | .write a ls _, s, s' => Write3Step a ls s (.ok s')
  | .writeShared a ls _, s, s' => WriteSharedStep k a ls s (.ok s')
  | .pin p, s, s' => PinStep p s (.ok s')
  | .unpin p, s, s' => UnpinStep k p s (.ok s')
  | .endUse p, s, s' => EndUseStep k p s (.ok s')
  | .free p auth, s, s' => FreeStep k p auth s (.ok s')
  | .alloc pr ow ls, s, s' => (∃ i, rootIdx ls = [i]) ∧ AllocStep k pr ow ls s (.ok s')
  | .newArena st i, s, s' => NewArenaStep st i s (.ok s')
  | .issue i via region dst, s, s' => IssueAt k i via region dst s (.ok s')
  | .reset i via, s, s' => ResetAtStep k i via s (.ok s')
  | .store a p, s, s' => StoreStep a p s (.ok s')

/-- A labelled step is a step of `Reachable` (MM-03.3 §10). -/
theorem Step3.step {k : K} {op : Op3} {s s' : S3} (h : Step3 k op s s') : Step k s s' := by
  cases op with
  | derive => exact .kernel (.derive h)
  | split => exact .kernel (.split h)
  | release => exact .kernel (.release h)
  | transfer => exact .kernel (.transfer h)
  | depend => exact .kernel (.depend h)
  | enter => exact .kernel (.enter h.2)
  | exit => exact .kernel (.exit h)
  | read => exact .kernel (.read h)
  | write => exact .kernel (.write h)
  | writeShared => exact .kernel (.writeShared h)
  | pin => exact .kernel (.pin h)
  | unpin => exact .kernel (.unpin h)
  | endUse => exact .kernel (.endUse h)
  | free => exact .kernel (.free h)
  | alloc => exact .kernel (.alloc h.2)
  | newArena => exact .newArena h
  | issue => exact .issue h
  | reset => exact .reset h
  | store => exact .kernel (.store h)

/-- An execution of MM-03 from `S3.init statics` within the envelope of L1 and L2: the operations,
most recent first, and the state reached. -/
inductive Exec3 (k : K) (statics : Statics) : List Op3 → S3 → Prop where
  | init : ShapeOK 0 (statics.map (·.1)) → Exec3 k statics [] (S3.init statics)
  | step {ops : List Op3} {s s' : S3} {op : Op3} : Exec3 k statics ops s → Step3 k op s s' →
      Exec3 k statics (op :: ops) s'

theorem Exec3.reachable {k : K} {statics : Statics} {ops : List Op3} {s : S3}
    (h : Exec3 k statics ops s) : Reachable k statics s := by
  induction h with
  | init hsh => exact .init hsh
  | step _ hs ih => exact Reachable.ofStep ih hs.step

/-- Parameters of the refinement fixed once for a whole execution (step 5): the layout, the frame
and provider tokens (K2, L4), the placement (K2), the geometry of the allocation of each root place,
read on its index, the encoding of pointers (L6), the initial bytes of the statics (K3). -/
structure Params where
  L : Layout
  tok : Nat → Nat
  ptok : Nat → Nat
  pl : Placement
  geom : Nat → Geom
  pe : PtrEnc
  w0 : Nat → Nat → UInt8 × Option Nat

/-- K4, L6: the MM-02 sequence associated with an MM-03 operation from the states `s3`, `s2`. -/
def assoc (π : Params) : Op3 → S3 → MM02.State → List Op2
  | .read _ ls, _, s2 => readOps s2 π.L ls
  | .write _ ls w, _, s2 => writeOps s2 π.L w ls
  | .writeShared _ ls w, _, s2 => writeOps s2 π.L w ls
  | .transfer src dst, s3, s2 => transferOps s2 π.L s3.P src dst
  | .store a p, s3, s2 => storeOps π.pe s2 π.L s3 a p
  | .issue i _ region dst, s3, s2 => issueOps π.pe s2 π.L s3 i region dst
  | .alloc pr _ ls, s3, s2 =>
    allocOps π.pl (fun i => π.geom (s3.P.length + i)) (some (π.ptok pr)) s2 (rootIdx ls)
  | .enter _ ls, s3, s2 =>
    allocOps π.pl (fun i => π.geom (s3.P.length + i)) (some (π.tok s3.nF)) s2 (rootIdx ls)
  | .free p auth, s3, _ => deallocOps [rootAlloc π.L s3.P p] auth
  | .exit, s3, _ => exitOps π.L π.tok s3
  | _, _, _ => []

/-- L4: the ghost `provOf` after an operation: `alloc pr _ ls` maps the places it creates to the
provider `pr`; no other operation changes it. -/
def provStep : Op3 → S3 → (Nat → Option Nat) → Nat → Option Nat
  | .alloc pr _ ls, s3, pv => fun r =>
    if s3.P.length ≤ r ∧ r < s3.P.length + ls.length then some pr else pv r
  | _, _, pv => pv

/-- K3: the MM-02 operations of the initial state with the parameters `π`. -/
def initOpsOf (π : Params) (statics : Statics) : List Op2 :=
  initOps π.pl π.geom π.tok π.L π.w0 statics

/-- The lock-step translation of an MM-03 execution: the operations (most recent first), the MM-03
state, the ghost `provOf`, the MM-02 operations (in the order of execution) and the MM-02 state.
It starts with the MM-02 run of `repr_init`; each MM-03 step appends its associated sequence. It is
determined by the execution and the parameters. -/
inductive Trans (k : K) (statics : Statics) (π : Params) :
    List Op3 → S3 → (Nat → Option Nat) → List Op2 → MM02.State → Prop where
  | init : ShapeOK 0 (statics.map (·.1)) →
      Trans k statics π [] (S3.init statics) (fun _ => none) (initOpsOf π statics)
        (exec MM02.State.empty (initOpsOf π statics))
  | step {ops : List Op3} {s3 s3' : S3} {pv : Nat → Option Nat} {os : List Op2}
      {s2 : MM02.State} {op : Op3} :
      Trans k statics π ops s3 pv os s2 → Step3 k op s3 s3' →
      Trans k statics π (op :: ops) s3' (provStep op s3 pv) (os ++ assoc π op s3 s2)
        (exec s2 (assoc π op s3 s2))

/-- Every MM-03 execution has a translation. -/
theorem Trans.of_exec {k : K} {statics : Statics} (π : Params) {ops : List Op3} {s3 : S3}
    (h : Exec3 k statics ops s3) : ∃ pv os s2, Trans k statics π ops s3 pv os s2 := by
  induction h with
  | init hsh => exact ⟨_, _, _, .init hsh⟩
  | step _ hs ih => obtain ⟨pv, os, s2, ht⟩ := ih; exact ⟨_, _, _, ht.step hs⟩

/-- K1, K2: the layout obligation of an operation that creates root places: the new roots are laid
out in fresh allocations, within their geometry (`NewLayout`). -/
def LayoutObl (π : Params) : Op3 → S3 → S3 → MM02.State → Prop
  | .enter _ ls, s3, s3', s2 =>
    NewLayout π.L s3'.P s3.P.length s2.next (fun i => π.geom (s3.P.length + i)) (rootIdx ls)
  | .alloc _ _ ls, s3, s3', s2 =>
    NewLayout π.L s3'.P s3.P.length s2.next (fun i => π.geom (s3.P.length + i)) (rootIdx ls)
  | _, _, _, _ => True

instance (π : Params) (op : Op3) (s3 s3' : S3) (s2 : MM02.State) :
    Decidable (LayoutObl π op s3 s3' s2) := by
  cases op <;> unfold LayoutObl <;> infer_instance

theorem ReprB.provOf_congr {tok ptok : Nat → Nat} {pv pv' : Nat → Option Nat} {L : Layout}
    {s3 : S3} {s2 : MM02.State} (hR : ReprB tok ptok pv L s3 s2)
    (h : ∀ r < s3.P.length, pv' r = pv r) : ReprB tok ptok pv' L s3 s2 :=
  { hR with provTokens := fun r hr hrt => by rw [h r hr]; exact hR.provTokens r hr hrt }

theorem decAlong_readOps {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec} {s2 s2' : MM02.State}
    {L : Layout} : ∀ {ls : List Nat}, DecAlong ObR ObW s2 (readOps s2' L ls) →
      ∀ l ∈ ls, ObR.dec s2 (leafAcc s2' L .read l)
  | [], _, _, h => by cases h
  | _ :: _, ⟨h0, h⟩, _, hl => by
    rcases List.mem_cons.1 hl with rfl | hl
    · exact h0
    · exact decAlong_readOps h _ hl

/-- L4: the obligation of the contracts at a `free` of the run: `FreeCompat` is instantiated by
the token of the provider recorded by the ghost `provOf` (`FreeCompatInst`). -/
def FreeOblig (k : K) (C : Nat → Nat → Prop) (π : Params) : Op3 → (Nat → Option Nat) → Prop
  | .free p auth, pv => k.FreeCompat p auth → FreeCompatInst C π.ptok pv p auth
  | _, _ => True

/-- The obligations of one step of the run, on the states where it runs: the layout of the new
roots (`LayoutObl`, K1, K2), `dec` along its MM-02 sequence (K5), and `FreeOblig` (L4). -/
def Oblig (k : K) (C : Nat → Nat → Prop) (ObR : MM02.ReadOblSpec) (ObW : MM02.WriteOblSpec)
    (π : Params) (op : Op3) (s3 s3' : S3) (pv : Nat → Option Nat) (s2 : MM02.State) : Prop :=
  LayoutObl π op s3 s3' s2 ∧ DecAlong ObR ObW s2 (assoc π op s3 s2) ∧ FreeOblig k C π op pv

/-- An execution of MM-03 with its translation (`Trans`) whose every step meets its obligations
(`Oblig`), and whose initial run meets the layout of the statics and `dec`. The obligations bear on
the states of this execution and its run only. -/
inductive SimRun (k : K) (C : Nat → Nat → Prop) (ObR : MM02.ReadOblSpec)
    (ObW : MM02.WriteOblSpec) (statics : Statics) (π : Params) :
    List Op3 → S3 → (Nat → Option Nat) → List Op2 → MM02.State → Prop where
  | init : ShapeOK 0 (statics.map (·.1)) →
      NewLayout π.L (S3.init statics).P 0 0 π.geom (rootIdx (statics.map (·.1))) →
      DecAlong ObR ObW MM02.State.empty (initOpsOf π statics) →
      SimRun k C ObR ObW statics π [] (S3.init statics) (fun _ => none) (initOpsOf π statics)
        (exec MM02.State.empty (initOpsOf π statics))
  | step {ops : List Op3} {s3 s3' : S3} {pv : Nat → Option Nat} {os : List Op2}
      {s2 : MM02.State} {op : Op3} :
      SimRun k C ObR ObW statics π ops s3 pv os s2 → Step3 k op s3 s3' →
      Oblig k C ObR ObW π op s3 s3' pv s2 →
      SimRun k C ObR ObW statics π (op :: ops) s3' (provStep op s3 pv) (os ++ assoc π op s3 s2)
        (exec s2 (assoc π op s3 s2))

/-- A `SimRun` is the canonical translation of its execution. -/
theorem SimRun.trans {k : K} {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec}
    {ObW : MM02.WriteOblSpec} {statics : Statics} {π : Params} {ops : List Op3} {s3 : S3}
    {pv : Nat → Option Nat} {os : List Op2} {s2 : MM02.State}
    (h : SimRun k C ObR ObW statics π ops s3 pv os s2) : Trans k statics π ops s3 pv os s2 := by
  induction h with
  | init hsh _ _ => exact .init hsh
  | step _ hs _ ih => exact ih.step hs

/-- A `SimRun` is an execution of MM-03. -/
theorem SimRun.exec3 {k : K} {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec}
    {ObW : MM02.WriteOblSpec} {statics : Statics} {π : Params} {ops : List Op3} {s3 : S3}
    {pv : Nat → Option Nat} {os : List Op2} {s2 : MM02.State}
    (h : SimRun k C ObR ObW statics π ops s3 pv os s2) : Exec3 k statics ops s3 := by
  induction h with
  | init hsh _ _ => exact .init hsh
  | step _ hs _ ih => exact ih.step hs

/-- `simulation` (step 5): along every execution of MM-03 from `S3.init statics` within the
envelope of L1 and L2, translated with parameters `π` fixed once for the whole execution, whose
steps meet their obligations (`SimRun`), the MM-02 run starts with the run of `repr_init`, appends
at each step the sequence associated by K4 and L6, has only `ok` outcomes, reaches the state `s2`,
and is in `Repr` with the MM-03 state; the MM-03 state is reached, and the ghost `provOf` is empty
beyond the places. Since every prefix of a `SimRun` is a `SimRun`, this holds at each step. The
remaining hypotheses: `DDSound k` (L7: `ddSound_of_layout`); `stat` (K5); the obligation of the
placement and valid alignments (K2); the compatibility of the frame tokens (K2). `SameSizeAlong`
(L6) is not one: the outcomes and `Repr` hold without it; the copy of the bytes of a `transfer`
holds under it (`transfer_copies`). -/
theorem simulation {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec} {ObW : MM02.WriteOblSpec}
    {k : K} {statics : Statics} {π : Params} (hdd : DDSound k)
    (hstatR : ∀ s ac, ObR.stat s ac) (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hpl : PlacementOK π.pl) (hg : ∀ r, 0 < (π.geom r).align ∧ MM02.Pow2 (π.geom r).align)
    (htc : TokCompat C π.tok) :
    ∀ {ops s3 pv os s2}, SimRun k C ObR ObW statics π ops s3 pv os s2 →
      AllOk C ObR ObW MM02.State.empty os ∧ exec MM02.State.empty os = s2 ∧
      Repr π.tok π.ptok pv π.L s3 s2 ∧ Reachable k statics s3 ∧
      ∀ r, s3.P.length ≤ r → pv r = none := by
  intro ops s3 pv os s2 ht
  induction ht with
  | init hsh hlay0 hdec0 =>
    have := repr_init (C := C) (ObR := ObR) (ObW := ObW) (tok := π.tok) (ptok := π.ptok)
      (provOf := fun _ => none) hsh hpl (fun i _ => hg i) hlay0 (fun _ _ => rfl) hstatW hdec0
    exact ⟨this.1, rfl, this.2, .init hsh, fun _ _ => rfl⟩
  | @step ops s3 s3' pv os s2 op _ hs hob ih =>
    obtain ⟨hok, hex, hR, hr, hpv⟩ := ih
    obtain ⟨hly, hdc, hfc⟩ := hob
    have hwf := (reachable_invariants hdd hr).1
    have hnd := (reachable_invariants hdd hr).2.1.nd
    have hfl := (reachable_fpLeaves_frameOwnedLive hdd hr).1
    have hfo := (reachable_fpLeaves_frameOwnedLive hdd hr).2
    have hr' : Reachable k statics s3' := Reachable.ofStep hr hs.step
    -- the MM-02 side of the step
    have key : AllOk C ObR ObW s2 (assoc π op s3 s2) ∧
        Repr π.tok π.ptok (provStep op s3 pv) π.L s3' (exec s2 (assoc π op s3 s2)) := by
      cases op with
      | derive => exact r6_noStep (k := k) hR (.derive hs)
      | split => exact r6_noStep (k := k) hR (.split hs)
      | release => exact r6_noStep (k := k) hR (.release hs)
      | transfer => exact r6_transfer hwf hR hs hstatR hstatW hdc
      | depend => exact r6_noStep (k := k) hR (.depend hs)
      | enter ps ls =>
        exact r6_enter hwf hR hpl (fun i _ => hg _) hs.2 (fun i _ => hpv _ (Nat.le_add_right _ _))
          hly
      | exit => exact r6_exit hwf hfo hR htc hs
      | read => exact r6_read3 hwf hnd hfl hR hs hstatR (decAlong_readOps hdc)
      | write => exact r2_write3 hwf hnd hfl hR hs hstatW hdc
      | writeShared => exact r2_writeShared hwf hnd hfl hR hs hstatW hdc
      | pin => exact r6_noStep (k := k) hR (.pin hs)
      | unpin => exact r6_noStep (k := k) hR (.unpin hs)
      | endUse => exact r6_noStep (k := k) hR (.endUse hs)
      | free p auth => exact r6_free hwf hR hfc hs
      | alloc pr ow ls =>
        obtain ⟨⟨i, hone⟩, hs'⟩ := hs
        have hi : i < ls.length := (rootIdx_mem (k := 0) (by rw [hone]; rfl)).1
        have hR₁ : Repr π.tok π.ptok (provStep (.alloc pr ow ls) s3 pv) π.L s3 s2 :=
          ⟨hR.toReprB.provOf_congr fun r hr => by
            simp only [provStep, show ¬ (s3.P.length ≤ r ∧ r < s3.P.length + ls.length) from
              fun h => absurd h.1 (Nat.not_le.2 hr), ↓reduceIte], hR.wf2⟩
        have := r6_alloc (C := C) (ObR := ObR) (ObW := ObW) (pl := π.pl)
          (g := fun i => π.geom (s3.P.length + i)) (i := i) hwf hR₁ hpl (hg _) hs' hone
          (by simp only [provStep, show s3.P.length ≤ s3.P.length + i ∧
              s3.P.length + i < s3.P.length + ls.length from ⟨Nat.le_add_right _ _, by omega⟩,
              and_self, ↓reduceIte])
          (by simp only [LayoutObl] at hly; rw [hone] at hly; exact hly)
        simp only [assoc, hone]
        exact this
      | newArena => exact r6_noStep (k := k) hR (.newArena hs)
      | issue => exact (r6_issue hwf hR hs hstatW hdc.1).imp id fun h => h.1
      | reset => exact r6_noStep (k := k) hR (.reset hs)
      | store => exact (r6_store hwf hR hs hstatW hdc.1).imp id fun h => h.1
    refine ⟨along_append.2 ⟨hok, hex ▸ key.1⟩, by rw [exec_append, hex], key.2, hr', fun r hr => ?_⟩
    have hlen := (step_extends hwf hs.step).1
    cases op with
    | alloc pr ow ls =>
      have hP : s3'.P.length = s3.P.length + ls.length := by
        obtain ⟨-, hs'⟩ := hs
        cases hs' with
        | ok _ _ => exact allocP_len s3 ow ls
      simp only [provStep, show ¬ (s3.P.length ≤ r ∧ r < s3.P.length + ls.length) from
        fun h => by omega, ↓reduceIte]
      exact hpv r (by omega)
    | _ => exact hpv r (by omega)

/-- L8 along the simulation: at every step of a `SimRun`, a leaf pinned before the step has a live
allocation before and after it, and the same address. -/
theorem simulation_pinned {C : Nat → Nat → Prop} {ObR : MM02.ReadOblSpec}
    {ObW : MM02.WriteOblSpec} {k : K} {statics : Statics} {π : Params} (hdd : DDSound k)
    (hstatR : ∀ s ac, ObR.stat s ac) (hstatW : ∀ s ac w, ObW.stat s ac w)
    (hpl : PlacementOK π.pl) (hg : ∀ r, 0 < (π.geom r).align ∧ MM02.Pow2 (π.geom r).align)
    (htc : TokCompat C π.tok) {ops : List Op3} {s3 s3' : S3} {pv : Nat → Option Nat}
    {os : List Op2} {s2 : MM02.State} {op : Op3}
    (ht : SimRun k C ObR ObW statics π ops s3 pv os s2) (hs : Step3 k op s3 s3')
    (hob : Oblig k C ObR ObW π op s3 s3' pv s2) {l : Nat} (hl : l < s3.P.length)
    (hlf : isLeaf s3.P l) (hpin : s3.pin l = true ∨ k.Pinned l) :
    LiveAlloc s2 (π.L l).alloc ∧ LiveAlloc (exec s2 (assoc π op s3 s2)) (π.L l).alloc ∧
      leafAddr (exec s2 (assoc π op s3 s2)) π.L l = leafAddr s2 π.L l := by
  have h₁ := simulation hdd hstatR hstatW hpl hg htc ht
  have h₂ := simulation hdd hstatR hstatW hpl hg htc (ht.step hs hob)
  exact pinned_address_stable hdd h₁.2.2.2.1 hs.step h₁.2.2.1 h₂.2.2.1 hl hlf hpin

/-! ## Cases (step 6 of the task)

Each verdict is checked by `decide` on the precondition of the MM-03 step and on `Repr`, which is
decidable; the MM-02 sequences are exhibited by the definitions `opsN` and their effects. Each
refinement theorem is applied to a step of one scenario reached from `S3.init`. The obligations `dec` of the
test cases ask an access aligned on 4 bytes, a non-trivial instance (K5); `stat` is `True`, as K5
fixes for the sequential fragment. -/

namespace CaseInit

/-- One static leaf, declared `Init`, in a 4-byte range of the static allocation. -/
def st : Statics := [((none, none, 0), true)]
def L : Layout := fun _ => ⟨0, 0, 4⟩
def tk : Nat → Nat := fun f => 100 + f
/-- Provider tokens (L4) and the ghost `provOf`: no root is allocated by `alloc`. -/
def ptk : Nat → Nat := fun pr => 6 + pr
def prov : Nat → Option Nat := fun _ => none
def g : Nat → Geom := fun _ => ⟨0, 4, 4⟩
def w : Nat → Nat → UInt8 × Option Nat := fun l i => ((l + i).toUInt8, none)
/-- Test obligations (K5): `dec`, an access aligned on 4 bytes; `stat`, true. -/
def obR : MM02.ReadOblSpec := ⟨fun _ ac => ac.addr % 4 = 0, fun _ _ => True⟩
def obW : MM02.WriteOblSpec := ⟨fun _ ac _ => ac.addr % 4 = 0, fun _ _ _ => True⟩
instance : ∀ s o, Decidable (Op2.Dec obR obW s o) := fun s o => by
  cases o <;> simp only [Op2.Dec, obR, obW] <;> infer_instance
def s2 : MM02.State := exec MM02.State.empty (initOps topPlacement g tk L w st)

/-- `repr_init` on the static storage, and the same verdict by `decide`; without the write of the
static, `Repr` fails (K3: an `Init` leaf has its bytes initialised). -/
example : ReprB tk ptk prov L (S3.init st) s2 :=
  (repr_init (C := fun _ _ => False) (ObR := obR) (ObW := obW) (by decide) topPlacement_ok
    (by decide) (by decide) (by decide) (fun _ _ _ => trivial) (by decide)).2.toReprB
example : ReprB tk ptk prov L (S3.init st) s2 := by decide
example : ¬ ReprB tk ptk prov L (S3.init st)
    (exec MM02.State.empty (allocOps topPlacement g (some (tk 0)) MM02.State.empty [0])) := by
  decide

/-- Counterexample kept (report, (f)): the draft `canRead3` does not ask the leaves read to be
usable (MM-03.3 O9.1). In a state outside the reached ones, where the static 0 is freed but its
root authority stays active, `read3` is `ok`, `Repr` holds, and the MM-02 read is `ub`: R1 needs
`NoDangling`. -/
def cx : S3 := { S3.init st with dead := fun _ => true, freed := fun _ => true }
def cx2 : MM02.State := s2.dealloc 0
example : ReprB tk ptk prov L cx cx2 := by decide
example : Read3Step 0 [0] cx (.ok cx) := .ok (by decide)
example : MM02.ReadStep obR (leafAcc cx2 L .read 0) cx2 .ub :=
  .ub fun ⟨h, _⟩ => absurd h (by decide)
example : ¬ NoDangling cx := fun h => h 0 _ rfl rfl 0 (by decide) 0 (by decide) (by decide)

end CaseInit

namespace Cases

/-- Test contracts: leaf 5 `SharedMutable`; `ExternalDone` for 2; place 6 deallocable with the
authority 7; the allocator at place 1 satisfiable, any other not. -/
def KC : K := ⟨fun _ _ => False, (· ∈ [5]), (· ∈ ([] : List Nat)), (· ∈ [2]), (· ∈ [6]),
  fun p a => (p, a) ∈ [(6, 7)], fun pr _ _ => pr = 1⟩
instance : ∀ r r', Decidable (KC.DeclaredDisjoint r r') := fun _ _ => instDecidableFalse
instance : DecidablePred KC.SharedMutable := fun l => inferInstanceAs (Decidable (l ∈ [5]))
instance : DecidablePred KC.Pinned := fun l => inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : DecidablePred KC.ExternalDone := fun l => inferInstanceAs (Decidable (l ∈ [2]))
instance : DecidablePred KC.Deallocable := fun p => inferInstanceAs (Decidable (p ∈ [6]))
instance : ∀ p a, Decidable (KC.FreeCompat p a) :=
  fun p a => inferInstanceAs (Decidable ((p, a) ∈ [(6, 7)]))
instance : ∀ p ls s, Decidable (KC.Satisfiable p ls s) :=
  fun p _ _ => inferInstanceAs (Decidable (p = 1))
theorem kc_dd : DDSound KC := fun _ _ h => h.elim

/-- The scenario. Static 0 (`Init`). Frame 1 with locals 1 (an allocator value), 2 (owner of
allocated storage, then arena value) and 3, a value with fields 4 and 5. Then: writes of 1 and 2,
read of 1, `derive` of 4 from the root of 3 and its `release`, `split` of 3 into 4 and 5, `write3`
of 4, `writeShared` of 5, `depend` of 2 on the root of 1, `pin` and `unpin` of 2, `alloc` of the
storage 6 owned by 2 (`fail` from the allocator 2), `newArena` on 6, `reset`, `endUse` of 2 (6
dies, not freed), `exitFrame`. On a branch, `free` of 6 after its allocation. -/
def st : Statics := [((none, none, 0), true)]
def lsF : List (Option Nat × Option Nat × Nat) :=
  [(none, none, 0), (none, none, 0), (none, none, 0), (some 3, none, 0), (some 3, none, 0)]
def e0 : S3 := S3.init st
def e1 : S3 := enterEff e0 [] lsF
def e2 : S3 := write3Eff e1 [1]
def e3 : S3 := write3Eff e2 [2]
def e4 : S3 := deriveEff e3 3 4 .observe
def e5 : S3 := releaseEff e4 4
def e6 : S3 := splitEff e5 3 [[4], [5]]
def e7 : S3 := write3Eff e6 [4]
def e8 : S3 := write3Eff e7 [5]
def e9 : S3 := dependEff e8 2 1
def e10 : S3 := pinEff e9 2 true
def e11 : S3 := pinEff e10 2 false
def e12 : S3 := allocEff e11 1 2 [(none, none, 0)]
def e13 : S3 := newArenaEff e12 6 7
def e14 : S3 := resetAtEff e13 0
def e15 : S3 := endUseEff e14 2
def e16 : S3 := exitEff e15
def f13 : S3 := freeEff e12 6

theorem r0 : Reachable KC st e0 := .init (by decide)
theorem r1 : Reachable KC st e1 := .enter r0 (.ok (by decide))
theorem r2 : Reachable KC st e2 := .write r1 (.ok (by decide) : Write3Step 1 [1] e1 (.ok e2))
theorem r3 : Reachable KC st e3 := .write r2 (.ok (by decide) : Write3Step 2 [2] e2 (.ok e3))
theorem r4 : Reachable KC st e4 := .derive r3 (.ok (by decide) : DeriveStep 3 4 .observe e3 (.ok e4))
theorem r5 : Reachable KC st e5 := .release r4 (.ok (by decide) : ReleaseStep 4 e4 (.ok e5))
theorem r6 : Reachable KC st e6 := .split r5 (.ok (by decide) : SplitStep KC 3 [[4], [5]] e5 (.ok e6))
theorem r7 : Reachable KC st e7 := .write r6 (.ok (by decide) : Write3Step 5 [4] e6 (.ok e7))
theorem r8 : Reachable KC st e8 :=
  .writeShared r7 (.ok (by decide) : WriteSharedStep KC 6 [5] e7 (.ok e8))
theorem r9 : Reachable KC st e9 := .depend r8 (.ok (by decide) : DependStep 2 1 e8 (.ok e9))
theorem r10 : Reachable KC st e10 := .pin r9 (.ok (by decide) : PinStep 2 e9 (.ok e10))
theorem r11 : Reachable KC st e11 := .unpin r10 (.ok (by decide) : UnpinStep KC 2 e10 (.ok e11))
theorem r12 : Reachable KC st e12 :=
  .alloc r11 (.ok (by decide) (by decide) : AllocStep KC 1 2 [(none, none, 0)] e11 (.ok e12))
theorem r13 : Reachable KC st e13 := .newArena r12 (.ok (by decide) : NewArenaStep 6 7 e12 (.ok e13))
theorem r14 : Reachable KC st e14 := .reset r13 (.ok (by decide) : ResetAtStep KC 0 2 e13 (.ok e14))
theorem r15 : Reachable KC st e15 := .endUse r14 (.ok (by decide) : EndUseStep KC 2 e14 (.ok e15))
theorem r16 : Reachable KC st e16 := .exit r15 (.ok (by decide) : ExitStep KC e15 (.ok e16))
theorem rf : Reachable KC st f13 := .free r12 (.ok (by decide) : FreeStep KC 6 7 e12 (.ok f13))

/-- MM-02 parameters: compatibility by equality of tokens (so `TokCompat`); frame token `100 + f`;
geometry: 8 bytes aligned on 4; layout: one allocation per root, fields 4 and 5 at offsets 0 and 4
of the allocation of 3; the bytes written in leaf `l` are `10 l + i`. -/
def C : Nat → Nat → Prop := fun a d => a = d
def tk : Nat → Nat := fun f => 100 + f
/-- Provider tokens (L4): the allocator at place 1 has the token 7. Ghost `provOf`: the places 6
and 7 are allocated from the provider 1. -/
def ptk : Nat → Nat := fun pr => 6 + pr
def prov : Nat → Option Nat := fun r => if r = 6 ∨ r = 7 then some 1 else none
def g : Nat → Geom := fun _ => ⟨0, 8, 4⟩
def L : Layout := fun q => match q with
  | 0 => ⟨0, 0, 4⟩ | 1 => ⟨1, 0, 4⟩ | 2 => ⟨2, 0, 4⟩ | 3 => ⟨3, 0, 8⟩
  | 4 => ⟨3, 0, 4⟩ | 5 => ⟨3, 4, 4⟩ | 6 => ⟨4, 0, 4⟩ | _ => ⟨99, 0, 0⟩
def w : Nat → Nat → UInt8 × Option Nat := fun l i => ((10 * l + i).toUInt8, none)
/-- Test obligations (K5): `dec`, an access aligned on 4 bytes; `stat`, true. -/
def obR : MM02.ReadOblSpec := ⟨fun _ ac => ac.addr % 4 = 0, fun _ _ => True⟩
def obW : MM02.WriteOblSpec := ⟨fun _ ac _ => ac.addr % 4 = 0, fun _ _ _ => True⟩
instance : ∀ s o, Decidable (Op2.Dec obR obW s o) := fun s o => by
  cases o <;> simp only [Op2.Dec, obR, obW] <;> infer_instance

/-- The MM-02 sequences attached to the steps (K4) and the states they reach. -/
def m0 : MM02.State := exec MM02.State.empty (initOps topPlacement g tk L w st)
def ops1 : List Op2 := allocOps topPlacement g (some (tk e0.nF)) m0 (rootIdx lsF)
def m1 : MM02.State := exec m0 ops1
def ops2 : List Op2 := writeOps m1 L w [1]
def m2 : MM02.State := exec m1 ops2
def ops3 : List Op2 := writeOps m2 L w [2]
def m3 : MM02.State := exec m2 ops3
def ops7 : List Op2 := writeOps m3 L w [4]
def m7 : MM02.State := exec m3 ops7
def ops8 : List Op2 := writeOps m7 L w [5]
def m8 : MM02.State := exec m7 ops8
def ops12 : List Op2 :=
  [.alloc (g 0).space (topPlacement m8 (g 0)) (g 0).size (g 0).align (some 7)]
def m12 : MM02.State := exec m8 ops12
def ops16 : List Op2 := exitOps L tk e15
def m16 : MM02.State := exec m12 ops16
def opsF : List Op2 := deallocOps [rootAlloc L e12.P 6] 7
def mF : MM02.State := exec m12 opsF

theorem wf_m0 : MM02.WF m0 := exec_wf _ _ fun _ _ => rfl
theorem wf_m1 : MM02.WF m1 := exec_wf _ _ wf_m0
theorem wf_m2 : MM02.WF m2 := exec_wf _ _ wf_m1
theorem wf_m3 : MM02.WF m3 := exec_wf _ _ wf_m2
theorem wf_m7 : MM02.WF m7 := exec_wf _ _ wf_m3
theorem wf_m8 : MM02.WF m8 := exec_wf _ _ wf_m7
theorem wf_m12 : MM02.WF m12 := exec_wf _ _ wf_m8
theorem wf_m16 : MM02.WF m16 := exec_wf _ _ wf_m12
theorem wf_mF : MM02.WF mF := exec_wf _ _ wf_m12

/-- The sequences exhibited: the bases chosen by `topPlacement` for the locals (16, 28, 40) and the
allocated storage (52), with their tokens; the deallocations of `exitFrame`, of the allocations 1,
2, 3 of the roots owned by frame 1, with its token 101. -/
example : (m1.allocs 1).map (·.base) = some 16 ∧ (m1.allocs 2).map (·.base) = some 28 ∧
    (m1.allocs 3).map (·.base) = some 40 ∧ (m1.allocs 3).map (·.freeAuth) = some (some 101) := by
  decide
example : (m12.allocs 4).map (·.base) = some 52 ∧ (m12.allocs 4).map (·.live) = some true ∧
    (m12.allocs 4).map (·.freeAuth) = some (some 7) := by decide
example : (frameRoots e15 e15.top).map (rootAlloc L e15.P) = [1, 2, 3] ∧ tk e15.top = 101 := by
  decide

/-- `Repr` at each point, by `decide`. -/
example : ReprB tk ptk prov L e0 m0 ∧ ReprB tk ptk prov L e1 m1 ∧ ReprB tk ptk prov L e2 m2 ∧ ReprB tk ptk prov L e3 m3 ∧
    ReprB tk ptk prov L e6 m3 ∧ ReprB tk ptk prov L e8 m8 ∧ ReprB tk ptk prov L e12 m12 ∧ ReprB tk ptk prov L e15 m12 ∧
    ReprB tk ptk prov L e16 m16 ∧ ReprB tk ptk prov L f13 mF := by decide

/-- K3: initial state (`repr_init`). -/
example : AllOk C obR obW MM02.State.empty (initOps topPlacement g tk L w st) ∧
    Repr tk ptk prov L e0 m0 :=
  repr_init (by decide) topPlacement_ok (by decide) (by decide) (by decide) (fun _ _ _ => trivial)
    (by decide)
/-- R6, `enterFrame`: three allocations, one per root local. -/
example : AllOk C obR obW m0 ops1 ∧ Repr tk ptk prov L e1 m1 :=
  r6_enter (reachable_invariants kc_dd r0).1 ⟨by decide, wf_m0⟩ topPlacement_ok (by decide)
    (.ok (by decide)) (by decide) (by decide)
/-- R2, `write3`. -/
example : AllOk C obR obW m1 ops2 ∧ Repr tk ptk prov L e2 m2 :=
  r2_write3_reachable kc_dd r1 ⟨by decide, wf_m1⟩ (.ok (by decide) : Write3Step 1 [1] e1 (.ok e2))
    (fun _ _ _ => trivial) (by decide)
example : AllOk C obR obW m2 ops3 ∧ Repr tk ptk prov L e3 m3 :=
  r2_write3_reachable kc_dd r2 ⟨by decide, wf_m2⟩ (.ok (by decide) : Write3Step 2 [2] e2 (.ok e3))
    (fun _ _ _ => trivial) (by decide)
example : AllOk C obR obW m3 ops7 ∧ Repr tk ptk prov L e7 m7 :=
  r2_write3_reachable kc_dd r6 ⟨by decide, wf_m3⟩ (.ok (by decide) : Write3Step 5 [4] e6 (.ok e7))
    (fun _ _ _ => trivial) (by decide)
/-- R2, `writeShared` under an authority of effective mode present. -/
example : AllOk C obR obW m7 ops8 ∧ Repr tk ptk prov L e8 m8 :=
  r2_writeShared_reachable kc_dd r7 ⟨by decide, wf_m7⟩
    (.ok (by decide) : WriteSharedStep KC 6 [5] e7 (.ok e8)) (fun _ _ _ => trivial) (by decide)
/-- R1 and R6, `read3`; the value read is the 4 bytes written by `write3` in leaf 1. -/
example : AllOk C obR obW m3 (readOps m3 L [1]) ∧
    Repr tk ptk prov L e3 (exec m3 (readOps m3 L [1])) :=
  r6_read3 (reachable_invariants kc_dd r3).1 (reachable_invariants kc_dd r3).2.1.nd
    (reachable_fpLeaves_frameOwnedLive kc_dd r3).1 ⟨by decide, wf_m3⟩
    (.ok (by decide) : Read3Step 1 [1] e3 (.ok e3)) (fun _ _ => trivial) (fun l hl => by
      rw [List.mem_singleton] at hl; subst hl; show (leafAcc m3 L .read 1).addr % 4 = 0; decide)
example : ((m3.allocs 1).map fun a => a.bytesAt 0 4) =
    some [.init 10 none, .init 11 none, .init 12 none, .init 13 none] := by decide
example : ((m8.allocs 3).map fun a => a.bytesAt 0 8) = some [.init 40 none, .init 41 none,
    .init 42 none, .init 43 none, .init 50 none, .init 51 none, .init 52 none, .init 53 none] := by
  decide
/-- R6, `alloc` `ok`: one allocation, at base 52, token 7. -/
example : AllOk C obR obW m8 ops12 ∧ Repr tk ptk prov L e12 m12 :=
  r6_alloc (i := 0) (ptok := ptk) (provOf := prov) (pr := 1) (reachable_invariants kc_dd r11).1
    ⟨by decide, wf_m8⟩ topPlacement_ok
    (by decide) (.ok (by decide) (by decide) : AllocStep KC 1 2 [(none, none, 0)] e11 (.ok e12)) rfl
    (by decide) (by decide)
/-- R6, `alloc` `fail`: allocator 2 not satisfiable, no step. -/
example : AllOk C obR obW m12 [] ∧ Repr tk ptk prov L e12 (exec m12 []) :=
  r6_alloc_fail ⟨by decide, wf_m12⟩
    (.fail (by decide) (by decide) : AllocStep KC 2 2 [(none, none, 0)] e12 (.fail e12))
/-- R6, `free` of 6 with the authority 7: the allocation 4 dies. -/
example : AllOk C obR obW m12 opsF ∧ Repr tk ptk prov L f13 mF :=
  r6_free (k := KC) (auth := 7) (reachable_invariants kc_dd r12).1 ⟨by decide, wf_m12⟩
    (fun _ => ⟨1, rfl, rfl⟩) (.ok (by decide))
example : DeadAlloc mF 4 := by decide
/-- R6, `exitFrame`: three deallocations; the storage 6, dead by `endUse` and not freed, keeps
its allocation 4 live (leak, K3, K4). -/
example : AllOk C obR obW m12 ops16 ∧ Repr tk ptk prov L e16 m16 :=
  r6_exit_reachable kc_dd r15 ⟨by decide, wf_m12⟩ (fun _ => rfl) (.ok (by decide))
example : DeadAlloc m16 1 ∧ DeadAlloc m16 2 ∧ DeadAlloc m16 3 ∧ LiveAlloc m16 4 ∧
    LiveAlloc m16 0 := by decide
/-- R6, the steps without MM-02 step (K4). After `endUse` of 2, the storage 6 is not usable and
not freed, and its allocation stays live. -/
example : AllOk C obR obW m3 [] ∧ Repr tk ptk prov L e4 (exec m3 []) :=
  r6_noStep (k := KC) ⟨by decide, wf_m3⟩ (.derive (.ok (by decide) : DeriveStep 3 4 .observe e3 (.ok e4)))
example : AllOk C obR obW m3 [] ∧ Repr tk ptk prov L e5 (exec m3 []) :=
  r6_noStep (k := KC) ⟨by decide, wf_m3⟩ (.release (.ok (by decide) : ReleaseStep 4 e4 (.ok e5)))
example : AllOk C obR obW m3 [] ∧ Repr tk ptk prov L e6 (exec m3 []) :=
  r6_noStep ⟨by decide, wf_m3⟩ (.split (.ok (by decide) : SplitStep KC 3 [[4], [5]] e5 (.ok e6)))
example : AllOk C obR obW m8 [] ∧ Repr tk ptk prov L e9 (exec m8 []) :=
  r6_noStep (k := KC) ⟨by decide, wf_m8⟩ (.depend (.ok (by decide) : DependStep 2 1 e8 (.ok e9)))
example : AllOk C obR obW m8 [] ∧ Repr tk ptk prov L e10 (exec m8 []) :=
  r6_noStep (k := KC) ⟨by decide, wf_m8⟩ (.pin (.ok (by decide) : PinStep 2 e9 (.ok e10)))
example : AllOk C obR obW m8 [] ∧ Repr tk ptk prov L e11 (exec m8 []) :=
  r6_noStep ⟨by decide, wf_m8⟩ (.unpin (.ok (by decide) : UnpinStep KC 2 e10 (.ok e11)))
example : AllOk C obR obW m12 [] ∧ Repr tk ptk prov L e13 (exec m12 []) :=
  r6_noStep (k := KC) ⟨by decide, wf_m12⟩ (.newArena (.ok (by decide) : NewArenaStep 6 7 e12 (.ok e13)))
example : AllOk C obR obW m12 [] ∧ Repr tk ptk prov L e14 (exec m12 []) :=
  r6_noStep ⟨by decide, wf_m12⟩ (.reset (.ok (by decide) : ResetAtStep KC 0 2 e13 (.ok e14)))
example : AllOk C obR obW m12 [] ∧ Repr tk ptk prov L e15 (exec m12 []) :=
  r6_noStep ⟨by decide, wf_m12⟩ (.endUse (.ok (by decide) : EndUseStep KC 2 e14 (.ok e15)))
example : ¬ e15.Usable 6 ∧ e15.freed 6 = false ∧ LiveAlloc m12 4 := by decide

/-- R4 on the reached state after `exitFrame`: the authorities still active cover only the
static leaf, in a live allocation. -/
example : ∀ j < e16.A.length, e16.Active j → e16.afp j = [0] := by decide
example : LiveAlloc m16 (L 0).alloc :=
  (r4_no_dead_cover (tok := tk) (ptok := ptk) (provOf := prov) kc_dd r16 ⟨by decide, wf_m16⟩ 0 _
    rfl rfl 0
    (List.mem_singleton_self _)).2.2

/-- `exclusive_bytes`: after `split`, authority 5 has effective `Modify` on leaf 4; the root 3,
active and covering 4, has no effective mode there; authority 6 keeps effective `Modify` on the
adjacent range of leaf 5. A layout where the ranges of 4 and 5 overlap violates `LayoutWF`. -/
example : effective e6 5 4 = some .modify ∧ e6.Active 3 ∧ 4 ∈ e6.afp 3 ∧
    effective e6 6 5 = some .modify := by decide
example : effective e6 3 4 = none :=
  exclusive_bytes (L := L) (s2 := m3) (by decide) (reachable_invariants kc_dd r6).2.1.base.1
    (l := 4) (l' := 4) (by decide) (by decide) (by decide) (by decide) (a := 5) (by decide)
    (by decide) rfl (by decide)
def Lov : Layout := fun q => if q = 5 then ⟨3, 2, 4⟩ else L q
example : ¬ LayoutWF Lov e6 m3 := by decide

/-- K1 (d): the storage 6, a shape of one leaf, may have size zero. -/
def L0 : Layout := fun q => if q = 6 then ⟨4, 0, 0⟩ else L q
def m12z : MM02.State := exec m8 [.alloc 0 (topPlacement m8 ⟨0, 0, 4⟩) 0 4 (some 7)]
example : ReprB tk ptk prov L0 e12 m12z := by decide

/-- Each clause of `Repr` rejects a wrong MM-02 state: a usable root with a dead allocation; a
leaked root deallocated at `endUse`; two roots in one allocation (`LayoutWF` holds); a wrong frame
token; an exited root or a freed root whose allocation is still live. -/
example : ¬ ReprB tk ptk prov L e3 (m3.dealloc 1) := by decide
example : ¬ ReprB tk ptk prov L e15 (m12.dealloc 4) := by decide
def Lsh : Layout := fun q => if q = 2 then ⟨1, 4, 4⟩ else L q
example : LayoutWF Lsh e1 m1 ∧ ¬ ReprB tk ptk prov Lsh e1 m1 := by decide
example : ¬ ReprB (fun f => 200 + f) ptk prov L e1 m1 := by decide
example : ¬ ReprB tk ptk prov L e16 m12 ∧ ¬ ReprB tk ptk prov L f13 m12 := by decide

/-- Counterexample kept (report, (e), (f)): the draft accepts `alloc` of a shape with two roots,
where O14 creates one root; with the one `AllocStep` of K4, a layout putting both roots in the
fresh allocation satisfies `LayoutWF` but not `Repr` (two roots, one allocation). -/
def e12b : S3 := allocEff e11 1 2 [(none, none, 0), (none, none, 0)]
example : AllocStep KC 1 2 [(none, none, 0), (none, none, 0)] e11 (.ok e12b) :=
  .ok (by decide) (by decide)
def L2 : Layout := fun q => if q = 7 then ⟨4, 4, 4⟩ else L q
def m12b : MM02.State := exec m8 [.alloc 0 (topPlacement m8 (g 0)) 8 4 (some 7)]
example : LayoutWF L2 e12b m12b ∧ ¬ ReprB tk ptk prov L2 e12b m12b := by decide

/-- Witness of question (e) 7 of the report: the storage 7, allocated with owner the storage 6,
dies with the `free` of 6 (O13); `free` has one `DeallocStep`, of the allocation 4 of 6, and the
allocation 5 of 7 stays live; deallocating it too breaks `Repr` (clause `leaked`). -/
def ao13 : S3 := allocEff e12 1 6 [(none, none, 0)]
def af14 : S3 := freeEff ao13 6
theorem ra13 : Reachable KC st ao13 :=
  .alloc r12 (.ok (by decide) (by decide) : AllocStep KC 1 6 [(none, none, 0)] e12 (.ok ao13))
theorem ra14 : Reachable KC st af14 := .free ra13 (.ok (by decide) : FreeStep KC 6 7 ao13 (.ok af14))
def La : Layout := fun q => if q = 7 then ⟨5, 0, 4⟩ else L q
def na13 : MM02.State := exec m12 [.alloc 0 (topPlacement m12 (g 0)) 8 4 (some 7)]
def na14 : MM02.State := exec na13 (deallocOps [rootAlloc La ao13.P 6] 7)
example : ReprB tk ptk prov La ao13 na13 ∧ ReprB tk ptk prov La af14 na14 := by decide
example : ¬ af14.Usable 7 ∧ af14.freed 7 = false ∧ LiveAlloc na14 5 ∧ DeadAlloc na14 4 := by decide
example : ¬ ReprB tk ptk prov La af14 (na14.dealloc 5) := by decide

/-- Clauses K1 (a) and (c) reject a layout on their own among the clauses of `LayoutWF`: the field
5 of 3 in a fresh allocation 4 (with the token of frame 1) other than the allocation 3 of the field
4 breaks (a) only; the range of leaf 1 past the size of its allocation breaks (c) only. -/
def m3x : MM02.State := exec m3 [.alloc 0 (topPlacement m3 (g 0)) 8 4 (some (tk 1))]
def Lsa : Layout := fun q => if q = 5 then ⟨4, 0, 4⟩ else L q
example : ¬ (∀ r < e6.P.length, RootPlace e6.P r → ∀ l ∈ footprint e6.P r,
    ∀ l' ∈ footprint e6.P r, (Lsa l).alloc = (Lsa l').alloc) := by decide
set_option synthInstance.maxSize 512 in
example : (∀ l < e6.P.length, ∀ l' < e6.P.length, isLeaf e6.P l → isLeaf e6.P l' → l ≠ l' →
    (Lsa l).alloc = (Lsa l').alloc →
      MM02.RangeDisjoint (Lsa l).off (Lsa l).len (Lsa l').off (Lsa l').len) ∧
    (∀ l < e6.P.length, isLeaf e6.P l →
      AllocP m3x (Lsa l).alloc fun a => (Lsa l).off + (Lsa l).len ≤ a.size) := by decide
def Lwi : Layout := fun q => if q = 1 then ⟨1, 6, 4⟩ else L q
example : ¬ (∀ l < e1.P.length, isLeaf e1.P l →
    AllocP m1 (Lwi l).alloc fun a => (Lwi l).off + (Lwi l).len ≤ a.size) := by decide
set_option synthInstance.maxSize 512 in
example : (∀ r < e1.P.length, RootPlace e1.P r → ∀ l ∈ footprint e1.P r,
      ∀ l' ∈ footprint e1.P r, (Lwi l).alloc = (Lwi l').alloc) ∧
    (∀ l < e1.P.length, ∀ l' < e1.P.length, isLeaf e1.P l → isLeaf e1.P l' → l ≠ l' →
      (Lwi l).alloc = (Lwi l').alloc →
        MM02.RangeDisjoint (Lwi l).off (Lwi l).len (Lwi l').off (Lwi l').len) := by decide

/-- R1 applied directly to the read of leaf 1 in `e3`: an allocation, the range initialised, a
read of outcome `ok` with the bytes of the range, never `ub`. -/
example : ∃ al, m3.allocs (L 1).alloc = some al ∧ al.InitRange (L 1).off (L 1).len ∧
    MM02.ReadStep obR (leafAcc m3 L .read 1) m3 (.ok (al.bytesAt (L 1).off (L 1).len)) ∧
    ¬ MM02.ReadStep obR (leafAcc m3 L .read 1) m3 .ub :=
  r1_read3 (tok := tk) (reachable_invariants kc_dd r3).1 (reachable_invariants kc_dd r3).2.1.nd
    (reachable_fpLeaves_frameOwnedLive kc_dd r3).1 (ptok := ptk) (provOf := prov) ⟨by decide, wf_m3⟩
    (.ok (by decide) : Read3Step 1 [1] e3 (.ok e3)) (fun _ _ => trivial) (fun l hl => by
      rw [List.mem_singleton] at hl; subst hl; show (leafAcc m3 L .read 1).addr % 4 = 0; decide)
    1 (List.mem_singleton_self _)

/-- Gap kept (report, (f) 4): after `free` of 6, the storage 7 it owns stops being usable but is
not marked dead, where O13 marks dead "le stockage qui cesse de vivre". -/
example : af14.dead 7 = false ∧ ¬ af14.Usable 7 := by decide

/-- Owned storage that dies with its frame (K4: no `DeallocStep` for it): `exitFrame` directly from
`e12`, where the storage 6 is owned by the local 2; the allocations 1, 2, 3 die, the allocation 4 of
6 stays live, as the clause `leaked` asks; deallocating it too breaks `Repr` (report, (c) 4). -/
def eX : S3 := exitEff e12
theorem rX : Reachable KC st eX := .exit r12 (.ok (by decide) : ExitStep KC e12 (.ok eX))
example : AllOk C obR obW m12 (exitOps L tk e12) ∧
    Repr tk ptk prov L eX (exec m12 (exitOps L tk e12)) :=
  r6_exit_reachable kc_dd r12 ⟨by decide, wf_m12⟩ (fun _ => rfl) (.ok (by decide))
example : ¬ eX.Usable 6 ∧ eX.dead 6 = false ∧ LiveAlloc (exec m12 (exitOps L tk e12)) 4 ∧
    DeadAlloc (exec m12 (exitOps L tk e12)) 2 := by decide
example : ¬ ReprB tk ptk prov L eX ((exec m12 (exitOps L tk e12)).dealloc 4) := by decide

/-- L4: the clause `provTokens` rejects a wrong provider token: the allocation 4 of the storage 6,
allocated from the provider 1, has the token `ptk 1 = 7`, not `9 + 1`; before the `alloc`, the
ghost already maps 6 to the provider 1 and nothing is required (6 does not exist yet). -/
example : ¬ ReprB tk (fun pr => 9 + pr) prov L e12 m12 := by decide
example : ReprB tk (fun pr => 9 + pr) prov L e11 m8 ∧ e11.P.length = 6 := by decide

end Cases

namespace CaseOwnedLocal

/-- Witness of question (e) 1 of the report: frame 1 with a local 0 and a local 1 owned by the
local 0 (an element of the shape with an owning element). Local 1 is a root local (K4: one
`AllocStep` at the entry, with the token of the frame, K2) and owned storage (O13: `OwnedRoot`, so
`free` applies to it). `exitFrame` deallocates the allocations of the roots owned by the frame
only: after `free` of 1, a second deallocation of its allocation would be `ub` (MM-02.D); without
`free`, its allocation stays live after the exit. -/
abbrev KO : K := KT [] [] [] [1] [(1, 101)]
def lsO : List (Option Nat × Option Nat × Nat) := [(none, none, 0), (none, some 0, 0)]
def o0 : S3 := S3.init []
def o1 : S3 := enterEff o0 [] lsO
def o2 : S3 := freeEff o1 1
def o3 : S3 := exitEff o2
def o3' : S3 := exitEff o1
example : EnterStep [] lsO o0 (.ok o1) := .ok (by decide)
example : FreeStep KO 1 101 o1 (.ok o2) := .ok (by decide)
example : ExitStep KO o2 (.ok o3) := .ok (by decide)
example : ExitStep KO o1 (.ok o3') := .ok (by decide)
def C : Nat → Nat → Prop := fun a d => a = d
instance : DecidableRel C := fun a d => inferInstanceAs (Decidable (a = d))
def tk : Nat → Nat := fun f => 100 + f
def ptk : Nat → Nat := fun pr => 6 + pr
def prov : Nat → Option Nat := fun _ => none
def g : Nat → Geom := fun _ => ⟨0, 4, 4⟩
def L : Layout := fun q => ⟨q, 0, 4⟩
def n1 : MM02.State :=
  exec MM02.State.empty (allocOps topPlacement g (some (tk o0.nF)) MM02.State.empty (rootIdx lsO))
def n2 : MM02.State := exec n1 (deallocOps [rootAlloc L o1.P 1] 101)
example : ReprB tk ptk prov L o1 n1 ∧ ReprB tk ptk prov L o2 n2 := by decide
example : (frameRoots o2 o2.top).map (rootAlloc L o2.P) = [0] := by decide
example : ReprB tk ptk prov L o3 (exec n2 (exitOps L tk o2)) ∧ ReprB tk ptk prov L o3' (exec n1 (exitOps L tk o1)) := by
  decide
example : LiveAlloc (exec n1 (exitOps L tk o1)) 1 := by decide
example : MM02.DeallocStep C 1 101 (exec n2 (exitOps L tk o2)) .ub := .ub (by decide)

end CaseOwnedLocal

namespace DraftGaps

/-- Gap kept (report, (f) 5): the `WF3` of the draft accepts a usable root place without its
active root authority (MM-03.3 §2.1, clause 7, `RootHeld`: "chaque emplacement racine utilisable
possède son autorité racine `Modify` active"); the draft `RootHeld` only constrains the root
authorities that exist. `RootLive` holds on the reached states under `DDSound k`
(`reachable_rootLive`). -/
def sNoRoot : S3 :=
  { F := [0], nF := 1, P := [⟨none, .frame 0, 0⟩], I := fun _ => .uninit, A := [],
    D := fun _ => [], dead := fun _ => false, freed := fun _ => false, pin := fun _ => false,
    arenas := [], callParams := fun _ => [] }

theorem wf_noRoot : WF3 sNoRoot := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b y; simp [sNoRoot]
  · intro a x; simp [sNoRoot]
  · decide
  · decide
  · decide
  · intro q pl f hq ho
    match q, hq with
    | 0, hq => simp [sNoRoot] at hq; subst hq; cases ho; decide
  · intro q pl o hq ho
    match q, hq with
    | 0, hq => simp [sNoRoot] at hq; subst hq; cases ho
  · intro q pl r hq hp
    match q, hq with
    | 0, hq => simp [sNoRoot] at hq; subst hq; cases hp
  · intro a y hy; simp [sNoRoot] at hy
  · intro a y l hy; simp [sNoRoot] at hy
  · intro x z l r hz; simp [sNoRoot] at hz

example : RootPlace sNoRoot.P 0 ∧ sNoRoot.Usable 0 ∧ sNoRoot.A = [] := by decide
example : ¬ RootLive sNoRoot := fun h => by
  obtain ⟨i, z, pr, hz, -⟩ := h 0 (by decide) (by decide)
  simp [sNoRoot] at hz

/-- Gap kept (report, (f) 6): the `WF3` of the draft accepts a cycle of owners (MM-03.3 §2.1,
clause 3: "des chaînes de possession bien fondées"); it only asks owner places to exist. -/
def sCyc : S3 :=
  { F := [0], nF := 1, P := [⟨none, .place 1, 0⟩, ⟨none, .place 0, 0⟩], I := fun _ => .uninit,
    A := [], D := fun _ => [], dead := fun _ => false, freed := fun _ => false,
    pin := fun _ => false, arenas := [], callParams := fun _ => [] }

theorem wf_cyc : WF3 sCyc := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b y; simp [sCyc]
  · intro a x; simp [sCyc]
  · decide
  · decide
  · decide
  · intro q pl f hq ho
    match q, hq with
    | 0, hq => simp [sCyc] at hq; subst hq; cases ho
    | 1, hq => simp [sCyc] at hq; subst hq; cases ho
  · intro q pl o hq ho
    match q, hq with
    | 0, hq => simp [sCyc] at hq; subst hq; cases ho; decide
    | 1, hq => simp [sCyc] at hq; subst hq; cases ho; decide
  · intro q pl r hq hp
    match q, hq with
    | 0, hq => simp [sCyc] at hq; subst hq; cases hp
    | 1, hq => simp [sCyc] at hq; subst hq; cases hp
  · intro a y hy; simp [sCyc] at hy
  · intro a y l hy; simp [sCyc] at hy
  · intro x z l r hz; simp [sCyc] at hz

example : sCyc.P[0]? = some ⟨none, .place 1, 0⟩ ∧ sCyc.P[1]? = some ⟨none, .place 0, 0⟩ := by
  decide

end DraftGaps

namespace CaseSim

/-- Step 6 of the task: a full execution translated step by step through `simulation`. Contracts:
leaf 0 (the metadata of the arena) `SharedMutable`; `ExternalDone` for 1; the storage 4
deallocable with the authority 7. Frame 1 has the locals 0 (arena value), 1 (allocator value), 2
(destination of the block) and 3. `alloc` gives the storage 4, parts 5 and 6, owned by 0, of root
authority 4 (L2: one root); `newArena 4 4` registers it. The caller derives 5 (`Observe` on 0) and
6 (`Modify` on 2), pins 1, and calls with `[5, 6]`; the callee has the locals 7 and 8. `issue` gives
the block 9 on the region `[5]`, held by 7; `store 5 8` writes a pointer to 0 into 8; `transfer 7 2`
moves the block to the caller; `exitFrame`; `endUse 2`; `reset`; `unpin 1`; `free 4 7`;
`exitFrame`. -/
abbrev KS : K := KT [0] [] [1] [4] [(4, 7)]
def lsC : List (Option Nat × Option Nat × Nat) :=
  [(none, none, 0), (none, none, 0), (none, none, 0), (none, none, 0)]
def lsA : List (Option Nat × Option Nat × Nat) :=
  [(none, none, 0), (some 4, none, 0), (some 4, none, 0)]
def lsE : List (Option Nat × Option Nat × Nat) := [(none, none, 0), (none, none, 0)]
def arS : Arena := ⟨4, 4, [5, 6], []⟩

def x0 : S3 := S3.init []
def x1 : S3 := enterEff x0 [] lsC
def x2 : S3 := write3Eff x1 [1]
def x3 : S3 := allocEff x2 1 0 lsA
def x4 : S3 := write3Eff x3 [0]
def x5 : S3 := newArenaEff x4 4 4
def x6 : S3 := deriveEff x5 0 0 .observe
def x7 : S3 := deriveEff x6 2 2 .modify
def x8 : S3 := pinEff x7 1 true
def x9 : S3 := enterEff x8 [5, 6] lsE
def x10 : S3 := arenaSet (issueEff x9 arS [5] 7).1 0 (issueEff x9 arS [5] 7).2
def x11 : S3 := storeEff x10 5 8
def x12 : S3 := transferEff x11 7 2
def x13 : S3 := exitEff x12
def x14 : S3 := endUseEff x13 2
def x15 : S3 := resetAtEff x14 0
def x16 : S3 := pinEff x15 1 false
def x17 : S3 := freeEff x16 4
def x18 : S3 := exitEff x17

/-- MM-02 parameters fixed once for the run (`Params`): compatibility by equality of tokens (so
`TokCompat`); frame token `100 + f`, provider token `6 + pr` (the allocator at place 1 has the
token 7); geometry of 16 bytes aligned on 8 for every root; layout: one allocation per root, leaves
of 8 bytes, the parts 5 and 6 at offsets 0 and 8 of the allocation of 4; pointers of 8 bytes, little
endian, each byte carrying the provenance; the bytes written in leaf `l` are `10 l + i`. -/
def C : Nat → Nat → Prop := fun a d => a = d
def L : Layout := fun q => match q with
  | 0 => ⟨0, 0, 8⟩ | 1 => ⟨1, 0, 8⟩ | 2 => ⟨2, 0, 8⟩ | 3 => ⟨3, 0, 8⟩
  | 4 => ⟨4, 0, 16⟩ | 5 => ⟨4, 0, 8⟩ | 6 => ⟨4, 8, 8⟩ | 7 => ⟨5, 0, 8⟩
  | 8 => ⟨6, 0, 8⟩ | _ => ⟨99, 0, 0⟩
def pe : PtrEnc :=
  ⟨fun addr prov i => ((addr >>> (8 * i)).toUInt8, prov),
   fun f => (List.range 8).foldl (fun acc i => acc ||| ((f i).1.toNat <<< (8 * i))) 0⟩
def w : Nat → Nat → UInt8 × Option Nat := fun l i => ((10 * l + i).toUInt8, none)
def π : Params :=
  ⟨L, fun f => 100 + f, fun pr => 6 + pr, topPlacement, fun _ => ⟨0, 16, 8⟩, pe, w⟩
/-- Test obligations (K5): `dec`, an access aligned on 4 bytes; `stat`, true. -/
def obR : MM02.ReadOblSpec := ⟨fun _ ac => ac.addr % 4 = 0, fun _ _ => True⟩
def obW : MM02.WriteOblSpec := ⟨fun _ ac _ => ac.addr % 4 = 0, fun _ _ _ => True⟩
instance : ∀ s o, Decidable (Op2.Dec obR obW s o) := fun s o => by
  cases o <;> simp only [Op2.Dec, obR, obW] <;> infer_instance

/-- The ghost `provOf` (L4): empty, then the places 4, 5, 6 allocated from the provider 1. -/
def pv0 : Nat → Option Nat := fun _ => none
def pvA : Nat → Option Nat := provStep (.alloc 1 0 lsA) x2 pv0

/-- The MM-02 states of the translation: the run of `repr_init` (no static), then the sequence
associated with each step (`assoc`); the steps without MM-02 operation keep the state. -/
def n0 : MM02.State := exec MM02.State.empty (initOpsOf π [])
def n1 : MM02.State := exec n0 (assoc π (.enter [] lsC) x0 n0)
def n2 : MM02.State := exec n1 (assoc π (.write 1 [1] w) x1 n1)
def n3 : MM02.State := exec n2 (assoc π (.alloc 1 0 lsA) x2 n2)
def n4 : MM02.State := exec n3 (assoc π (.write 0 [0] w) x3 n3)
def n9 : MM02.State := exec n4 (assoc π (.enter [5, 6] lsE) x8 n4)
def n10 : MM02.State := exec n9 (assoc π (.issue 0 5 [5] 7) x9 n9)
def n11 : MM02.State := exec n10 (assoc π (.store 5 8) x10 n10)
def n12 : MM02.State := exec n11 (assoc π (.transfer 7 2) x11 n11)
def n13 : MM02.State := exec n12 (assoc π .exit x12 n12)
def n17 : MM02.State := exec n13 (assoc π (.free 4 7) x16 n13)
def n18 : MM02.State := exec n17 (assoc π .exit x17 n17)

/-- A prefix of the execution with its translation, the ghost and the MM-02 state named. -/
abbrev Run (s3 : S3) (pv : Nat → Option Nat) (s2 : MM02.State) : Prop :=
  ∃ ops os, SimRun KS C obR obW [] π ops s3 pv os s2

/-- The execution, step by step: each `ok` step of MM-03 (`Step3`, checked by `decide`) with its
obligations (`Oblig`: `NewLayout` for `enterFrame` and `alloc`, `dec` along its sequence, and
`FreeOblig` for `free 4 7`, met by the provider 1 of 4 and `ptok 1 = 7`). -/
theorem run0 : Run x0 pv0 n0 := ⟨_, _, .init (by decide) (by decide) trivial⟩
theorem run1 : Run x1 pv0 n1 := by
  obtain ⟨_, _, h⟩ := run0
  exact ⟨_, _, h.step (op := .enter [] lsC) ⟨by decide, .ok (by decide)⟩
    ⟨by decide, by decide, trivial⟩⟩
theorem run2 : Run x2 pv0 n2 := by
  obtain ⟨_, _, h⟩ := run1
  exact ⟨_, _, h.step (op := .write 1 [1] w) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run3 : Run x3 pvA n3 := by
  obtain ⟨_, _, h⟩ := run2
  exact ⟨_, _, h.step (op := .alloc 1 0 lsA) ⟨⟨0, by decide⟩, .ok (by decide) trivial⟩
    ⟨by decide, by decide, trivial⟩⟩
theorem run4 : Run x4 pvA n4 := by
  obtain ⟨_, _, h⟩ := run3
  exact ⟨_, _, h.step (op := .write 0 [0] w) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run5 : Run x5 pvA n4 := by
  obtain ⟨_, _, h⟩ := run4
  exact ⟨_, _, h.step (op := .newArena 4 4) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run6 : Run x6 pvA n4 := by
  obtain ⟨_, _, h⟩ := run5
  exact ⟨_, _, h.step (op := .derive 0 0 .observe) (.ok (by decide))
    ⟨by decide, by decide, trivial⟩⟩
theorem run7 : Run x7 pvA n4 := by
  obtain ⟨_, _, h⟩ := run6
  exact ⟨_, _, h.step (op := .derive 2 2 .modify) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run8 : Run x8 pvA n4 := by
  obtain ⟨_, _, h⟩ := run7
  exact ⟨_, _, h.step (op := .pin 1) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run9 : Run x9 pvA n9 := by
  obtain ⟨_, _, h⟩ := run8
  exact ⟨_, _, h.step (op := .enter [5, 6] lsE) ⟨by decide, .ok (by decide)⟩
    ⟨by decide, by decide, trivial⟩⟩
theorem step10 : Step3 KS (.issue 0 5 [5] 7) x9 x10 :=
  IssueAt.ok (ar := arS) (by decide) (.ok (by decide) (by decide) (by decide) (by decide))
theorem run10 : Run x10 pvA n10 := by
  obtain ⟨_, _, h⟩ := run9
  exact ⟨_, _, h.step step10 ⟨by decide, by decide, trivial⟩⟩
theorem run11 : Run x11 pvA n11 := by
  obtain ⟨_, _, h⟩ := run10
  exact ⟨_, _, h.step (op := .store 5 8) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem step12 : Step3 KS (.transfer 7 2) x11 x12 := .ok (by decide)
theorem ob12 : Oblig KS C obR obW π (.transfer 7 2) x11 x12 pvA n11 :=
  ⟨trivial, by decide, trivial⟩
theorem run12 : Run x12 pvA n12 := by
  obtain ⟨_, _, h⟩ := run11
  exact ⟨_, _, h.step step12 ob12⟩
theorem run13 : Run x13 pvA n13 := by
  obtain ⟨_, _, h⟩ := run12
  exact ⟨_, _, h.step (op := .exit) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run14 : Run x14 pvA n13 := by
  obtain ⟨_, _, h⟩ := run13
  exact ⟨_, _, h.step (op := .endUse 2) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run15 : Run x15 pvA n13 := by
  obtain ⟨_, _, h⟩ := run14
  exact ⟨_, _, h.step (op := .reset 0 0) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run16 : Run x16 pvA n13 := by
  obtain ⟨_, _, h⟩ := run15
  exact ⟨_, _, h.step (op := .unpin 1) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩
theorem run17 : Run x17 pvA n17 := by
  obtain ⟨_, _, h⟩ := run16
  exact ⟨_, _, h.step (op := .free 4 7) (.ok (by decide))
    ⟨trivial, by decide, fun _ => ⟨1, by decide, rfl⟩⟩⟩
theorem run18 : Run x18 pvA n18 := by
  obtain ⟨_, _, h⟩ := run17
  exact ⟨_, _, h.step (op := .exit) (.ok (by decide)) ⟨by decide, by decide, trivial⟩⟩

/-- `simulation` on every prefix of the run: an MM-02 run from `State.empty` with only `ok`
outcomes, reaching the state of the translation, in `Repr`. -/
theorem sim {s3 : S3} {pv : Nat → Option Nat} {s2 : MM02.State} (h : Run s3 pv s2) :
    ∃ os, AllOk C obR obW MM02.State.empty os ∧ exec MM02.State.empty os = s2 ∧
      Repr π.tok π.ptok pv π.L s3 s2 ∧ Reachable KS [] s3 := by
  obtain ⟨_, os, h⟩ := h
  have := simulation (KT_dd _ _ _ _ _) (fun _ _ => trivial) (fun _ _ _ => trivial) topPlacement_ok
    (fun _ => ⟨(by decide : 0 < 8), (by decide : MM02.Pow2 8)⟩) (fun _ => rfl) h
  exact ⟨os, this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩

/-- The whole execution: every MM-02 operation `ok`, `Repr` at the end; every allocation is dead at
the end (the storage 4 freed with the token 7, the locals deallocated at the exits). -/
example : ∃ os, AllOk C obR obW MM02.State.empty os ∧ exec MM02.State.empty os = n18 ∧
    Repr π.tok π.ptok pvA L x18 n18 := (sim run18).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩
example : ∀ i < 7, DeadAlloc n18 i := by decide
example : (n18.allocs 4).map (·.freeAuth) = some (some 7) := by decide


/-- The invariants of MM-03 and `Repr` on a prefix of the run. -/
theorem inv {s3 : S3} {pv : Nat → Option Nat} {s2 : MM02.State} (h : Run s3 pv s2) :
    Repr π.tok π.ptok pv L s3 s2 ∧ WF3 s3 ∧ NoDangling s3 ∧ FpLeaves s3 ∧ ArenasInv s3 ∧
      Reachable KS [] s3 := by
  obtain ⟨_, _, -, hR, hr⟩ := sim h
  exact ⟨hR, (reachable_invariants (KT_dd _ _ _ _ _) hr).1,
    (reachable_invariants (KT_dd _ _ _ _ _) hr).2.1.nd,
    (reachable_fpLeaves_frameOwnedLive (KT_dd _ _ _ _ _) hr).1,
    (reachable_access_invariant_underDD (KT_dd _ _ _ _ _) hr).2.2, hr⟩

/-- `issue` (L6): R6 on the step of the run, and `pointer_sound_issue`: the bytes written in the
destination 7 decode to the address 104 of the leaf 5 (base of the allocation 4 of the storage, plus
offset 0), and each carries the provenance 4, the allocation of every leaf of the storage 4 of the
arena, live. -/
example : AllOk C obR obW n9 (issueOps pe n9 L x9 0 [5] 7) ∧ Repr π.tok π.ptok pvA L x10 n10 := by
  obtain ⟨hR, hwf, -⟩ := inv run9
  have := r6_issue (C := C) (ObR := obR) (ObW := obW) (pe := pe) hwf hR step10
    (fun _ _ _ => trivial)
    (by show (leafAcc n9 L .write 7).addr % 4 = 0; decide)
  exact ⟨this.1, this.2.1⟩
example : pe.decode (issueBytes pe n9 L x9 0 [5]) = 104 ∧
    (∀ j, (issueBytes pe n9 L x9 0 [5] j).2 = some 4) ∧
    (∃ ar, x9.arenas[0]? = some ar ∧ ar.storage = 4 ∧
      ∀ l' ∈ footprint x9.P ar.storage, (L l').alloc = 4) ∧
    (∃ al, n9.allocs 4 = some al ∧ al.live = true ∧ regionAddr n9 L [5] = al.base + 0) := by
  obtain ⟨hR, hwf, hnd, hfl, hai, -⟩ := inv run9
  obtain ⟨h1, h2, ⟨ar, h3, h3'⟩, ⟨al, h4, h5, h6, -⟩, -⟩ := pointer_sound_issue (C := C)
    (ObR := obR) (ObW := obW) (pe := pe) hwf hnd hfl hai hR step10 (fun _ _ _ => trivial)
    (by show (leafAcc n9 L .write 7).addr % 4 = 0; decide) (l := 5) rfl
    ⟨by decide, fun _ => rfl⟩
  have e : ar = arS := Option.some.inj (h3.symm.trans (by decide))
  subst e
  exact ⟨h1.trans (by decide), h2, ⟨arS, h3, rfl, h3'⟩, al, h4, h5, h6⟩
example : rangeBytes n10 L 7 = some ([104, 0, 0, 0, 0, 0, 0, 0].map fun v => .init v (some 4)) := by
  decide

/-- `store` (L6), `pointer_sound_store`: the bytes written in 8 decode to the address 8 of the
leaf 0 covered by the authority 5, and each carries the provenance 0, the allocation of 0. -/
example : pe.decode (ptrBytes pe n10 L (x10.afp 5)) = 8 ∧
    (∀ i, (ptrBytes pe n10 L (x10.afp 5) i).2 = some 0) := by
  obtain ⟨hR, hwf, hnd, hfl, -⟩ := inv run10
  obtain ⟨h1, h2, -⟩ := pointer_sound_store (C := C) (ObR := obR) (ObW := obW) (pe := pe) hwf hnd
    hfl hR
    (.ok (by decide) : StoreStep 5 8 x10 (.ok x11)) (fun _ _ _ => trivial)
    (by show (leafAcc n10 L .write 8).addr % 4 = 0; decide) (l := 0) (by decide)
    ⟨by decide, fun _ => rfl⟩
  exact ⟨h1.trans (by decide), h2⟩

/-- `transfer` to the caller (L6), `transfer_copies`: the range of the destination 2 holds the bytes
of the source 7, the pointer to the block with its provenance 4; the source range is unchanged. -/
example : rangeBytes n12 L 2 = rangeBytes n11 L 7 ∧ rangeBytes n12 L 7 = rangeBytes n11 L 7 := by
  obtain ⟨hR, hwf, -⟩ := inv run11
  refine transfer_copies hwf hR step12 (fun l l' hm => ?_) 7 2 (by decide)
  rw [show transferPairs x11.P 7 2 = [(7, 2)] by decide, List.mem_singleton] at hm
  cases hm; rfl
example : rangeBytes n12 L 2 = some ([104, 0, 0, 0, 0, 0, 0, 0].map fun v => .init v (some 4)) := by
  decide

/-- `reset` (L6): no MM-02 step; only the library state of the arena entry (`available`, `issued`)
changes. -/
example : AllOk C obR obW n13 [] ∧ Repr π.tok π.ptok pvA L x15 (exec n13 []) := by
  obtain ⟨hR, -⟩ := inv run14
  exact r6_noStep (k := KS) hR (.reset (.ok (by decide) : ResetAtStep KS 0 0 x14 (.ok x15)))
example : x14.arenas = [⟨4, 4, [6], [([5], 9)]⟩] ∧ x15.arenas = [arS] := by decide
/-- After `transfer`, the block 9 is held by the leaf 2 of the caller (J1). -/
example : (x12.A[9]?).map (·.holder) = some (.place 2) ∧ x12.F = [2, 1, 0] := by decide
/-- Without the write of `issue` or of `transfer`, `Repr` fails (K3: an `Init` leaf has its bytes
initialised). -/
example : ¬ ReprB π.tok π.ptok pvA L x10 n9 ∧ ¬ ReprB π.tok π.ptok pvA L x12 n11 := by
  decide

/-- Witness of question (e) 2 of the pass-2 report, `issue`: `issue` of the empty region is `ok`
in `x9`; the pointer that L6 writes has the provenance 4 of the arena storage, and the address 0,
which L6 does not define for an empty block. -/
example : IssueAt KS 0 5 [] 7 x9
      (.ok (arenaSet (issueEff x9 arS [] 7).1 0 (issueEff x9 arS [] 7).2)) ∧
    regionAddr n9 L [] = 0 ∧ ∀ j, (issueBytes pe n9 L x9 0 [] j).2 = some 4 :=
  ⟨.ok (ar := arS) (by decide) (.ok (by decide) (by decide) (by decide) (by decide)), rfl,
    fun _ => (by decide : arenaProv L x9 0 = some 4)⟩

/-- Witness of question (e) 2 of the pass-2 report, `store`: `split 6 [[]]` gives the authority 10
of empty footprint (MM-03.3 O2 allows sub-regions of size zero), and `store 10 8` is `ok`; the
pointer of the empty region has the address 0 and no provenance. -/
def x10e : S3 := splitEff x10 6 [[]]
example : Step3 KS (.split 6 [[]]) x10 x10e ∧ Step3 KS (.store 10 8) x10e (storeEff x10e 10 8) ∧
    x10e.afp 10 = [] ∧ regionAddr n10 L (x10e.afp 10) = 0 ∧ regionProv L (x10e.afp 10) = none :=
  ⟨.ok (by decide), .ok (by decide), by decide, by decide, by decide⟩

/-- Witness of question (e) 3 of the pass-2 report: `issue` of the region `[6, 5]` (the leaves of
`[5, 6]`) is `ok`; the pointer has the address 112 of its first leaf 6, while the region begins at
104, the address of 5. Under the layout `Lsw`, which swaps the two fields (K1 fixes no order of
fields) and satisfies `LayoutWF`, the region `[5, 6]` gives 112 while it begins at 104. -/
example : Step3 KS (.issue 0 5 [6, 5] 7) x9
      (arenaSet (issueEff x9 arS [6, 5] 7).1 0 (issueEff x9 arS [6, 5] 7).2) ∧
    regionAddr n9 L [6, 5] = 112 ∧ leafAddr n9 L 5 = 104 ∧ leafAddr n9 L 6 = 112 :=
  ⟨.ok (ar := arS) (by decide) (.ok (by decide) (by decide) (by decide) (by decide)),
    by decide, by decide, by decide⟩
def Lsw : Layout := fun q => if q = 5 then ⟨4, 8, 8⟩ else if q = 6 then ⟨4, 0, 8⟩ else L q
example : LayoutWF Lsw x9 n9 ∧ regionAddr n9 Lsw [5, 6] = 112 ∧ leafAddr n9 Lsw 6 = 104 := by
  decide

/-- Witness of question (e) 4 of the pass-2 report: under the layout `L0`, where the leaf 8 has
size 0 (K1 (d)), `ReprB` holds before `store 5 8`, the pointer written decodes to 8 as before, and
the range of 8 receives no byte of it, while MM-03 makes 8 `Init` and lets it hold the
authority 5. -/
def L0 : Layout := fun q => if q = 8 then ⟨6, 0, 0⟩ else L q
example : ReprB π.tok π.ptok pvA L0 x10 n10 ∧ pe.decode (ptrBytes pe n10 L0 (x10.afp 5)) = 8 ∧
    rangeBytes (exec n10 (storeOps pe n10 L0 x10 5 8)) L0 8 = some [] ∧ x11.I 8 = .init ∧
    (x11.A[5]?).map (·.holder) = some (.place 8) := by
  decide

/-- L8 along the run (`simulation_pinned`): the leaf 1, pinned before the transfer, keeps a live
allocation and its address across the reads and writes of the step. -/
example : LiveAlloc n11 1 ∧ LiveAlloc n12 1 ∧ leafAddr n12 L 1 = leafAddr n11 L 1 := by
  obtain ⟨_, _, h⟩ := run11
  exact simulation_pinned (KT_dd _ _ _ _ _) (fun _ _ => trivial) (fun _ _ _ => trivial)
    topPlacement_ok (fun _ => ⟨(by decide : 0 < 8), (by decide : MM02.Pow2 8)⟩) (fun _ => rfl)
    h step12 ob12 (l := 1) (by decide) (by decide) (.inl (by decide))

end CaseSim

end Ern.MM23
