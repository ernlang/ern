/-!
# Elementary memory machine (spec v0.1, Parts II–III, §8–§20)

Source: `specs/ERN_Memory_Model_Specification.md`. Citations: `§N.k` is numbered item `k`
of section `N`; `§N ¶p` is the `p`-th paragraph of section `N`, a list belonging to the
paragraph that introduces it.

* State, allocations, bytes, places and accesses (§9–§12).
* Effects of valid operations: `State.write`, `State.dealloc`, `State.alloc`.
* Raw operations as transition relations with `ok`/`ub` outcomes, stated on every state
  (§20.1): `ReadStep`, `WriteStep`, `DeallocStep`, `AllocStep`. Typed reads and writes carry
  a type argument of an opaque type `Ty`; their unspecified obligations are explicit
  parameters split into a decidable part `dec` and a static part `stat` (§20.3).
* Interpreters `read`, `write`, `dealloc`, `alloc`, computable, with the static part as a
  proof argument (§20.3 ¶3), agreeing with the relations in both directions.
* Executions `Exec` (sequences of `ok` steps) from any initial state (§9 ¶9).
-/

namespace Ern.MemoryModel.Machine

/-! ## State and accesses (Part II) -/

/-- Elementary access authority of a means of access (§12 ¶1, §12 ¶4). -/
inductive Auth where
  | read
  | write
  deriving DecidableEq

/-- The elementary authority order `read ≤ write`, reflexive (§12 ¶4). -/
instance : LE Auth := ⟨fun a b => a = .read ∨ b = .write⟩

/-- The elementary authority order is decidable (§12 ¶4). -/
instance (a b : Auth) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a = .read ∨ b = .write))

/-- Abstract byte: uninitialized, or initialized with an 8-bit value and an optional
provenance represented by an allocation identity (§10 ¶1–¶3). -/
inductive AByte where
  | uninit
  | init (val : UInt8) (prov : Option Nat)
  deriving DecidableEq

/-- Abstract allocation (§9 ¶1). Its identity is its key in `State.allocs`. `bytes` is
indexed by offset from `base`; offsets outside `[0, size)` are reached by no permitted
access (`Spatial`). `freeAuth = some d` records the deallocation token `d` of a
deallocatable allocation (§9 ¶1 b8, §17 ¶4); `none` marks a non-deallocatable one. -/
structure Alloc where
  space : Nat
  base : Nat
  size : Nat
  align : Nat
  live : Bool
  bytes : Nat → AByte
  freeAuth : Option Nat

/-- Place of the minimal kernel: allocation identity, offset and length (§11 ¶1). -/
structure Place where
  alloc : Nat
  off : Nat
  len : Nat

/-- Means of access: address, provenance (an allocation identity), length and elementary
access authority (§12 ¶1, §12 ¶2). -/
structure Access where
  addr : Nat
  prov : Nat
  len : Nat
  auth : Auth

/-- Abstract state: registered allocations by identity, live or dead, and the counter `next`
representing the freshness discipline (§9 ¶7, §13 ¶1). -/
structure State where
  allocs : Nat → Option Alloc
  next : Nat

/-- Well-formedness of identities and freshness: no identity at or above the counter is
registered (§9 ¶7, §9 ¶8 b1). -/
def WF (s : State) : Prop := ∀ i, s.next ≤ i → s.allocs i = none

/-- Spatial containment of an access in an allocation (§15 ¶1; used by §15.2 and §16.2). -/
def Spatial (a : Alloc) (ac : Access) : Prop :=
  a.base ≤ ac.addr ∧ ac.addr + ac.len ≤ a.base + a.size

/-- Spatial containment is decidable (§15 ¶1). -/
instance (a : Alloc) (ac : Access) : Decidable (Spatial a ac) :=
  inferInstanceAs (Decidable (a.base ≤ ac.addr ∧ ac.addr + ac.len ≤ a.base + a.size))

/-- The `len` bytes from offset `off` are initialized (§15.3, read as: every byte of the
accessed range). -/
def Alloc.InitRange (a : Alloc) (off len : Nat) : Prop :=
  ∀ i, i < len → a.bytes (off + i) ≠ .uninit

/-- Initialization of a range is decidable (§15.3). -/
instance (a : Alloc) (off len : Nat) : Decidable (a.InitRange off len) :=
  inferInstanceAs (Decidable (∀ i, i < len → a.bytes (off + i) ≠ .uninit))

/-- Kernel conditions of a raw typed read by `ac`: §15.1, §15.2, §15.3 and §15.5. The
conditions §15.4, §15.6 and §15.7 are the parametric obligations of `ReadOblSpec`. -/
def CanRead (s : State) (ac : Access) : Prop :=
  ∃ a, s.allocs ac.prov = some a ∧ a.live = true ∧ Spatial a ac ∧
    a.InitRange (ac.addr - a.base) ac.len ∧ Auth.read ≤ ac.auth

/-- Kernel conditions of a raw typed write by `ac`: §16.1, §16.2 and §16.3. The conditions
§16.4–§16.6 are the parametric obligations of `WriteOblSpec`. -/
def CanWrite (s : State) (ac : Access) : Prop :=
  ∃ a, s.allocs ac.prov = some a ∧ a.live = true ∧ Spatial a ac ∧ Auth.write ≤ ac.auth

/-- The kernel conditions of a read are decidable (§15). -/
instance (s : State) (ac : Access) : Decidable (CanRead s ac) :=
  match h : s.allocs ac.prov with
  | some a =>
    if hc : a.live = true ∧ Spatial a ac ∧ a.InitRange (ac.addr - a.base) ac.len ∧
        Auth.read ≤ ac.auth then isTrue ⟨a, h, hc⟩
    else isFalse fun ⟨b, hb, hb'⟩ => hc (by rw [h] at hb; cases hb; exact hb')
  | none => isFalse fun ⟨b, hb, _⟩ => by rw [h] at hb; cases hb

/-- The kernel conditions of a write are decidable (§16). -/
instance (s : State) (ac : Access) : Decidable (CanWrite s ac) :=
  match h : s.allocs ac.prov with
  | some a =>
    if hc : a.live = true ∧ Spatial a ac ∧ Auth.write ≤ ac.auth then isTrue ⟨a, h, hc⟩
    else isFalse fun ⟨b, hb, hb'⟩ => hc (by rw [h] at hb; cases hb; exact hb')
  | none => isFalse fun ⟨b, hb, _⟩ => by rw [h] at hb; cases hb

/-- Partial resolution of a means of access to a place (§11 ¶2): defined when the
provenance identifies a registered allocation, live or dead, that spatially contains the
access. It proves no right to read or write. -/
def Access.toPlace (s : State) (ac : Access) : Option Place :=
  match s.allocs ac.prov with
  | some a => if Spatial a ac then some ⟨ac.prov, ac.addr - a.base, ac.len⟩ else none
  | none => none

/-- Characterization of resolution (§11 ¶2). -/
theorem toPlace_eq_some {s : State} {ac : Access} {p : Place} :
    ac.toPlace s = some p ↔
      ∃ a, s.allocs ac.prov = some a ∧ Spatial a ac ∧
        p = ⟨ac.prov, ac.addr - a.base, ac.len⟩ := by
  unfold Access.toPlace
  split
  · next a ha =>
    by_cases hs : Spatial a ac
    · simp [hs, ha, eq_comm]
    · simp [hs, ha]
  · next ha => simp [ha]

/-- The `len` bytes of `a` from offset `off`: the value of a valid read (§20.2 ¶1). -/
def Alloc.bytesAt (a : Alloc) (off len : Nat) : List AByte :=
  (List.range len).map fun i => a.bytes (off + i)

/-- The `len` written bytes from position `off` of the supplied representation `w`, each
initialized with its value and provenance (§16 ¶2, §16 ¶5). -/
def writtenBytes (w : Nat → UInt8 × Option Nat) (off len : Nat) : List AByte :=
  (List.range len).map fun i => .init (w (off + i)).1 (w (off + i)).2

/-- Effect of a valid write on storage (§16 ¶2, §10 ¶4): the bytes at offsets
`[off, off + len)` are replaced byte by byte by `w`, initialized with the supplied value and
provenance; other bytes are unchanged (§16 ¶3). -/
def Alloc.write (a : Alloc) (off len : Nat) (w : Nat → UInt8 × Option Nat) : Alloc :=
  { a with bytes := fun j =>
      if off ≤ j ∧ j < off + len then .init (w (j - off)).1 (w (j - off)).2 else a.bytes j }

/-- Effect of a valid write of `w` through `ac` on the state (§16 ¶2, §16 ¶3). -/
def State.write (s : State) (ac : Access) (w : Nat → UInt8 × Option Nat) : State :=
  { s with allocs := fun i =>
      if i = ac.prov then (s.allocs i).map (fun a => a.write (ac.addr - a.base) ac.len w)
      else s.allocs i }

/-- Conditions of a successful raw deallocation of `id` with presented authority `auth`
(§17.1, §17.2): live, deallocatable, and `auth` compatible with the recorded token under the
context relation `C` (§17 ¶2, §17 ¶4). -/
def CanDealloc (C : Nat → Nat → Prop) (s : State) (id auth : Nat) : Prop :=
  ∃ a, s.allocs id = some a ∧ a.live = true ∧ ∃ d, a.freeAuth = some d ∧ C auth d

/-- Deallocation conditions are decidable when compatibility is (§17, §20.3 ¶3). -/
instance {C : Nat → Nat → Prop} [DecidableRel C] (s : State) (id auth : Nat) :
    Decidable (CanDealloc C s id auth) :=
  match h : s.allocs id with
  | none => isFalse fun ⟨b, hb, _⟩ => by rw [h] at hb; cases hb
  | some a =>
    match hf : a.freeAuth with
    | none => isFalse fun ⟨b, hb, _, d, hd, _⟩ => by
        rw [h] at hb
        cases hb
        rw [hf] at hd
        cases hd
    | some d =>
      if hc : a.live = true ∧ C auth d then isTrue ⟨a, h, hc.1, d, hf, hc.2⟩
      else isFalse fun ⟨b, hb, hl, d', hd', hc'⟩ => hc (by
        rw [h] at hb
        cases hb
        rw [hf] at hd'
        cases hd'
        exact ⟨hl, hc'⟩)

/-- Effect of a valid deallocation (§17 ¶3, §20.2 ¶2): `id` becomes dead and stays
registered (§13 ¶1). -/
def State.dealloc (s : State) (id : Nat) : State :=
  { s with allocs := fun i =>
      if i = id then (s.allocs i).map (fun a => { a with live := false }) else s.allocs i }

/-- Effect of a valid raw creation (§9 ¶11, §13 ¶1, §20.2 ¶2): a live allocation under the
identity `s.next`, wholly uninitialized (§10 ¶5); the counter advances (§9 ¶7). -/
def State.alloc (s : State) (space base size align : Nat) (freeAuth : Option Nat) : State :=
  { allocs := fun i =>
      if i = s.next then
        some { space, base, size, align, live := true, bytes := fun _ => .uninit, freeAuth }
      else s.allocs i
    next := s.next + 1 }

/-- Half-open ranges `[b1, b1 + n1)` and `[b2, b2 + n2)` have an empty intersection (§9 ¶3). -/
def RangeDisjoint (b1 n1 b2 n2 : Nat) : Prop :=
  ∀ x, b1 ≤ x → x < b1 + n1 → b2 ≤ x → x < b2 + n2 → False

/-- Arithmetic form of range disjointness (§9 ¶3). -/
theorem rangeDisjoint_iff {b1 n1 b2 n2 : Nat} :
    RangeDisjoint b1 n1 b2 n2 ↔ b1 + n1 ≤ b2 ∨ b2 + n2 ≤ b1 ∨ n1 = 0 ∨ n2 = 0 := by
  constructor
  · intro h
    rcases Nat.le_total b1 b2 with h12 | h12
    · by_cases hlt : b2 < b1 + n1
      · by_cases hn : 0 < n2
        · exact (h b2 h12 hlt (Nat.le_refl _) (by omega)).elim
        · omega
      · omega
    · by_cases hlt : b1 < b2 + n2
      · by_cases hn : 0 < n1
        · exact (h b1 (Nat.le_refl _) (by omega) h12 hlt).elim
        · omega
      · omega
  · intro h x h1 h2 h3 h4
    omega

/-- Range disjointness is decidable (§9 ¶3). -/
instance (b1 n1 b2 n2 : Nat) : Decidable (RangeDisjoint b1 n1 b2 n2) :=
  decidable_of_iff _ rangeDisjoint_iff.symm

/-- Disjointness of live allocations in the same address space (§9 ¶3, §9 ¶8 b2). -/
def LiveDisjoint (s : State) : Prop :=
  ∀ i j a b, i ≠ j → s.allocs i = some a → s.allocs j = some b →
    a.live = true → b.live = true → a.space = b.space →
    RangeDisjoint a.base a.size b.base b.size

/-- `n` is a power of two (§9 ¶1 b5, §9 ¶4). -/
def Pow2 (n : Nat) : Prop := ∃ k, n = 2 ^ k

/-- Bounded form of `Pow2` (§9 ¶4). -/
theorem pow2_iff (n : Nat) : Pow2 n ↔ ∃ k, k < n + 1 ∧ n = 2 ^ k :=
  ⟨fun ⟨k, hk⟩ => ⟨k, by have := @Nat.lt_two_pow_self k; omega, hk⟩, fun ⟨k, _, hk⟩ => ⟨k, hk⟩⟩

/-- `Pow2` is decidable (§9 ¶4). -/
instance (n : Nat) : Decidable (Pow2 n) :=
  decidable_of_iff _ (pow2_iff n).symm

/-- Operation preconditions of raw creation in space `space` (§9 ¶11): fresh identity
`s.next`, strictly positive power-of-two alignment, aligned base, no overlap with any live
allocation of the same space. -/
def AllocPre (s : State) (space base size align : Nat) : Prop :=
  s.allocs s.next = none ∧ 0 < align ∧ Pow2 align ∧ base % align = 0 ∧
    ∀ i a, s.allocs i = some a → a.live = true → a.space = space →
      RangeDisjoint a.base a.size base size

/-- The entry `o` does not overlap `[base, base + size)` in space `space`: absent, dead, of
another space, or disjoint (§9 ¶11). -/
def NoOverlap (space base size : Nat) : Option Alloc → Prop
  | some a => a.live = true → a.space = space → RangeDisjoint a.base a.size base size
  | none => True

/-- `NoOverlap` is decidable (§9 ¶11). -/
instance (space base size : Nat) : (o : Option Alloc) → Decidable (NoOverlap space base size o)
  | some a => inferInstanceAs
      (Decidable (a.live = true → a.space = space → RangeDisjoint a.base a.size base size))
  | none => inferInstanceAs (Decidable True)

/-- Decidable form of `AllocPre`, checking overlap on identities below the counter only
(§9 ¶11, §20.3 ¶3). -/
def AllocPreDec (s : State) (space base size align : Nat) : Prop :=
  s.allocs s.next = none ∧ 0 < align ∧ Pow2 align ∧ base % align = 0 ∧
    ∀ i, i < s.next → NoOverlap space base size (s.allocs i)

/-- `AllocPreDec` is decidable (§20.3 ¶3). -/
instance (s : State) (space base size align : Nat) :
    Decidable (AllocPreDec s space base size align) := by
  unfold AllocPreDec
  infer_instance

/-- Under freshness, `AllocPreDec` is `AllocPre` (§9 ¶7, §9 ¶11). -/
theorem allocPreDec_iff {s : State} (hwf : WF s) {space base size align : Nat} :
    AllocPreDec s space base size align ↔ AllocPre s space base size align := by
  constructor
  · rintro ⟨hf, h0, h2, hm, hd⟩
    refine ⟨hf, h0, h2, hm, fun i a ha hl hsp => ?_⟩
    have hi : i < s.next := Nat.lt_of_not_le fun hle => by rw [hwf i hle] at ha; cases ha
    have := hd i hi
    rw [ha] at this
    exact this hl hsp
  · rintro ⟨hf, h0, h2, hm, hd⟩
    refine ⟨hf, h0, h2, hm, fun i _ => ?_⟩
    cases ha : s.allocs i with
    | none => trivial
    | some a => exact fun hl hsp => hd i a ha hl hsp

/-- Alignment of every registered allocation, live or dead (§9 ¶4, §9 ¶8 b3). -/
def Aligned (s : State) : Prop :=
  ∀ i a, s.allocs i = some a → 0 < a.align ∧ Pow2 a.align ∧ a.base % a.align = 0

/-- Admissible state (§9 ¶8): freshness, live disjointness, alignment. -/
structure Admissible (s : State) : Prop where
  wf : WF s
  disjoint : LiveDisjoint s
  aligned : Aligned s

/-- The empty state: no allocation, counter `0` (§9 ¶9). -/
def State.empty : State := ⟨fun _ => none, 0⟩

/-- The empty state is an admissible initial state (§9 ¶9). -/
theorem admissible_empty : Admissible State.empty :=
  ⟨fun _ _ => rfl, (fun _ _ _ _ _ h => nomatch h), (fun _ _ h => nomatch h)⟩

/-! ## Restrictive derivation (§14) -/

/-- `ac'` is a restrictive derivation of `ac` (§14 ¶1): same provenance, address subrange,
authority at most that of the source. -/
def Derive (ac ac' : Access) : Prop :=
  ac.addr ≤ ac'.addr ∧ ac'.addr + ac'.len ≤ ac.addr + ac.len ∧
    ac'.prov = ac.prov ∧ ac'.auth ≤ ac.auth

/-- A restrictive derivation preserves provenance (§14 ¶1 b1). -/
theorem derive_prov {ac ac' : Access} (hd : Derive ac ac') : ac'.prov = ac.prov :=
  hd.2.2.1

/-- A restrictive derivation of an access contained in an allocation is contained in it
(§14 ¶1 b2, §15 ¶1). -/
theorem derive_spatial {ac ac' : Access} (hd : Derive ac ac') {a : Alloc}
    (hs : Spatial a ac) : Spatial a ac' := by
  obtain ⟨h1, h2, -, -⟩ := hd
  obtain ⟨h3, h4⟩ := hs
  exact ⟨Nat.le_trans h3 h1, Nat.le_trans h2 h4⟩

/-- A restrictive derivation confers no greater authority (§14 ¶1 b3). -/
theorem derive_auth_le {ac ac' : Access} (hd : Derive ac ac') : ac'.auth ≤ ac.auth :=
  hd.2.2.2

/-! ## Parametric obligations and outcomes (§15 ¶5, §16 ¶4, §20) -/

/-- Read obligations not defined by the kernel, §15.4, §15.6, §15.7 (§15 ¶5): explicit
predicates of the execution context (§20.3 ¶1), depending on the state, the access and the
read type; `dec` is the part with a decision procedure, `stat` the part established
statically or by contract (§20.3 ¶2). -/
structure ReadOblSpec (Ty : Type) where
  dec : State → Access → Ty → Prop
  stat : State → Access → Ty → Prop

/-- Read obligations with a decision instance for `dec`, as required by a computable
interpreter (§20.3 ¶3). -/
structure ReadObl (Ty : Type) extends toSpec : ReadOblSpec Ty where
  decInst : ∀ s ac t, Decidable (dec s ac t)

attribute [instance] ReadObl.decInst

/-- Write obligations not defined by the kernel, §16.4, §16.5, §16.6 (§16 ¶4): explicit
predicates of the execution context (§20.3 ¶1), depending on the state, the access, the
written type and the supplied representation; split into `dec` and `stat` (§20.3 ¶2). -/
structure WriteOblSpec (Ty : Type) where
  dec : State → Access → Ty → (Nat → UInt8 × Option Nat) → Prop
  stat : State → Access → Ty → (Nat → UInt8 × Option Nat) → Prop

/-- Write obligations with a decision instance for `dec`, as required by a computable
interpreter (§20.3 ¶3). -/
structure WriteObl (Ty : Type) extends toSpec : WriteOblSpec Ty where
  decInst : ∀ s ac t w, Decidable (dec s ac t w)

attribute [instance] WriteObl.decInst

/-- Outcome of a raw state-transforming operation: `ok` with the new state, or `ub`, which
supplies no state (§20.1 ¶2, §1). -/
inductive Outcome where
  | ok (s : State)
  | ub

/-- Outcome of a raw read: `ok` with the bytes read, or `ub` (§20.1 ¶2, §20.2 ¶1). -/
inductive ReadOutcome where
  | ok (v : List AByte)
  | ub
  deriving DecidableEq

section Relations

variable {Ty : Type}

/-- Raw typed read of type `t` through `ac` (§15, §20.1, §20.2 ¶1): `ok` with the bytes of
the accessed range when the kernel conditions (`CanRead`) and both parts of the obligations
hold; `ub` otherwise, a violated static part included (§20.1 ¶2 b2). The state is
unchanged. -/
inductive ReadStep (ObR : ReadOblSpec Ty) (ac : Access) (t : Ty) (s : State) :
    ReadOutcome → Prop where
  | ok {a : Alloc} : s.allocs ac.prov = some a → CanRead s ac ∧ ObR.dec s ac t ∧ ObR.stat s ac t →
      ReadStep ObR ac t s (.ok (a.bytesAt (ac.addr - a.base) ac.len))
  | ub : ¬ (CanRead s ac ∧ ObR.dec s ac t ∧ ObR.stat s ac t) → ReadStep ObR ac t s .ub

/-- Raw typed write of `w` at type `t` through `ac` (§16, §20.1, §20.2 ¶2): `ok` with the
effect `State.write` when the kernel conditions (`CanWrite`) and both parts of the
obligations hold; `ub` otherwise (§20.1 ¶2 b2). -/
inductive WriteStep (ObW : WriteOblSpec Ty) (ac : Access) (t : Ty)
    (w : Nat → UInt8 × Option Nat) (s : State) : Outcome → Prop where
  | ok : CanWrite s ac ∧ ObW.dec s ac t w ∧ ObW.stat s ac t w →
      WriteStep ObW ac t w s (.ok (s.write ac w))
  | ub : ¬ (CanWrite s ac ∧ ObW.dec s ac t w ∧ ObW.stat s ac t w) → WriteStep ObW ac t w s .ub

end Relations

/-- Raw deallocation of `id` with presented authority `auth` (§17, §20.1, §20.2 ¶2): `ok`
with the effect `State.dealloc` when `CanDealloc`; `ub` otherwise. `C` needs no decision
instance (§20.3 ¶3). -/
inductive DeallocStep (C : Nat → Nat → Prop) (id auth : Nat) (s : State) : Outcome → Prop where
  | ok : CanDealloc C s id auth → DeallocStep C id auth s (.ok (s.dealloc id))
  | ub : ¬ CanDealloc C s id auth → DeallocStep C id auth s .ub

/-- Raw creation (§9 ¶11, §20.1, §20.2 ¶2): `ok` with the effect `State.alloc` when
`AllocPre`; `ub` otherwise. -/
inductive AllocStep (space base size align : Nat) (freeAuth : Option Nat) (s : State) :
    Outcome → Prop where
  | ok : AllocPre s space base size align →
      AllocStep space base size align freeAuth s (.ok (s.alloc space base size align freeAuth))
  | ub : ¬ AllocPre s space base size align → AllocStep space base size align freeAuth s .ub

/-! ## Interpreters (§20.3 ¶3; `formal/DESIGN.md`, "Representation") -/

section Interpreters

variable {Ty : Type}

/-- Interpreter of `ReadStep`: decides the kernel conditions and `dec`, takes the static
part `stat` as a proof argument (§20.3 ¶3), and returns the bytes read (§20.2 ¶1). -/
def read (ObR : ReadObl Ty) (ac : Access) (t : Ty) (s : State) (_hs : ObR.stat s ac t) :
    ReadOutcome :=
  match s.allocs ac.prov with
  | some a =>
    if CanRead s ac ∧ ObR.dec s ac t then .ok (a.bytesAt (ac.addr - a.base) ac.len) else .ub
  | none => .ub

/-- Interpreter of `WriteStep`: decides the kernel conditions and `dec`, takes `stat` as a
proof argument (§20.3 ¶3). -/
def write (ObW : WriteObl Ty) (ac : Access) (t : Ty) (w : Nat → UInt8 × Option Nat) (s : State)
    (_hs : ObW.stat s ac t w) : Outcome :=
  if CanWrite s ac ∧ ObW.dec s ac t w then .ok (s.write ac w) else .ub

end Interpreters

/-- Interpreter of `DeallocStep`, given a decision instance for compatibility (§20.3 ¶3). -/
def dealloc (C : Nat → Nat → Prop) [DecidableRel C] (id auth : Nat) (s : State) : Outcome :=
  if CanDealloc C s id auth then .ok (s.dealloc id) else .ub

/-- Interpreter of `AllocStep`, taking freshness `WF s` as a proof argument; it decides
`AllocPreDec`, which is `AllocPre` under `WF` (§9 ¶11, §20.3 ¶3). -/
def alloc (space base size align : Nat) (freeAuth : Option Nat) (s : State) (_hwf : WF s) :
    Outcome :=
  if AllocPreDec s space base size align then .ok (s.alloc space base size align freeAuth)
  else .ub

/-! ## Executions (§9 ¶9, §20.1 ¶2, §20.3 ¶3) -/

/-- Raw operations of the machine (§15, §16, §17, §9 ¶11, §20.1). -/
inductive Op (Ty : Type) where
  | read (ac : Access) (t : Ty)
  | write (ac : Access) (t : Ty) (w : Nat → UInt8 × Option Nat)
  | dealloc (id auth : Nat)
  | alloc (space base size align : Nat) (freeAuth : Option Nat)

section Executions

variable {Ty : Type}

/-- `ok` transitions of the raw operations, with compatibility and obligations fixed by the
execution context (§20.1 ¶2, §20.3 ¶3). A read leaves the state unchanged (§20.2 ¶1). -/
inductive Step (C : Nat → Nat → Prop) (ObR : ReadOblSpec Ty) (ObW : WriteOblSpec Ty) :
    Op Ty → State → State → Prop where
  | read {ac : Access} {t : Ty} {s : State} {v : List AByte} :
      ReadStep ObR ac t s (.ok v) → Step C ObR ObW (.read ac t) s s
  | write {ac : Access} {t : Ty} {w : Nat → UInt8 × Option Nat} {s s' : State} :
      WriteStep ObW ac t w s (.ok s') → Step C ObR ObW (.write ac t w) s s'
  | dealloc {id auth : Nat} {s s' : State} :
      DeallocStep C id auth s (.ok s') → Step C ObR ObW (.dealloc id auth) s s'
  | alloc {space base size align : Nat} {freeAuth : Option Nat} {s s' : State} :
      AllocStep space base size align freeAuth s (.ok s') →
      Step C ObR ObW (.alloc space base size align freeAuth) s s'

/-- Execution: a sequence of `ok` steps under one context (§20.3 ¶3). A `ub` step supplies
no state, so it never occurs inside an execution (§20.1 ¶2 b3). -/
inductive Exec (C : Nat → Nat → Prop) (ObR : ReadOblSpec Ty) (ObW : WriteOblSpec Ty) :
    List (Op Ty) → State → State → Prop where
  | nil (s : State) : Exec C ObR ObW [] s s
  | cons {op : Op Ty} {ops : List (Op Ty)} {s s' s'' : State} :
      Step C ObR ObW op s s' → Exec C ObR ObW ops s' s'' → Exec C ObR ObW (op :: ops) s s''

/-- `s` is reachable from the initial state `s₀`, which need not be empty (§9 ¶9). -/
def Reachable (C : Nat → Nat → Prop) (ObR : ReadOblSpec Ty) (ObW : WriteOblSpec Ty)
    (s₀ s : State) : Prop :=
  ∃ ops, Exec C ObR ObW ops s₀ s

/-- The operation neither writes through provenance `i` nor deallocates `i`. Used to state
the "absence of an intervening write or invalidation" of §16 ¶5 for allocation `i`; writes
through other provenances are allowed (non-interference, §16 ¶5). -/
def Op.KeepsAlloc (i : Nat) : Op Ty → Prop
  | .read _ _ => True
  | .write ac _ _ => ac.prov ≠ i
  | .dealloc id _ => id ≠ i
  | .alloc .. => True

end Executions

/-! ## Outcome characterizations, determinism, totality (§20.1) -/

section Theorems

variable {Ty : Type}

/-- `ok` outcome of a raw read (§15, §20.1 ¶2 b1, §20.2 ¶1). -/
theorem ReadStep_ok_iff {ObR : ReadOblSpec Ty} {ac : Access} {t : Ty} {s : State}
    {v : List AByte} :
    ReadStep ObR ac t s (.ok v) ↔ (CanRead s ac ∧ ObR.dec s ac t ∧ ObR.stat s ac t) ∧
      ∃ a, s.allocs ac.prov = some a ∧ v = a.bytesAt (ac.addr - a.base) ac.len :=
  ⟨fun h => by cases h with | ok ha h => exact ⟨h, _, ha, rfl⟩,
   fun ⟨h, _, ha, e⟩ => by subst e; exact .ok ha h⟩

/-- `ok` outcome of a raw write (§16, §20.1 ¶2 b1). -/
theorem WriteStep_ok_iff {ObW : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s s' : State} :
    WriteStep ObW ac t w s (.ok s') ↔
      (CanWrite s ac ∧ ObW.dec s ac t w ∧ ObW.stat s ac t w) ∧ s' = s.write ac w :=
  ⟨fun h => by cases h with | ok h => exact ⟨h, rfl⟩, fun ⟨h, e⟩ => by subst e; exact .ok h⟩

/-- `ok` outcome of a raw deallocation (§17, §20.1 ¶2 b1). -/
theorem DeallocStep_ok_iff {C : Nat → Nat → Prop} {id auth : Nat} {s s' : State} :
    DeallocStep C id auth s (.ok s') ↔ CanDealloc C s id auth ∧ s' = s.dealloc id :=
  ⟨fun h => by cases h with | ok h => exact ⟨h, rfl⟩, fun ⟨h, e⟩ => by subst e; exact .ok h⟩

/-- `ok` outcome of a raw creation (§9 ¶11, §20.1 ¶2 b1). -/
theorem AllocStep_ok_iff {space base size align : Nat} {freeAuth : Option Nat} {s s' : State} :
    AllocStep space base size align freeAuth s (.ok s') ↔
      AllocPre s space base size align ∧ s' = s.alloc space base size align freeAuth :=
  ⟨fun h => by cases h with | ok h => exact ⟨h, rfl⟩, fun ⟨h, e⟩ => by subst e; exact .ok h⟩

/-- A raw read has at most one outcome (§20.1 ¶3). -/
theorem ReadStep_det {ObR : ReadOblSpec Ty} {ac : Access} {t : Ty} {s : State}
    {o₁ o₂ : ReadOutcome} (h₁ : ReadStep ObR ac t s o₁) (h₂ : ReadStep ObR ac t s o₂) :
    o₁ = o₂ := by
  cases h₁ with
  | ok ha _ =>
    cases h₂ with
    | ok hb _ => rw [ha] at hb; cases hb; rfl
    | ub => contradiction
  | ub => cases h₂ with
    | ok => contradiction
    | ub => rfl

/-- A raw write has at most one outcome (§20.1 ¶3). -/
theorem WriteStep_det {ObW : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s : State} {o₁ o₂ : Outcome}
    (h₁ : WriteStep ObW ac t w s o₁) (h₂ : WriteStep ObW ac t w s o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- A raw deallocation has at most one outcome (§20.1 ¶3). -/
theorem DeallocStep_det {C : Nat → Nat → Prop} {id auth : Nat} {s : State}
    {o₁ o₂ : Outcome} (h₁ : DeallocStep C id auth s o₁) (h₂ : DeallocStep C id auth s o₂) :
    o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- A raw creation has at most one outcome (§20.1 ¶3). -/
theorem AllocStep_det {space base size align : Nat} {freeAuth : Option Nat} {s : State}
    {o₁ o₂ : Outcome} (h₁ : AllocStep space base size align freeAuth s o₁)
    (h₂ : AllocStep space base size align freeAuth s o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

/-- Totality of the raw read on every state (§20.1 ¶3), in the constructive form
`¬¬∃`, classically equivalent to `∃`; `stat` has no decision procedure. -/
theorem ReadStep_total (ObR : ReadOblSpec Ty) (ac : Access) (t : Ty) (s : State) :
    ¬¬ ∃ o, ReadStep ObR ac t s o :=
  fun hn => hn ⟨.ub, .ub fun h => let ⟨_, ha, _⟩ := h.1; hn ⟨_, .ok ha h⟩⟩

/-- Totality of the raw write on every state (§20.1 ¶3), constructive form `¬¬∃`. -/
theorem WriteStep_total (ObW : WriteOblSpec Ty) (ac : Access) (t : Ty)
    (w : Nat → UInt8 × Option Nat) (s : State) : ¬¬ ∃ o, WriteStep ObW ac t w s o :=
  fun hn => hn ⟨.ub, .ub fun h => hn ⟨_, .ok h⟩⟩

/-- Totality of the raw deallocation on every state (§20.1 ¶3), constructive form `¬¬∃`;
`C` has no decision procedure. -/
theorem DeallocStep_total (C : Nat → Nat → Prop) (id auth : Nat) (s : State) :
    ¬¬ ∃ o, DeallocStep C id auth s o :=
  fun hn => hn ⟨.ub, .ub fun h => hn ⟨_, .ok h⟩⟩

/-- Totality of the raw creation on every state (§20.1 ¶3), constructive form `¬¬∃`;
`AllocPre` quantifies over every identity. -/
theorem AllocStep_total (space base size align : Nat) (freeAuth : Option Nat) (s : State) :
    ¬¬ ∃ o, AllocStep space base size align freeAuth s o :=
  fun hn => hn ⟨.ub, .ub fun h => hn ⟨_, .ok h⟩⟩

/-! ## Agreement of the interpreters with the relations (§20.3 ¶3) -/

/-- Soundness of `read`: its result is an outcome of `ReadStep` (§20.1, §20.3 ¶3). -/
theorem read_sound {ObR : ReadObl Ty} {ac : Access} {t : Ty} {s : State}
    {hs : ObR.stat s ac t} {o : ReadOutcome} (h : read ObR ac t s hs = o) :
    ReadStep ObR.toSpec ac t s o := by
  subst h
  unfold read
  split
  · next a ha =>
    split
    · next hc => exact .ok ha ⟨hc.1, hc.2, hs⟩
    · next hc => exact .ub fun ⟨h1, h2, _⟩ => hc ⟨h1, h2⟩
  · next ha => exact .ub fun ⟨⟨b, hb, _⟩, _⟩ => by rw [ha] at hb; cases hb

/-- Completeness of `read`: every outcome of `ReadStep` is the result of `read`, for every
proof of the static part (§20.1, §20.3 ¶3). -/
theorem read_complete {ObR : ReadObl Ty} {ac : Access} {t : Ty} {s : State}
    {o : ReadOutcome} (h : ReadStep ObR.toSpec ac t s o) (hs : ObR.stat s ac t) :
    read ObR ac t s hs = o := by
  unfold read
  cases h with
  | ok ha hc =>
    split
    · next b hb =>
      rw [ha] at hb
      cases hb
      exact ite_eq_left ⟨hc.1, hc.2.1⟩
    · next hb => rw [ha] at hb; cases hb
  | ub hc =>
    split
    · exact ite_eq_right fun ⟨h1, h2⟩ => hc ⟨h1, h2, hs⟩
    · rfl

/-- Soundness of `write` (§20.1, §20.3 ¶3). -/
theorem write_sound {ObW : WriteObl Ty} {ac : Access} {t : Ty} {w : Nat → UInt8 × Option Nat}
    {s : State} {hs : ObW.stat s ac t w} {o : Outcome} (h : write ObW ac t w s hs = o) :
    WriteStep ObW.toSpec ac t w s o := by
  subst h
  unfold write
  split
  · next hc => exact .ok ⟨hc.1, hc.2, hs⟩
  · next hc => exact .ub fun ⟨h1, h2, _⟩ => hc ⟨h1, h2⟩

/-- Completeness of `write`, for every proof of the static part (§20.1, §20.3 ¶3). -/
theorem write_complete {ObW : WriteObl Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s : State} {o : Outcome}
    (h : WriteStep ObW.toSpec ac t w s o) (hs : ObW.stat s ac t w) :
    write ObW ac t w s hs = o := by
  unfold write
  cases h with
  | ok h => exact ite_eq_left ⟨h.1, h.2.1⟩
  | ub h => exact ite_eq_right fun ⟨h1, h2⟩ => h ⟨h1, h2, hs⟩

end Theorems

/-- Soundness of `dealloc` (§20.1, §20.3 ¶3). -/
theorem dealloc_sound {C : Nat → Nat → Prop} [DecidableRel C] {id auth : Nat} {s : State}
    {o : Outcome} (h : dealloc C id auth s = o) : DeallocStep C id auth s o := by
  subst h
  unfold dealloc
  split
  · next hc => exact .ok hc
  · next hc => exact .ub hc

/-- Completeness of `dealloc` (§20.1, §20.3 ¶3). -/
theorem dealloc_complete {C : Nat → Nat → Prop} [DecidableRel C] {id auth : Nat} {s : State}
    {o : Outcome} (h : DeallocStep C id auth s o) : dealloc C id auth s = o := by
  unfold dealloc
  cases h with
  | ok h => exact ite_eq_left h
  | ub h => exact ite_eq_right h

/-- Soundness of `alloc` on states satisfying `WF` (§9 ¶11, §20.1, §20.3 ¶3). -/
theorem alloc_sound {space base size align : Nat} {freeAuth : Option Nat} {s : State}
    {hwf : WF s} {o : Outcome} (h : alloc space base size align freeAuth s hwf = o) :
    AllocStep space base size align freeAuth s o := by
  subst h
  unfold alloc
  split
  · next hc => exact .ok ((allocPreDec_iff hwf).1 hc)
  · next hc => exact .ub (mt (allocPreDec_iff hwf).2 hc)

/-- Completeness of `alloc`, for every proof of `WF` (§9 ¶11, §20.1, §20.3 ¶3). -/
theorem alloc_complete {space base size align : Nat} {freeAuth : Option Nat} {s : State}
    {o : Outcome} (h : AllocStep space base size align freeAuth s o) (hwf : WF s) :
    alloc space base size align freeAuth s hwf = o := by
  unfold alloc
  cases h with
  | ok h => exact ite_eq_left ((allocPreDec_iff hwf).2 h)
  | ub h => exact ite_eq_right (mt (allocPreDec_iff hwf).1 h)

section Domain

variable {Ty : Type}

/-- On the interpreter's domain the raw read has an outcome, computed by `read` (§20.1 ¶3). -/
theorem ReadStep_total_on (ObR : ReadObl Ty) (ac : Access) (t : Ty) (s : State)
    (hs : ObR.stat s ac t) : ∃ o, ReadStep ObR.toSpec ac t s o :=
  ⟨_, read_sound (hs := hs) rfl⟩

/-- On the interpreter's domain the raw write has an outcome, computed by `write`
(§20.1 ¶3). -/
theorem WriteStep_total_on (ObW : WriteObl Ty) (ac : Access) (t : Ty)
    (w : Nat → UInt8 × Option Nat) (s : State) (hs : ObW.stat s ac t w) :
    ∃ o, WriteStep ObW.toSpec ac t w s o :=
  ⟨_, write_sound (hs := hs) rfl⟩

end Domain

/-- With decidable compatibility the raw deallocation has an outcome, computed by
`dealloc` (§20.1 ¶3). -/
theorem DeallocStep_total_on (C : Nat → Nat → Prop) [DecidableRel C] (id auth : Nat)
    (s : State) : ∃ o, DeallocStep C id auth s o :=
  ⟨_, dealloc_sound rfl⟩

/-- On states satisfying `WF` the raw creation has an outcome, computed by `alloc`
(§20.1 ¶3). -/
theorem AllocStep_total_on (space base size align : Nat) (freeAuth : Option Nat) (s : State)
    (hwf : WF s) : ∃ o, AllocStep space base size align freeAuth s o :=
  ⟨_, alloc_sound (hwf := hwf) rfl⟩

/-! ## Effects: frame and invariants (§9, §13, §16 ¶2–¶3, §17 ¶3, §20.2 ¶2) -/

/-- Entry of the written allocation after the write effect (§16 ¶2). -/
theorem State.write_allocs_self (s : State) (ac : Access) (w : Nat → UInt8 × Option Nat) :
    (s.write ac w).allocs ac.prov =
      (s.allocs ac.prov).map (fun a => a.write (ac.addr - a.base) ac.len w) := by
  dsimp only [State.write]
  exact ite_eq_left rfl

/-- Entry of the deallocated allocation after the deallocation effect (§17 ¶3). -/
theorem State.dealloc_allocs_self (s : State) (id : Nat) :
    (s.dealloc id).allocs id = (s.allocs id).map (fun a => { a with live := false }) := by
  dsimp only [State.dealloc]
  exact ite_eq_left rfl

/-- Entry of the new allocation after the creation effect (§9 ¶11, §10 ¶5). -/
theorem State.alloc_allocs_self (s : State) (space base size align : Nat)
    (freeAuth : Option Nat) :
    (s.alloc space base size align freeAuth).allocs s.next =
      some { space, base, size, align, live := true, bytes := fun _ => .uninit, freeAuth } := by
  dsimp only [State.alloc]
  exact ite_eq_left rfl

/-- Inside the written range, offset `off + i` holds the `i`-th written byte with its value
and provenance (§16 ¶2). -/
theorem Alloc.write_bytes_in (a : Alloc) {off len : Nat} (w : Nat → UInt8 × Option Nat)
    {i : Nat} (hi : i < len) : (a.write off len w).bytes (off + i) = .init (w i).1 (w i).2 := by
  simp only [Alloc.write]
  rw [ite_eq_left ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩, Nat.add_sub_cancel_left]

/-- Outside the written range, bytes are unchanged (§16 ¶3). -/
theorem Alloc.write_bytes_out (a : Alloc) {off len : Nat} (w : Nat → UInt8 × Option Nat)
    {j : Nat} (hj : ¬ (off ≤ j ∧ j < off + len)) : (a.write off len w).bytes j = a.bytes j := by
  simp only [Alloc.write]
  exact ite_eq_right hj

/-- Freshness is preserved by the write effect (§9 ¶7, §13 ¶3). -/
theorem write_wf {s : State} (hwf : WF s) (ac : Access) (w : Nat → UInt8 × Option Nat) :
    WF (s.write ac w) := by
  intro i hi
  simp only [State.write, hwf i hi]
  split <;> rfl

/-- Freshness is preserved by the deallocation effect (§9 ¶7, §13 ¶3). -/
theorem dealloc_wf {s : State} (hwf : WF s) (id : Nat) : WF (s.dealloc id) := by
  intro i hi
  simp only [State.dealloc, hwf i hi]
  split <;> rfl

/-- Freshness is preserved by the creation effect (§9 ¶7, §13 ¶1). -/
theorem alloc_wf {s : State} (hwf : WF s) (space base size align : Nat)
    (freeAuth : Option Nat) : WF (s.alloc space base size align freeAuth) := by
  intro i hi
  have hi' : s.next + 1 ≤ i := hi
  have hne : i ≠ s.next := fun e => by rw [e] at hi'; exact Nat.not_succ_le_self _ hi'
  simp only [State.alloc]
  rw [ite_eq_right hne]
  exact hwf i (Nat.le_of_succ_le hi')

/-- A step that makes no allocation live and keeps space, base and extent of every
allocation that stays live preserves live disjointness (§9 ¶3). -/
theorem LiveDisjoint.of_fields {s s' : State} (hd : LiveDisjoint s)
    (h : ∀ i a, s'.allocs i = some a → a.live = true →
      ∃ a₀, s.allocs i = some a₀ ∧ a₀.live = true ∧ a₀.space = a.space ∧
        a₀.base = a.base ∧ a₀.size = a.size) :
    LiveDisjoint s' := by
  intro i j a b hij ha hb hla hlb hsp
  obtain ⟨a₀, ha₀, hla₀, hs₁, hb₁, hz₁⟩ := h i a ha hla
  obtain ⟨b₀, hb₀, hlb₀, hs₂, hb₂, hz₂⟩ := h j b hb hlb
  have := hd i j a₀ b₀ hij ha₀ hb₀ hla₀ hlb₀ (by rw [hs₁, hs₂, hsp])
  rw [hb₁, hz₁, hb₂, hz₂] at this
  exact this

/-- Live disjointness is preserved by the write effect (§9 ¶3). -/
theorem liveDisjoint_write {s : State} (hd : LiveDisjoint s) (ac : Access)
    (w : Nat → UInt8 × Option Nat) : LiveDisjoint (s.write ac w) :=
  hd.of_fields fun i a ha hla => by
    simp only [State.write] at ha
    split at ha
    · obtain ⟨a₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 ha
      exact ⟨a₀, h₀, hla, rfl, rfl, rfl⟩
    · exact ⟨a, ha, hla, rfl, rfl, rfl⟩

/-- Live disjointness is preserved by the deallocation effect (§9 ¶3). -/
theorem liveDisjoint_dealloc {s : State} (hd : LiveDisjoint s) (id : Nat) :
    LiveDisjoint (s.dealloc id) :=
  hd.of_fields fun i a ha hla => by
    simp only [State.dealloc] at ha
    split at ha
    · obtain ⟨a₀, -, rfl⟩ := Option.map_eq_some_iff.1 ha
      exact nomatch hla
    · exact ⟨a, ha, hla, rfl, rfl, rfl⟩

/-- Live disjointness is preserved by a creation satisfying its preconditions (§9 ¶3,
§9 ¶11). -/
theorem liveDisjoint_alloc {s : State} (hd : LiveDisjoint s) {space base size align : Nat}
    (hp : AllocPre s space base size align) (freeAuth : Option Nat) :
    LiveDisjoint (s.alloc space base size align freeAuth) := by
  obtain ⟨-, -, -, -, hdis⟩ := hp
  intro i j a b hij ha hb hla hlb hsp
  simp only [State.alloc] at ha hb
  by_cases hi : i = s.next <;> by_cases hj : j = s.next
  · exact absurd (hi.trans hj.symm) hij
  · rw [ite_eq_left hi] at ha
    rw [ite_eq_right hj] at hb
    cases ha
    exact fun x h1 h2 h3 h4 => hdis j b hb hlb hsp.symm x h3 h4 h1 h2
  · rw [ite_eq_right hi] at ha
    rw [ite_eq_left hj] at hb
    cases hb
    exact hdis i a ha hla hsp
  · rw [ite_eq_right hi] at ha
    rw [ite_eq_right hj] at hb
    exact hd i j a b hij ha hb hla hlb hsp

/-- Alignment is preserved by the write effect (§9 ¶4). -/
theorem aligned_write {s : State} (h : Aligned s) (ac : Access) (w : Nat → UInt8 × Option Nat) :
    Aligned (s.write ac w) := by
  intro i a ha
  simp only [State.write] at ha
  split at ha
  · obtain ⟨a₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact h i a₀ h₀
  · exact h i a ha

/-- Alignment is preserved by the deallocation effect (§9 ¶4). -/
theorem aligned_dealloc {s : State} (h : Aligned s) (id : Nat) : Aligned (s.dealloc id) := by
  intro i a ha
  simp only [State.dealloc] at ha
  split at ha
  · obtain ⟨a₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 ha
    exact h i a₀ h₀
  · exact h i a ha

/-- Alignment is preserved by a creation satisfying its preconditions (§9 ¶4, §9 ¶11). -/
theorem aligned_alloc {s : State} (h : Aligned s) {space base size align : Nat}
    (hp : AllocPre s space base size align) (freeAuth : Option Nat) :
    Aligned (s.alloc space base size align freeAuth) := by
  obtain ⟨-, h0, h2, hm, -⟩ := hp
  intro i a ha
  simp only [State.alloc] at ha
  split at ha
  · cases ha
    exact ⟨h0, h2, hm⟩
  · exact h i a ha

section StepTheorems

variable {Ty : Type}

/-- An `ok` raw write preserves admissibility (§9 ¶8, §20.2 ¶2). -/
theorem WriteStep_admissible {ObW : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s s' : State} (h : WriteStep ObW ac t w s (.ok s'))
    (hs : Admissible s) : Admissible s' := by
  obtain ⟨-, rfl⟩ := WriteStep_ok_iff.1 h
  exact ⟨write_wf hs.wf ac w, liveDisjoint_write hs.disjoint ac w, aligned_write hs.aligned ac w⟩

/-- An `ok` raw deallocation preserves admissibility (§9 ¶8, §20.2 ¶2). -/
theorem DeallocStep_admissible {C : Nat → Nat → Prop} {id auth : Nat} {s s' : State}
    (h : DeallocStep C id auth s (.ok s')) (hs : Admissible s) : Admissible s' := by
  obtain ⟨-, rfl⟩ := DeallocStep_ok_iff.1 h
  exact ⟨dealloc_wf hs.wf id, liveDisjoint_dealloc hs.disjoint id,
    aligned_dealloc hs.aligned id⟩

/-- An `ok` raw creation preserves admissibility (§9 ¶8, §9 ¶11, §20.2 ¶2). -/
theorem AllocStep_admissible {space base size align : Nat} {freeAuth : Option Nat}
    {s s' : State} (h : AllocStep space base size align freeAuth s (.ok s'))
    (hs : Admissible s) : Admissible s' := by
  obtain ⟨hp, rfl⟩ := AllocStep_ok_iff.1 h
  exact ⟨alloc_wf hs.wf space base size align freeAuth, liveDisjoint_alloc hs.disjoint hp freeAuth,
    aligned_alloc hs.aligned hp freeAuth⟩

/-- Every `ok` step preserves admissibility (§9 ¶8, §20.2 ¶2). -/
theorem Step.admissible {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {op : Op Ty} {s s' : State} (h : Step C ObR ObW op s s') (hs : Admissible s) :
    Admissible s' := by
  cases h with
  | read _ => exact hs
  | write h => exact WriteStep_admissible h hs
  | dealloc h => exact DeallocStep_admissible h hs
  | alloc h => exact AllocStep_admissible h hs

/-- Every state of an execution from an admissible initial state is admissible
(§9 ¶8, §9 ¶9). -/
theorem Exec.admissible {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {ops : List (Op Ty)} {s₀ s : State} (h : Exec C ObR ObW ops s₀ s) (h₀ : Admissible s₀) :
    Admissible s := by
  induction h with
  | nil => exact h₀
  | cons hs _ ih => exact ih (hs.admissible h₀)

/-- Every state reachable from an admissible initial state is admissible (§9 ¶9). -/
theorem Reachable.admissible {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty}
    {ObW : WriteOblSpec Ty} {s₀ s : State} (h : Reachable C ObR ObW s₀ s)
    (h₀ : Admissible s₀) : Admissible s :=
  let ⟨_, he⟩ := h
  he.admissible h₀

/-- Frame of an `ok` raw write (§16 ¶3, §13 ¶3): other allocations unchanged; in the target
only bytes change, and only inside the written range; the counter is unchanged. -/
theorem WriteStep_frame {ObW : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s s' : State} (h : WriteStep ObW ac t w s (.ok s')) :
    (∀ i, i ≠ ac.prov → s'.allocs i = s.allocs i) ∧
    (∃ a a', s.allocs ac.prov = some a ∧ s'.allocs ac.prov = some a' ∧
      { a' with bytes := a.bytes } = a ∧
      ∀ j, ¬ (ac.addr - a.base ≤ j ∧ j < ac.addr - a.base + ac.len) → a'.bytes j = a.bytes j) ∧
    s'.next = s.next := by
  obtain ⟨⟨⟨a, ha, -⟩, -⟩, rfl⟩ := WriteStep_ok_iff.1 h
  refine ⟨fun i hi => by simp only [State.write]; exact ite_eq_right hi,
    ⟨a, a.write (ac.addr - a.base) ac.len w, ha, ?_, rfl,
      fun j hj => Alloc.write_bytes_out a w hj⟩, rfl⟩
  rw [State.write_allocs_self, ha]
  rfl

/-- Frame of an `ok` raw deallocation (§17 ¶3, §13): other allocations unchanged; the target
only becomes dead and stays registered; the counter is unchanged. -/
theorem DeallocStep_frame {C : Nat → Nat → Prop} {id auth : Nat} {s s' : State}
    (h : DeallocStep C id auth s (.ok s')) :
    (∀ i, i ≠ id → s'.allocs i = s.allocs i) ∧
    (∃ a, s.allocs id = some a ∧ s'.allocs id = some { a with live := false }) ∧
    s'.next = s.next := by
  obtain ⟨⟨a, ha, -⟩, rfl⟩ := DeallocStep_ok_iff.1 h
  refine ⟨fun i hi => by simp only [State.dealloc]; exact ite_eq_right hi, ⟨a, ha, ?_⟩, rfl⟩
  rw [State.dealloc_allocs_self, ha]
  rfl

/-- Frame of an `ok` raw creation (§13 ¶3, §9 ¶11, §10 ¶5): the identity `s.next` was
unregistered, every other entry is unchanged, the new allocation is live and wholly
uninitialized, and the counter advances. -/
theorem AllocStep_frame {space base size align : Nat} {freeAuth : Option Nat} {s s' : State}
    (h : AllocStep space base size align freeAuth s (.ok s')) :
    s.allocs s.next = none ∧ (∀ i, i ≠ s.next → s'.allocs i = s.allocs i) ∧
    s'.allocs s.next =
      some { space, base, size, align, live := true, bytes := fun _ => .uninit, freeAuth } ∧
    s'.next = s.next + 1 := by
  obtain ⟨hp, rfl⟩ := AllocStep_ok_iff.1 h
  exact ⟨hp.1, fun i hi => by simp only [State.alloc]; exact ite_eq_right hi,
    State.alloc_allocs_self s space base size align freeAuth, rfl⟩

/-! ## Liveness, invalidation, identities across executions (§13, §15.1, §16.1, §17) -/

/-- An `ok` raw read resolves to a live allocation (§15.1). -/
theorem read_requires_live {ObR : ReadOblSpec Ty} {ac : Access} {t : Ty} {s : State}
    {v : List AByte} (h : ReadStep ObR ac t s (.ok v)) :
    ∃ a, s.allocs ac.prov = some a ∧ a.live = true :=
  let ⟨⟨⟨a, ha, hl, _⟩, _⟩, _⟩ := ReadStep_ok_iff.1 h
  ⟨a, ha, hl⟩

/-- An `ok` raw write resolves to a live allocation (§16.1). -/
theorem write_requires_live {ObW : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s s' : State} (h : WriteStep ObW ac t w s (.ok s')) :
    ∃ a, s.allocs ac.prov = some a ∧ a.live = true :=
  let ⟨⟨⟨a, ha, hl, _⟩, _⟩, _⟩ := WriteStep_ok_iff.1 h
  ⟨a, ha, hl⟩

/-- A raw read through the provenance of a dead allocation is `ub` (§15.1, §17 ¶3). -/
theorem ReadStep_dead {R : ReadOblSpec Ty} {ac : Access} {t : Ty} {s : State} {a : Alloc}
    {o : ReadOutcome} (ha : s.allocs ac.prov = some a) (hd : a.live = false)
    (h : ReadStep R ac t s o) : o = .ub := by
  cases h with
  | ok _ hc =>
    obtain ⟨b, hb, hl, _⟩ := hc.1
    rw [ha] at hb
    cases hb
    rw [hd] at hl
    exact nomatch hl
  | ub => rfl

/-- A raw write through the provenance of a dead allocation is `ub` (§16.1, §17 ¶3). -/
theorem WriteStep_dead {W : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s : State} {a : Alloc} {o : Outcome}
    (ha : s.allocs ac.prov = some a) (hd : a.live = false) (h : WriteStep W ac t w s o) :
    o = .ub := by
  cases h with
  | ok hc =>
    obtain ⟨b, hb, hl, _⟩ := hc.1
    rw [ha] at hb
    cases hb
    rw [hd] at hl
    exact nomatch hl
  | ub => rfl

/-- A raw deallocation of a dead allocation is `ub` (§17.1, §17 ¶3). -/
theorem DeallocStep_dead {C : Nat → Nat → Prop} {id auth : Nat} {s : State} {a : Alloc}
    {o : Outcome} (ha : s.allocs id = some a) (hd : a.live = false)
    (h : DeallocStep C id auth s o) : o = .ub := by
  cases h with
  | ok hc =>
    obtain ⟨b, hb, hl, _⟩ := hc
    rw [ha] at hb
    cases hb
    rw [hd] at hl
    exact nomatch hl
  | ub => rfl

/-- An `ok` step that neither writes through `i` nor deallocates `i` leaves the registered
entry `i` unchanged (§13 ¶3, §16 ¶3, §17 ¶3). -/
theorem Step.keeps {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {op : Op Ty} {s s' : State} (h : Step C ObR ObW op s s') {i : Nat} {a : Alloc}
    (hk : op.KeepsAlloc i) (ha : s.allocs i = some a) : s'.allocs i = some a := by
  cases h with
  | read _ => exact ha
  | @write ac _ w _ _ hw =>
    obtain ⟨-, rfl⟩ := WriteStep_ok_iff.1 hw
    have hk : ac.prov ≠ i := hk
    simp only [State.write]
    rw [ite_eq_right (Ne.symm hk)]
    exact ha
  | @dealloc id _ _ _ hd =>
    obtain ⟨-, rfl⟩ := DeallocStep_ok_iff.1 hd
    have hk : id ≠ i := hk
    simp only [State.dealloc]
    rw [ite_eq_right (Ne.symm hk)]
    exact ha
  | alloc hal =>
    obtain ⟨hp, rfl⟩ := AllocStep_ok_iff.1 hal
    have hne : i ≠ s.next := fun e => by rw [e, hp.1] at ha; cases ha
    simp only [State.alloc]
    rw [ite_eq_right hne]
    exact ha

/-- No `ok` step writes through or deallocates a dead allocation (§16.1, §17.1). -/
theorem Step.keepsAlloc_of_dead {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty}
    {ObW : WriteOblSpec Ty} {op : Op Ty} {s s' : State} (h : Step C ObR ObW op s s') {i : Nat}
    {a : Alloc} (ha : s.allocs i = some a) (hd : a.live = false) : op.KeepsAlloc i := by
  cases h with
  | read _ => trivial
  | @write ac _ _ _ _ hw =>
    show ac.prov ≠ i
    intro e
    rw [← e] at ha
    exact nomatch WriteStep_dead ha hd hw
  | @dealloc id _ _ _ hdl =>
    show id ≠ i
    intro e
    rw [← e] at ha
    exact nomatch DeallocStep_dead ha hd hdl
  | alloc _ => trivial

/-- An `ok` step keeps every registered identity registered (§13 ¶1). -/
theorem Step.registered {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {op : Op Ty} {s s' : State} (h : Step C ObR ObW op s s') {i : Nat} {a : Alloc}
    (ha : s.allocs i = some a) : ∃ a', s'.allocs i = some a' := by
  cases h with
  | read _ => exact ⟨a, ha⟩
  | @write ac _ w _ _ hw =>
    obtain ⟨-, rfl⟩ := WriteStep_ok_iff.1 hw
    simp only [State.write]
    split
    · exact ⟨_, by rw [ha]; rfl⟩
    · exact ⟨a, ha⟩
  | @dealloc id _ _ _ hd =>
    obtain ⟨-, rfl⟩ := DeallocStep_ok_iff.1 hd
    simp only [State.dealloc]
    split
    · exact ⟨_, by rw [ha]; rfl⟩
    · exact ⟨a, ha⟩
  | alloc hal => exact ⟨a, (Step.alloc (C := C) (ObR := ObR) (ObW := ObW) hal).keeps trivial ha⟩

/-- Along an execution whose operations neither write through `i` nor deallocate `i`, the
registered entry `i` is unchanged (§13 ¶3, §16 ¶3, §16 ¶5). -/
theorem Exec.keeps {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {ops : List (Op Ty)} {s s' : State} (h : Exec C ObR ObW ops s s') {i : Nat} {a : Alloc}
    (hk : ∀ op ∈ ops, op.KeepsAlloc i) (ha : s.allocs i = some a) : s'.allocs i = some a := by
  induction h with
  | nil => exact ha
  | cons hs _ ih =>
    exact ih (fun op hop => hk op (List.Mem.tail _ hop)) (hs.keeps (hk _ (List.Mem.head _)) ha)

/-- A dead allocation stays registered and dead, unchanged, in every later state of an
execution (§13 ¶1). -/
theorem dead_persists {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {ops : List (Op Ty)} {s s' : State} (h : Exec C ObR ObW ops s s') {i : Nat} {a : Alloc}
    (ha : s.allocs i = some a) (hd : a.live = false) : s'.allocs i = some a := by
  induction h with
  | nil => exact ha
  | cons hs _ ih => exact ih (hs.keeps (hs.keepsAlloc_of_dead ha hd) ha)

/-- A registered identity stays registered in every later state of an execution
(§13 ¶1). -/
theorem Exec.registered {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {ops : List (Op Ty)} {s s' : State} (h : Exec C ObR ObW ops s s') {i : Nat} {a : Alloc}
    (ha : s.allocs i = some a) : ∃ a', s'.allocs i = some a' := by
  induction h generalizing a with
  | nil => exact ⟨a, ha⟩
  | cons hs _ ih =>
    obtain ⟨a', ha'⟩ := hs.registered ha
    exact ih ha'

/-- An identity registered at some point of an execution is never assigned again by a later
creation (§13 ¶1). -/
theorem alloc_identity_never_reused {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty}
    {ObW : WriteOblSpec Ty} {ops : List (Op Ty)} {s s' s'' : State}
    (h : Exec C ObR ObW ops s s') {i : Nat} {a : Alloc} (ha : s.allocs i = some a)
    {space base size align : Nat} {freeAuth : Option Nat}
    (hal : AllocStep space base size align freeAuth s' (.ok s'')) : i ≠ s'.next := by
  intro e
  obtain ⟨a', ha'⟩ := h.registered ha
  rw [e, (AllocStep_frame hal).1] at ha'
  cases ha'

/-- After an `ok` raw deallocation of `i`, in every later state of an execution, every
raw read and every raw write through provenance `i` is `ub` (§17 ¶3, §13 ¶2). -/
theorem dealloc_invalidates {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty}
    {ObW : WriteOblSpec Ty} {i auth : Nat} {s s₁ s₂ : State} {ops : List (Op Ty)}
    (hd : DeallocStep C i auth s (.ok s₁)) (he : Exec C ObR ObW ops s₁ s₂) {ac : Access}
    (hp : ac.prov = i) :
    (∀ (R : ReadOblSpec Ty) (t : Ty) (o : ReadOutcome), ReadStep R ac t s₂ o → o = .ub) ∧
    (∀ (W : WriteOblSpec Ty) (t : Ty) (w : Nat → UInt8 × Option Nat) (o : Outcome),
      WriteStep W ac t w s₂ o → o = .ub) := by
  obtain ⟨-, ⟨a, -, ha⟩, -⟩ := DeallocStep_frame hd
  have h₂ : s₂.allocs ac.prov = some { a with live := false } := hp ▸ dead_persists he ha rfl
  exact ⟨fun _ _ _ hr => ReadStep_dead h₂ rfl hr, fun _ _ _ _ hw => WriteStep_dead h₂ rfl hw⟩

/-- No double free: after an `ok` raw deallocation of `i`, every raw deallocation of `i`
in a later state of an execution is `ub`, whatever the authority and compatibility relation
(§17 ¶3). -/
theorem no_double_free {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {i auth : Nat} {s s₁ s₂ : State} {ops : List (Op Ty)}
    (hd : DeallocStep C i auth s (.ok s₁)) (he : Exec C ObR ObW ops s₁ s₂) :
    ∀ (C' : Nat → Nat → Prop) (auth' : Nat) (o : Outcome), DeallocStep C' i auth' s₂ o → o = .ub := by
  obtain ⟨-, ⟨a, -, ha⟩, -⟩ := DeallocStep_frame hd
  exact fun _ _ _ h => DeallocStep_dead (dead_persists he ha rfl) rfl h

/-- Reuse does not restore: after an `ok` raw deallocation of `i` and an `ok` raw
creation, possibly at the same base, raw reads and writes through provenance `i` stay `ub`
in every later state (§13 ¶2, §12 ¶3). -/
theorem reuse_does_not_restore {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty}
    {ObW : WriteOblSpec Ty} {i auth : Nat} {space base size align : Nat}
    {freeAuth : Option Nat} {s s₁ s₂ s₃ : State} {ops : List (Op Ty)}
    (hd : DeallocStep C i auth s (.ok s₁))
    (hal : AllocStep space base size align freeAuth s₁ (.ok s₂))
    (he : Exec C ObR ObW ops s₂ s₃) {ac : Access} (hp : ac.prov = i) :
    (∀ (R : ReadOblSpec Ty) (t : Ty) (o : ReadOutcome), ReadStep R ac t s₃ o → o = .ub) ∧
    (∀ (W : WriteOblSpec Ty) (t : Ty) (w : Nat → UInt8 × Option Nat) (o : Outcome),
      WriteStep W ac t w s₃ o → o = .ub) :=
  dealloc_invalidates hd (.cons (.alloc hal) he) hp

/-! ## Writes: initialization, read-after-write, non-interference (§16) -/

/-- After an `ok` raw write, the bytes of the written range are initialized with the
written values and provenance (§16 ¶2). -/
theorem write_initializes {ObW : WriteOblSpec Ty} {ac : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s s' : State} (h : WriteStep ObW ac t w s (.ok s')) :
    ∃ a', s'.allocs ac.prov = some a' ∧
      ∀ i, i < ac.len → a'.bytes (ac.addr - a'.base + i) = .init (w i).1 (w i).2 := by
  obtain ⟨⟨⟨a, ha, -⟩, -⟩, rfl⟩ := WriteStep_ok_iff.1 h
  refine ⟨a.write (ac.addr - a.base) ac.len w, ?_, fun i hi => Alloc.write_bytes_in a w hi⟩
  rw [State.write_allocs_self, ha]
  rfl

/-- When the kernel conditions of a read hold, its outcome depends only on the parametric
obligations, and an `ok` outcome carries the bytes of the accessed range (§15, §20.2 ¶1). -/
theorem ReadStep_iff_of_canRead {R : ReadOblSpec Ty} {ac : Access} {t : Ty} {s : State}
    {a : Alloc} (ha : s.allocs ac.prov = some a) (hc : CanRead s ac) (o : ReadOutcome) :
    ReadStep R ac t s o ↔
      (R.dec s ac t ∧ R.stat s ac t) ∧ o = .ok (a.bytesAt (ac.addr - a.base) ac.len) ∨
      ¬ (R.dec s ac t ∧ R.stat s ac t) ∧ o = .ub := by
  constructor
  · intro h
    cases h with
    | ok hb hcd =>
      rw [ha] at hb
      cases hb
      exact Or.inl ⟨⟨hcd.2.1, hcd.2.2⟩, rfl⟩
    | ub hn => exact Or.inr ⟨fun ⟨h1, h2⟩ => hn ⟨hc, h1, h2⟩, rfl⟩
  · rintro (⟨⟨h1, h2⟩, rfl⟩ | ⟨hn, rfl⟩)
    · exact .ok ha ⟨hc, h1, h2⟩
    · exact .ub fun ⟨_, h1, h2⟩ => hn ⟨h1, h2⟩

/-- Read-after-write (§16 ¶5): after an `ok` raw write through `ac`, followed by an execution
with no write through the same provenance and no deallocation of the allocation, an access
`ac'` of the same provenance on any subrange of the written range satisfies the kernel read
conditions, and every raw read through it, at any type and under any obligations, is `ok`
with exactly the corresponding written bytes, provenance included, when the obligations hold,
and `ub` otherwise. -/
theorem write_read_sub {C : Nat → Nat → Prop} {ObR : ReadOblSpec Ty} {ObW : WriteOblSpec Ty}
    {ac ac' : Access} {t : Ty} {w : Nat → UInt8 × Option Nat} {s s₁ s₂ : State}
    {ops : List (Op Ty)} (hw : WriteStep ObW ac t w s (.ok s₁)) (he : Exec C ObR ObW ops s₁ s₂)
    (hk : ∀ op ∈ ops, op.KeepsAlloc ac.prov)
    (hp : ac'.prov = ac.prov) (h1 : ac.addr ≤ ac'.addr)
    (h2 : ac'.addr + ac'.len ≤ ac.addr + ac.len) :
    CanRead s₂ ac' ∧ ∀ (R : ReadOblSpec Ty) (t' : Ty) (o : ReadOutcome),
      ReadStep R ac' t' s₂ o ↔
        (R.dec s₂ ac' t' ∧ R.stat s₂ ac' t') ∧
          o = .ok (writtenBytes w (ac'.addr - ac.addr) ac'.len) ∨
        ¬ (R.dec s₂ ac' t' ∧ R.stat s₂ ac' t') ∧ o = .ub := by
  obtain ⟨⟨⟨a, ha, hl, hsp, -⟩, -⟩, rfl⟩ := WriteStep_ok_iff.1 hw
  have h₁ : (s.write ac w).allocs ac.prov = some (a.write (ac.addr - a.base) ac.len w) := by
    rw [State.write_allocs_self, ha]
    rfl
  have h₂ : s₂.allocs ac'.prov = some (a.write (ac.addr - a.base) ac.len w) :=
    hp ▸ he.keeps hk h₁
  have key : ∀ i, i < ac'.len → (a.write (ac.addr - a.base) ac.len w).bytes
      (ac'.addr - a.base + i) = .init (w (ac'.addr - ac.addr + i)).1
        (w (ac'.addr - ac.addr + i)).2 := by
    intro i hi
    have hb := hsp.1
    have e : ac'.addr - a.base + i = (ac.addr - a.base) + (ac'.addr - ac.addr + i) := by omega
    rw [e, Alloc.write_bytes_in a w (by omega)]
  have hR : CanRead s₂ ac' :=
    ⟨_, h₂, hl, ⟨Nat.le_trans hsp.1 h1, Nat.le_trans h2 hsp.2⟩, fun i hi => by
      show (a.write (ac.addr - a.base) ac.len w).bytes (ac'.addr - a.base + i) ≠ .uninit
      rw [key i hi]
      nofun, Or.inl rfl⟩
  refine ⟨hR, fun R t' o => ?_⟩
  have hv : (a.write (ac.addr - a.base) ac.len w).bytesAt
      (ac'.addr - (a.write (ac.addr - a.base) ac.len w).base) ac'.len =
      writtenBytes w (ac'.addr - ac.addr) ac'.len :=
    List.map_congr_left fun i hi => key i (List.mem_range.1 hi)
  rw [← hv]
  exact ReadStep_iff_of_canRead h₂ hR o

/-- Non-interference (§16 ¶5): an `ok` raw write through `ac` changes neither the kernel read
conditions nor the result of a valid read through `ac'` when `ac'` has another provenance or
a range disjoint from the written range. -/
theorem write_noninterference {ObW : WriteOblSpec Ty} {ac ac' : Access} {t : Ty}
    {w : Nat → UInt8 × Option Nat} {s s' : State} (hw : WriteStep ObW ac t w s (.ok s'))
    (hd : ac'.prov ≠ ac.prov ∨ RangeDisjoint ac.addr ac.len ac'.addr ac'.len) :
    (CanRead s' ac' ↔ CanRead s ac') ∧
      ∀ (R : ReadOblSpec Ty) (t' : Ty) (v v' : List AByte),
        ReadStep R ac' t' s (.ok v) → ReadStep R ac' t' s' (.ok v') → v = v' := by
  obtain ⟨⟨⟨a, ha, -, hsp, -⟩, -⟩, rfl⟩ := WriteStep_ok_iff.1 hw
  by_cases hp : ac'.prov = ac.prov
  · have hr : RangeDisjoint ac.addr ac.len ac'.addr ac'.len := hd.resolve_left (· hp)
    have ha' : s.allocs ac'.prov = some a := hp ▸ ha
    have hwa : (s.write ac w).allocs ac'.prov = some (a.write (ac.addr - a.base) ac.len w) := by
      rw [hp, State.write_allocs_self, ha]
      rfl
    have key : Spatial a ac' → ∀ i, i < ac'.len →
        (a.write (ac.addr - a.base) ac.len w).bytes (ac'.addr - a.base + i) =
          a.bytes (ac'.addr - a.base + i) := by
      intro hs' i hi
      apply Alloc.write_bytes_out
      intro ⟨h1, h2⟩
      obtain ⟨hb, -⟩ := hsp
      obtain ⟨hb', -⟩ := hs'
      exact hr (ac'.addr + i) (by omega) (by omega) (by omega) (by omega)
    refine ⟨⟨?_, ?_⟩, fun R t' v v' h h' => ?_⟩
    · rintro ⟨b, hb, hl', hs', hi', hau⟩
      rw [hwa] at hb
      cases hb
      exact ⟨a, ha', hl', hs', fun i hi => by rw [← key hs' i hi]; exact hi' i hi, hau⟩
    · rintro ⟨b, hb, hl', hs', hi', hau⟩
      rw [ha'] at hb
      cases hb
      exact ⟨_, hwa, hl', hs', fun i hi => by
        show (a.write (ac.addr - a.base) ac.len w).bytes (ac'.addr - a.base + i) ≠ .uninit
        rw [key hs' i hi]
        exact hi' i hi, hau⟩
    · obtain ⟨⟨⟨b, hb, -, hs', -⟩, -⟩, b₁, hb₁, rfl⟩ := ReadStep_ok_iff.1 h
      obtain ⟨-, b₂, hb₂, rfl⟩ := ReadStep_ok_iff.1 h'
      rw [ha'] at hb hb₁
      cases hb
      cases hb₁
      rw [hwa] at hb₂
      cases hb₂
      exact (List.map_congr_left fun i hi => key hs' i (List.mem_range.1 hi)).symm
  · have he : (s.write ac w).allocs ac'.prov = s.allocs ac'.prov := by
      simp only [State.write]
      exact ite_eq_right hp
    refine ⟨by unfold CanRead; rw [he], fun R t' v v' h h' => ?_⟩
    obtain ⟨-, b₁, hb₁, rfl⟩ := ReadStep_ok_iff.1 h
    obtain ⟨-, b₂, hb₂, rfl⟩ := ReadStep_ok_iff.1 h'
    rw [he, hb₁] at hb₂
    cases hb₂
    rfl

end StepTheorems

/-! ## Non-vacuity witnesses -/

namespace Witness

/-- Explicit test instance of the read obligations, both parts `True` (§20.3 ¶1: explicit
predicates, chosen here, not tacitly replaced). -/
def obR : ReadObl Unit :=
  { dec := fun _ _ _ => True, stat := fun _ _ _ => True, decInst := fun _ _ _ => instDecidableTrue }

/-- Explicit test instance of the write obligations, both parts `True` (§20.3 ¶1). -/
def obW : WriteObl Unit :=
  { dec := fun _ _ _ _ => True, stat := fun _ _ _ _ => True,
    decInst := fun _ _ _ _ => instDecidableTrue }

/-- A state with one live allocation, identity `0`, base `96`, size `8`, alignment `8`,
deallocation token `7` (§9 ¶1). -/
def s₁ : State := State.empty.alloc 0 96 8 8 (some 7)

/-- Write access to the first 4 bytes of allocation `0` (§12 ¶1). -/
def acW : Access := ⟨96, 0, 4, .write⟩

/-- Read access to the first 4 bytes of allocation `0` (§12 ¶1). -/
def acR : Access := ⟨96, 0, 4, .read⟩

/-- Written representation: value `i + 1`, no provenance, at position `i` (§10 ¶2). -/
def w₀ : Nat → UInt8 × Option Nat := fun i => (i.toUInt8 + 1, none)

/-- `s₁` after the write of `w₀` through `acW` (§16 ¶2). -/
def s₂ : State := s₁.write acW w₀

/-- Non-vacuity (§9 ¶9, §16, §15, §20.2 ¶1): `s₁` is reached from the empty state, is
admissible and has a live allocation; a raw write through `acW` is `ok` and leads to `s₂`; a
raw read through `acR` in `s₂` is `ok` with the written bytes, by the relation and by the
interpreter. -/
theorem nonvacuous :
    Exec (· = ·) obR.toSpec obW.toSpec [.alloc 0 96 8 8 (some 7), .write acW () w₀]
      State.empty s₂ ∧
    Admissible s₁ ∧ (∃ a, s₁.allocs 0 = some a ∧ a.live = true) ∧
    WriteStep obW.toSpec acW () w₀ s₁ (.ok s₂) ∧
    ReadStep obR.toSpec acR () s₂ (.ok [.init 1 none, .init 2 none, .init 3 none, .init 4 none]) ∧
    read obR acR () s₂ trivial = .ok [.init 1 none, .init 2 none, .init 3 none, .init 4 none] := by
  have hal : AllocStep 0 96 8 8 (some 7) State.empty (.ok s₁) :=
    .ok ((allocPreDec_iff admissible_empty.wf).1 (by decide))
  have hw : WriteStep obW.toSpec acW () w₀ s₁ (.ok s₂) := .ok ⟨by decide, trivial, trivial⟩
  have hr : read obR acR () s₂ trivial =
      .ok [.init 1 none, .init 2 none, .init 3 none, .init 4 none] := by decide
  exact ⟨.cons (.alloc hal) (.cons (.write hw) (.nil _)), AllocStep_admissible hal admissible_empty,
    ⟨_, rfl, rfl⟩, hw, read_sound hr, hr⟩

/-- Non-vacuity of `reuse_does_not_restore` (§13 ¶2): from `s₂`, allocation `0` is
deallocated with a compatible token, then a new allocation is created at the same base `96`;
both steps are `ok`, the new allocation is live at base `96`, and the old read access is
`ub`. -/
theorem reuse_nonvacuous :
    ∃ s₃ s₄, DeallocStep (· = ·) 0 7 s₂ (.ok s₃) ∧ AllocStep 0 96 8 8 none s₃ (.ok s₄) ∧
      (∃ b, s₄.allocs 1 = some b ∧ b.live = true ∧ b.base = 96) ∧
      ReadStep obR.toSpec acR () s₄ .ub := by
  have hd : DeallocStep (· = ·) 0 7 s₂ (.ok (s₂.dealloc 0)) := .ok (by decide)
  have hwf : WF (s₂.dealloc 0) :=
    (DeallocStep_admissible hd (WriteStep_admissible nonvacuous.2.2.2.1 nonvacuous.2.1)).wf
  have hal : AllocStep 0 96 8 8 none (s₂.dealloc 0)
      (.ok ((s₂.dealloc 0).alloc 0 96 8 8 none)) :=
    .ok ((allocPreDec_iff hwf).1 (by decide))
  obtain ⟨o, ho⟩ := ReadStep_total_on obR acR () ((s₂.dealloc 0).alloc 0 96 8 8 none) trivial
  have hub := (reuse_does_not_restore (ObR := obR.toSpec) (ObW := obW.toSpec) hd hal (.nil _)
    (ac := acR) rfl).1 _ _ _ ho
  subst hub
  exact ⟨_, _, hd, hal, ⟨_, rfl, rfl, rfl⟩, ho⟩

-- The read interpreter also runs in compiled code on the witness (§20.3 ¶3).
#guard read obR acR () s₂ trivial = .ok [.init 1 none, .init 2 none, .init 3 none, .init 4 none]

end Witness

end Ern.MemoryModel.Machine
