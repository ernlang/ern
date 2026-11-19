import Ern.ConcurrencyModel.Contract

/-!
# Theorem 10: the event graph (C26–C34, C40, C48)

The event graph of C26–C34 as a declarative object (`formal/DESIGN.md`, Milestone 4, "Semantic
style": the third object, obtained neither from the step relation nor from the memory machine).
Events (C27), the base relations `po`, `rf`, `mo` (C28, C31), `sw` (C32, C48), `hb` and races
(C33), conflicts (C30), and the consistency predicate `EventConsistent` with its seven conjuncts
(C34); the legality of memory orders (C40) is a separate predicate.

The type of events is arbitrary: a graph may be infinite, and no well-foundedness is assumed on
`po`, `rf` or `mo` (C26: "a finite or potentially unbounded trace"). Finiteness is a hypothesis of a
statement only where C34 names it ("For a finite event graph") or where the brief of the tranche
names it.

Formalization hypotheses (retained readings, not rules of the specification):

1. `sw` is exactly the relation of the three sources of C32 (C32; C48: "This is an axiom of the
   event graph"); this formalization declares no other mechanism.
2. An access designates at most one atomic unit (`Acc`). An event accessing several atomic units
   is not represented; the events of a composite step or of an access to several leaves stay open.
3. `po` is total on the events of one context (C28, "the strict order of semantic events within one
   execution context").
4. No map from steps to events is defined.
5. The release sequence of C48 is read as the interval `RSMember`: on a total `mo`, the maximal
   convex set of atomic RMW modifications following the head. What C48 means when `mo` is not well
   founded is the open point on infinite graphs; this reading is not a rule (`RSMember`).

Not proven here, nor anywhere in this tranche: that a graph comes from an execution or that an
execution has a consistent graph; the events of a composite step; the physical classification of
markers and the projection of validity events (`OB-C19`, external part); the compilation of memory
orders and of the no-thin-air rule (`OB-C22`, `OB-C27`); any absence of race.
-/

namespace Ern.ConcurrencyModel.Events

open Ern.ConcurrencyModel (MemOrder)

/-! ## Events (C27) -/

/-- A concrete byte range (C27 `acc`, C30): the bytes `base`, …, `base + len - 1`. -/
structure Range where
  base : Nat
  len : Nat
deriving DecidableEq, Repr

/-- Byte `n` belongs to the range. -/
def Range.Mem (r : Range) (n : Nat) : Prop := r.base ≤ n ∧ n < r.base + r.len

/-- Two concrete byte ranges intersect (C30: "their concrete byte ranges intersect"): some byte
belongs to both. -/
def Range.Inter (r r' : Range) : Prop := ∃ n, r.Mem n ∧ r'.Mem n

/-- The kind of an access (C27): `read`, `write` or `RMW`. -/
inductive Kind where
  | read
  | write
  | rmw
deriving DecidableEq, Repr

/-- The kind has a read component; an RMW counts as a read (C30, C31). -/
def Kind.Reads : Kind → Prop
  | .read | .rmw => True
  | .write => False

/-- The kind has a write component; an RMW counts as a write (C30, C31). -/
def Kind.Writes : Kind → Prop
  | .write | .rmw => True
  | .read => False

/-- The kind of an access that designates a unit, with the value read by its read component and
the value written by its write component (C34.1, C31); an RMW has both components (C30, C31), a
failed CAS is a read (C39). -/
inductive UKind (V : Type) where
  | read (vr : V)
  | write (vw : V)
  | rmw (vr vw : V)
deriving DecidableEq, Repr

/-- The kind of an access designating a unit. -/
def UKind.kind {V : Type} : UKind V → Kind
  | .read _ => .read
  | .write _ => .write
  | .rmw _ _ => .rmw

/-- The `acc` attribute of an event (C27): an access kind, a concrete byte range, an atomicity
classification, and a memory order for an atomic access.

* An atomic access designates exactly one atomic unit and covers its whole range (C30, C31, C38);
  its range is the range of the unit (`Graph.uRange`).
* A non-atomic access may designate a unit: the initial write (C31), an exclusive ordinary access
  (C42); it then covers the whole range of the unit ("range-identity", C31).
* A non-atomic access may designate no unit: it carries its own byte range.

An access designates at most one unit (retained reading 2, a limit of this formalization). -/
inductive Acc (U V : Type) where
  /-- An atomic access of the unit `u` with the memory order `o` (C27, C38, C40). -/
  | atomic (u : U) (o : MemOrder) (k : UKind V)
  /-- A non-atomic access designating the unit `u` (C31, C42). -/
  | unit (u : U) (k : UKind V)
  /-- A non-atomic access of the byte range `r`, designating no unit. -/
  | plain (r : Range) (k : Kind)
deriving DecidableEq, Repr

/-- The role of a `sync` event (C27, C28): the lifecycle markers `spawn(c)`, `start(c)`,
`complete(c)` and `join(c)` of the context `c` (C28), or another event eligible to participate in a
justified `sw` relation (C27), such as a controller operation of the reference mutex. -/
inductive SyncRole (C : Type) where
  | spawn (c : C)
  | start (c : C)
  | complete (c : C)
  | join (c : C)
  | protocol
deriving DecidableEq, Repr

/-- The `validity` attribute (C27): whether storage validity begins or ends, and the storage
identity. -/
structure Validity (S : Type) where
  begins : Bool
  storage : S
deriving DecidableEq, Repr

/-- The cumulative attributes of an event (C27): a `validity` event carries neither `acc` nor
`sync`; any other event carries an optional `acc` and an optional `sync`. An event carrying none of
the three is a pure authority marker. -/
inductive Attrs (C U V S : Type) where
  | validity (v : Validity S)
  | marks (acc : Option (Acc U V)) (sync : Option (SyncRole C))
deriving DecidableEq, Repr

/-- The origin of an event (C27): the index of the abstract transition or library phase that
generates it in the trace, and its position in that transition. This tranche relates it to no
step. -/
structure Origin where
  step : Nat
  pos : Nat
deriving DecidableEq, Repr

/-- An event (C27): its execution context, its origin, its attributes. -/
structure Event (C U V S : Type) where
  ctx : C
  origin : Origin
  attrs : Attrs C U V S
deriving DecidableEq, Repr

/-! ## Graphs (C26, C28, C31) -/

/-- An event graph (C26 item 3): events of an arbitrary type `E` with their attributes, the range
of each atomic unit, and the relations `po`, `rf` and `mo`.

* `po` (C28) is a strict order relating only events of the same context, total on the events of
  each context (retained reading 3).
* `rf` and `mo` (C31) are arbitrary relations: their typing is not in the type of graphs but in the
  conjuncts 1 and 2 of `EventConsistent` (C34.1, C34.2), and the erasure paragraph of C34 makes it
  a premise. A graph where `rf` or `mo` touches a marker is representable, and rejected. -/
structure Graph (E C U V S : Type) where
  ev : E → Event C U V S
  uRange : U → Range
  po : E → E → Prop
  rf : E → E → Prop
  mo : E → E → Prop
  po_irrefl : ∀ a, ¬ po a a
  po_trans : ∀ {a b c}, po a b → po b c → po a c
  po_ctx : ∀ {a b}, po a b → (ev a).ctx = (ev b).ctx
  po_total : ∀ {a b}, (ev a).ctx = (ev b).ctx → a ≠ b → po a b ∨ po b a

/-- A relation is acyclic: its transitive closure is irreflexive. -/
def Acyclic {E : Type} (R : E → E → Prop) : Prop := ∀ a, ¬ Relation.TransGen R a a

/-- The type of events is finite. -/
def Finite (E : Type) : Prop := ∃ l : List E, ∀ e, e ∈ l

namespace Graph

variable {E C U V S : Type} (G : Graph E C U V S)

/-! ## Attributes of the events of a graph (C27) -/

/-- The `acc` attribute of an event, if any (C27). -/
def acc? (e : E) : Option (Acc U V) :=
  match (G.ev e).attrs with
  | .marks a _ => a
  | .validity _ => none

/-- The `sync` attribute of an event, if any (C27). -/
def sync? (e : E) : Option (SyncRole C) :=
  match (G.ev e).attrs with
  | .marks _ s => s
  | .validity _ => none

/-- The context of an event (C27). -/
def ctx (e : E) : C := (G.ev e).ctx

/-- The event carries `acc` (C27). -/
def IsAcc (e : E) : Prop := G.acc? e ≠ none

/-- A pure authority marker (C27, C29): an event carrying none of `acc`, `sync` and `validity`. -/
def Pure (e : E) : Prop := (G.ev e).attrs = .marks none none

/-- The unit designated by an access, if any (C30, C31, C38). -/
def unitOf (e : E) : Option U :=
  match G.acc? e with
  | some (.atomic u _ _) | some (.unit u _) => some u
  | _ => none

/-- The concrete byte range of an access (C27, C30): the range of its unit when it designates one
(C31, C38), its own range otherwise. -/
def range? (e : E) : Option Range :=
  match G.acc? e with
  | some (.atomic u _ _) | some (.unit u _) => some (G.uRange u)
  | some (.plain r _) => some r
  | none => none

/-- The access kind of an event, if it carries `acc` (C27). -/
def kind? (e : E) : Option Kind :=
  match G.acc? e with
  | some (.atomic _ _ k) | some (.unit _ k) => some k.kind
  | some (.plain _ k) => some k
  | none => none

/-- The event is an access with a read component; an RMW counts (C30, C31). -/
def Reads (e : E) : Prop := ∃ k, G.kind? e = some k ∧ k.Reads

/-- The event is an access with a write component; an RMW counts (C30, C31). -/
def Writes (e : E) : Prop := ∃ k, G.kind? e = some k ∧ k.Writes

/-- The event is an RMW (C31, C34.3). -/
def IsRMW (e : E) : Prop := G.kind? e = some .rmw

/-- The event is an atomic access (C27, C33). -/
def Atomic (e : E) : Prop := ∃ u o k, G.acc? e = some (.atomic u o k)

/-- A modification of the unit `u` (C31): an access designating `u` with a write component, atomic
or not (the initial write and an exclusive ordinary write included). -/
def ModOn (e : E) (u : U) : Prop := G.unitOf e = some u ∧ G.Writes e

/-- A read component of an access to the unit `u` (C31, C34.1). -/
def ReadOn (e : E) (u : U) : Prop := G.unitOf e = some u ∧ G.Reads e

/-- An atomic RMW modification of the unit `u` (C31, C48). -/
def AtomicRMWOn (e : E) (u : U) : Prop := ∃ o vr vw, G.acc? e = some (.atomic u o (.rmw vr vw))

/-- The value read by the read component of an access designating a unit (C34.1). -/
def valR (e : E) : Option V :=
  match G.acc? e with
  | some (.atomic _ _ (.read v)) | some (.atomic _ _ (.rmw v _)) => some v
  | some (.unit _ (.read v)) | some (.unit _ (.rmw v _)) => some v
  | _ => none

/-- The value written by the write component of an access designating a unit (C34.1). -/
def valW (e : E) : Option V :=
  match G.acc? e with
  | some (.atomic _ _ (.write v)) | some (.atomic _ _ (.rmw _ v)) => some v
  | some (.unit _ (.write v)) | some (.unit _ (.rmw _ v)) => some v
  | _ => none

/-- A release-capable event of the unit `u` (C32.1, C40): an atomic write or RMW of order
`release`, `acq_rel` or `seq_cst`. -/
def RelCap (e : E) (u : U) : Prop :=
  ∃ o k, G.acc? e = some (.atomic u o k) ∧ k.kind.Writes ∧
    (o = .release ∨ o = .acqRel ∨ o = .seqCst)

/-- An acquire-capable event of the unit `u` (C32.1, C40): an atomic read or RMW of order
`acquire`, `acq_rel` or `seq_cst`. -/
def AcqCap (e : E) (u : U) : Prop :=
  ∃ o k, G.acc? e = some (.atomic u o k) ∧ k.kind.Reads ∧
    (o = .acquire ∨ o = .acqRel ∨ o = .seqCst)

/-- A `seq_cst` atomic access event (C34: "the set of `seq_cst` atomic access events (including
`seq_cst` RMWs)"). -/
def SC (e : E) : Prop := ∃ u k, G.acc? e = some (.atomic u .seqCst k)

/-! ## `sw` (C32, C48) -/

/-- Membership in the release sequence of the head `h` on the unit `u`, **retained reading 5, a
formalization hypothesis**. C48: "beginning with release modification `h` of a given atomic unit,
the release sequence consists of `h` followed by the maximal contiguous `mo` segment of atomic RMW
modifications on that unit. Ordinary atomic stores, including same-thread non-RMW stores, do
**not** extend the sequence."

This formalization reads it as an interval: `m` is a member when `m = h`, or when `m` is an atomic
RMW modification of `u` with `mo(h, m)` and every modification `x` of `u` with `mo(h, x)` and
`mo(x, m)` is an atomic RMW modification of `u`. On a total `mo` it is a convex segment, maximal
(`rsMember_between`, `not_rsMember_after`). What the rule of C48 means when `mo` is not well founded
is open (decision 6 of the tranche, infinite graphs); this definition does not settle it, and the
infinite witness of `EventInfinite` shows where it can give more members than the atomic RMWs
reached from `h` by `rf` chains. A non-atomic write is neither a head nor a member (C31). -/
def RSMember (u : U) (h m : E) : Prop :=
  m = h ∨ (G.AtomicRMWOn m u ∧ G.mo h m ∧
    ∀ x, G.ModOn x u → G.mo h x → G.mo x m → G.AtomicRMWOn x u)

/-- `sw` (C32, retained reading 1): exactly the pairs of the three reference sources.

1. Atomic (C32.1, C48): `h` release-capable and `r` acquire-capable on the same unit, and `r`
   reads by `rf` a member of the release sequence of `h` (`RSMember`, retained reading 5).
2. Context creation (C32.2): `spawn(c)` to `start(c)`.
3. Completion observation (C32.3): `complete(c)` to each `join(c)`; a `join(c)` event is the event
   of a successful join (C28).

No other mechanism is declared (C32: "admissible only under an explicit contract"). -/
def SW (a b : E) : Prop :=
  (∃ u m, G.RelCap a u ∧ G.AcqCap b u ∧ G.RSMember u a m ∧ G.rf m b) ∨
  (∃ c, G.sync? a = some (.spawn c) ∧ G.sync? b = some (.start c)) ∨
  (∃ c, G.sync? a = some (.complete c) ∧ G.sync? b = some (.join c))

/-- `po ∪ sw`. -/
def PoSw (a b : E) : Prop := G.po a b ∨ G.SW a b

/-- `hb := (po ∪ sw)⁺` (C33). -/
def HB (a b : E) : Prop := Relation.TransGen G.PoSw a b

/-! ## Conflicts and races (C30, C33) -/

/-- Two `acc` events conflict (C30): they are of different contexts, their concrete byte ranges
intersect, and at least one is a write, an RMW counting as a read and as a write. -/
def Conflict (a b : E) : Prop :=
  ∃ ra rb, G.range? a = some ra ∧ G.range? b = some rb ∧ G.ctx a ≠ G.ctx b ∧ ra.Inter rb ∧
    (G.Writes a ∨ G.Writes b)

/-- A data race (C33, Spec 1 §18), the four conditions as written: the events belong to distinct
contexts, conflict, include a non-atomic event, and are not ordered by `hb` in either direction. -/
def Race (a b : E) : Prop :=
  G.ctx a ≠ G.ctx b ∧ G.Conflict a b ∧ (¬ G.Atomic a ∨ ¬ G.Atomic b) ∧ ¬ G.HB a b ∧ ¬ G.HB b a

/-! ## The relations of C34 -/

/-- `loc` (C34): the events access the same atomic unit. -/
def Loc (a b : E) : Prop := ∃ u, G.unitOf a = some u ∧ G.unitOf b = some u

/-- `hb|loc := hb ∩ loc` (C34). -/
def HBLoc (a b : E) : Prop := G.HB a b ∧ G.Loc a b

/-- `rb := (rf⁻¹ ; mo) \ id` (C34). -/
def RB (a b : E) : Prop := (∃ w, G.rf w a ∧ G.mo w b) ∧ a ≠ b

/-- `rf ∪ mo ∪ rb`. -/
def EcoBase (a b : E) : Prop := G.rf a b ∨ G.mo a b ∨ G.RB a b

/-- `eco := (rf ∪ mo ∪ rb)⁺` (C34.4). -/
def ECO (a b : E) : Prop := Relation.TransGen G.EcoBase a b

/-- `scb := po ∪ (po ; hb ; po) ∪ hb|loc ∪ mo ∪ rb` (C34). -/
def SCB (a b : E) : Prop :=
  G.po a b ∨ (∃ x y, G.po a x ∧ G.HB x y ∧ G.po y b) ∨ G.HBLoc a b ∨ G.mo a b ∨ G.RB a b

/-- `psc := [SC] ; scb ; [SC]` (C34). -/
def PSC (a b : E) : Prop := G.SC a ∧ G.SCB a b ∧ G.SC b

/-- `po ∪ rf`. -/
def PoRf (a b : E) : Prop := G.po a b ∨ G.rf a b

/-! ## `EventConsistent` (C34) -/

/-- Conjunct 1, `rf` well-formedness (C34.1, C31): `rf` relates only a modification of an atomic
unit to a read component of an access to that same unit; every read component of an access to an
atomic unit has exactly one `rf` source; and the value read is the value that source wrote. -/
def RfWF : Prop :=
  (∀ w r, G.rf w r → ∃ u, G.ModOn w u ∧ G.ReadOn r u) ∧
  (∀ r u, G.ReadOn r u → (∃ w, G.rf w r) ∧ ∀ w w', G.rf w r → G.rf w' r → w = w') ∧
  (∀ w r, G.rf w r → ∃ v, G.valW w = some v ∧ G.valR r = some v)

/-- Conjunct 2, `mo` totality (C34.2, C31): `mo` relates only two modifications of the same atomic
unit; on each atomic unit, it is a strict total order of all the modifications of that unit (the
represented initial write included, as a modification of the unit). -/
def MoTotal : Prop :=
  (∀ a b, G.mo a b → ∃ u, G.ModOn a u ∧ G.ModOn b u) ∧
  ∀ u, (∀ a, G.ModOn a u → ¬ G.mo a a) ∧
    (∀ a b c, G.ModOn a u → G.ModOn b u → G.ModOn c u → G.mo a b → G.mo b c → G.mo a c) ∧
    (∀ a b, G.ModOn a u → G.ModOn b u → a ≠ b → G.mo a b ∨ G.mo b a)

/-- Conjunct 3, RMW atomicity (C34.3, C31): the `rf` source of a successful RMW is its immediate
`mo`-predecessor. -/
def RmwAtomic : Prop :=
  ∀ w r, G.IsRMW r → G.rf w r → G.mo w r ∧ ∀ x, ¬ (G.mo w x ∧ G.mo x r)

/-- Conjunct 4, coherence (C34.4): `hb ; eco?` is irreflexive. -/
def Coherence : Prop := ∀ a b, G.HB a b → ¬ (b = a ∨ G.ECO b a)

/-- Conjunct 5, `hb` irreflexivity (C34.5, C33). -/
def HbIrrefl : Prop := ∀ a, ¬ G.HB a a

/-- Conjunct 6, `NoThinAir_RC11 := acyclic(po ∪ rf)` (C34.6). -/
def NoThinAir : Prop := Acyclic G.PoRf

/-- Conjunct 7, `SCConsistent` (C34.7): `psc` is acyclic. -/
def SCConsistent : Prop := Acyclic G.PSC

/-- `EventConsistent` (C34): the seven conjuncts, in the order of the clause. -/
def EventConsistent : Prop :=
  G.RfWF ∧ G.MoTotal ∧ G.RmwAtomic ∧ G.Coherence ∧ G.HbIrrefl ∧ G.NoThinAir ∧ G.SCConsistent

/-! ## Legality of memory orders (C40) -/

/-- The order of an atomic access is permitted for its kind (C40): a read `relaxed`, `acquire` or
`seq_cst`; a write `relaxed`, `release` or `seq_cst`; an RMW any of the five. -/
def OrderOK : Kind → MemOrder → Prop
  | .read, o => o = .relaxed ∨ o = .acquire ∨ o = .seqCst
  | .write, o => o = .relaxed ∨ o = .release ∨ o = .seqCst
  | .rmw, _ => True

/-- Legality of the memory-order annotations of a graph (C40): a typing condition on events,
separate from the conjuncts of `EventConsistent` (C34, last sentence). -/
def OrderLegal : Prop := ∀ e u o k, G.acc? e = some (.atomic u o k) → OrderOK k.kind o

end Graph

end Ern.ConcurrencyModel.Events
