import Ern.Concurrency.EventModel.Closure

/-!
# Event fragment: graphs, relations, consistency, races

Brief of milestone 4, slice 2 (layer E), task 1 (`formal/reports/spec2-m4-eventmodel.md`): the
"ERN fragment" level of WC5.1 corrigé C53, independent of the authority machine. One atomic unit
`x` and one ordinary leaf `d` per graph; `po`, `rf`, `mo`, `sw` by direct read (WC5.1 corrigé C32
item 1, C48), `hb` (C33), `EventConsistent` (C31) and races (C30, C33). `seq_cst` only acts as a
release and an acquire (C40); no global constraint, no release sequence, no `NoThinAir_RC11`
(C34).

Representation: event `0` is the initial write of `x`, events `i + 1` are the entries of `evs`;
`po` is the listing order of the events of a context; `rf` and `mo` are finite relations given as
lists of pairs, read on the events of the graph.
-/

set_option autoImplicit false

namespace Ern.Concurrency.EventModel

/-! ## Events -/

/-- Memory orders (WC5.1 corrigé C40). -/
inductive MOrd where
  | rlx | rel | acq | acqRel | sc
deriving DecidableEq, Repr

/-- Kinds of the events other than the initial write (WC5.1 corrigé C31, C36, C37, C39):
`read3(d)`, `write3(d)` (no value, C36); `read3(x)` with the value read, `write3(x, v)` (non-atomic
accesses to the atomic unit, C36, C42); `readShared(x, o)` with the value read (C37);
`writeShared(x, v, o)` (C39); a successful RMW on `x` with the value read, the value written and
an order (C39). A failed compare-exchange is a `readShared` (C39). -/
inductive Kind where
  | readD
  | writeD
  | readX (v : Nat)
  | writeX (v : Nat)
  | rsh (o : MOrd) (v : Nat)
  | wsh (o : MOrd) (v : Nat)
  | rmw (o : MOrd) (vr vw : Nat)
deriving DecidableEq, Repr

/-- An event other than the initial write: its context and its kind. -/
structure Ev where
  ctx : Nat
  kind : Kind
deriving DecidableEq, Repr

/-- A finite graph: the value of the initial write of `x` (event `0`, of no context, non-atomic,
exactly one, WC5.1 corrigé C31), the other events (event `i + 1` is `evs[i]`), and the relations
`rf` and `mo` as lists of pairs. -/
structure Graph where
  init : Nat
  evs : List Ev
  rf : List (Nat × Nat)
  mo : List (Nat × Nat)

namespace Graph

variable (g : Graph)

/-- Number of events, the initial write included. -/
def size : Nat := g.evs.length + 1

/-- Event `i`, if it is not the initial write. -/
def ev? (i : Nat) : Option Ev := if i = 0 then none else g.evs[i - 1]?

/-- Kind of event `i`, if it is not the initial write. -/
def kind? (i : Nat) : Option Kind := (g.ev? i).map (·.kind)

/-- Context of event `i`; `none` for the initial write. -/
def ctx? (i : Nat) : Option Nat := (g.ev? i).map (·.ctx)

/-- Event `i` is on the atomic unit `x`. -/
def onX (i : Nat) : Bool :=
  i = 0 || match g.kind? i with
    | some (.readX _) | some (.writeX _) | some (.rsh _ _) | some (.wsh _ _)
    | some (.rmw _ _ _) => true
    | _ => false

/-- Event `i` is on the ordinary leaf `d`. -/
def onD (i : Nat) : Bool :=
  match g.kind? i with
  | some .readD | some .writeD => true
  | _ => false

/-- Event `i` is a modification of `x` (WC5.1 corrigé C31): the initial write, `writeShared`, a
successful RMW, `write3(x, v)`. -/
def isMod (i : Nat) : Bool :=
  i = 0 || match g.kind? i with
    | some (.writeX _) | some (.wsh _ _) | some (.rmw _ _ _) => true
    | _ => false

/-- Event `i` reads `x` (brief, "rf"): `readShared`, the read component of an RMW, `read3(x)`. -/
def isReadX (i : Nat) : Bool :=
  match g.kind? i with
  | some (.readX _) | some (.rsh _ _) | some (.rmw _ _ _) => true
  | _ => false

/-- Event `i` is a successful RMW (WC5.1 corrigé C39). -/
def isRMW (i : Nat) : Bool :=
  match g.kind? i with
  | some (.rmw _ _ _) => true
  | _ => false

/-- Event `i` writes or modifies its location (WC5.1 corrigé C30). -/
def isWrite (i : Nat) : Bool := g.isMod i || g.kind? i == some .writeD

/-- Event `i` is atomic (WC5.1 corrigé C36, C37, C39): `readShared`, `writeShared`, RMW. -/
def isAtomic (i : Nat) : Bool :=
  match g.kind? i with
  | some (.rsh _ _) | some (.wsh _ _) | some (.rmw _ _ _) => true
  | _ => false

/-- Value written by event `i`. -/
def valW (i : Nat) : Option Nat :=
  if i = 0 then some g.init else
  match g.kind? i with
  | some (.writeX v) | some (.wsh _ v) | some (.rmw _ _ v) => some v
  | _ => none

/-- Value read by event `i`. -/
def valR (i : Nat) : Option Nat :=
  match g.kind? i with
  | some (.readX v) | some (.rsh _ v) | some (.rmw _ v _) => some v
  | _ => none

/-- Event `i` is release-capable (WC5.1 corrigé C32 item 1, C40): `writeShared` in `release` or
`seq_cst`, RMW in `release`, `acq_rel` or `seq_cst`. -/
def relCap (i : Nat) : Bool :=
  match g.kind? i with
  | some (.wsh .rel _) | some (.wsh .sc _) | some (.rmw .rel _ _) | some (.rmw .acqRel _ _)
  | some (.rmw .sc _ _) => true
  | _ => false

/-- Event `i` is acquire-capable (WC5.1 corrigé C32 item 1, C40): `readShared` in `acquire` or
`seq_cst`, RMW in `acquire`, `acq_rel` or `seq_cst`. -/
def acqCap (i : Nat) : Bool :=
  match g.kind? i with
  | some (.rsh .acq _) | some (.rsh .sc _) | some (.rmw .acq _ _) | some (.rmw .acqRel _ _)
  | some (.rmw .sc _ _) => true
  | _ => false

end Graph

/-! ## Typing of the orders -/

/-- The order of an event is in its row (WC5.1 corrigé C40). -/
def Kind.OrdOk : Kind → Prop
  | .rsh o _ => o = .rlx ∨ o = .acq ∨ o = .sc
  | .wsh o _ => o = .rlx ∨ o = .rel ∨ o = .sc
  | _ => True

/-- Decidability of `Kind.OrdOk`. -/
instance (k : Kind) : Decidable k.OrdOk := by unfold Kind.OrdOk; split <;> infer_instance

/-- A graph is well typed when every event has an order of its row (WC5.1 corrigé C40). Typing is
not a consistency conjunct. -/
def WellTyped (g : Graph) : Prop := ∀ e ∈ g.evs, e.kind.OrdOk

/-- Decidability of `WellTyped`. -/
instance (g : Graph) : Decidable (WellTyped g) := by unfold WellTyped; infer_instance

/-! ## Relations -/

/-- `po` (brief): events of the same context, in listing order; the initial write has no
context. -/
def PO (g : Graph) (a b : Nat) : Prop :=
  0 < a ∧ a < b ∧ b < g.size ∧ g.ctx? a = g.ctx? b

/-- `rf`, read on the events of the graph. -/
def RF (g : Graph) (w r : Nat) : Prop := (w, r) ∈ g.rf ∧ w < g.size ∧ r < g.size

/-- `mo`, read on the events of the graph. -/
def MO (g : Graph) (a b : Nat) : Prop := (a, b) ∈ g.mo ∧ a < g.size ∧ b < g.size

/-- `sw` by direct read (WC5.1 corrigé C32 item 1, C48): `rf` from a release-capable event to an
acquire-capable event. The initial write and `write3(x, v)` are never release-capable (C31). -/
def SW (g : Graph) (w r : Nat) : Prop := RF g w r ∧ g.relCap w = true ∧ g.acqCap r = true

/-- `po ∪ sw`. -/
def PoSw (g : Graph) (a b : Nat) : Prop := PO g a b ∨ SW g a b

/-- `hb` (brief; WC5.1 corrigé C33): the transitive closure of `po ∪ sw`, plus the initial write
`hb`-before every other event, a convention of the fragment for the state built before the
contexts start. -/
def HB (g : Graph) (a b : Nat) : Prop :=
  Relation.TransGen (PoSw g) a b ∨ (a = 0 ∧ 0 < b ∧ b < g.size)

/-- `rb = (rf⁻¹ ; mo) \ id` (brief). -/
def RB (g : Graph) (a b : Nat) : Prop := (∃ w ∈ List.range g.size, RF g w a ∧ MO g w b) ∧ a ≠ b

/-- `rf ∪ mo ∪ rb`. -/
def EcoBase (g : Graph) (a b : Nat) : Prop := RF g a b ∨ MO g a b ∨ RB g a b

/-- `eco = (rf ∪ mo ∪ rb)⁺` (brief). -/
def ECO (g : Graph) (a b : Nat) : Prop := Relation.TransGen (EcoBase g) a b

/-- Decidability of `PO`. -/
instance (g : Graph) (a b : Nat) : Decidable (PO g a b) := by unfold PO; infer_instance
/-- Decidability of `RF`. -/
instance (g : Graph) (a b : Nat) : Decidable (RF g a b) := by unfold RF; infer_instance
/-- Decidability of `MO`. -/
instance (g : Graph) (a b : Nat) : Decidable (MO g a b) := by unfold MO; infer_instance
/-- Decidability of `SW`. -/
instance (g : Graph) (a b : Nat) : Decidable (SW g a b) := by unfold SW; infer_instance
/-- Decidability of `PoSw`. -/
instance (g : Graph) (a b : Nat) : Decidable (PoSw g a b) := by unfold PoSw; infer_instance
/-- Decidability of `RB`. -/
instance (g : Graph) (a b : Nat) : Decidable (RB g a b) := by unfold RB; infer_instance
/-- Decidability of `EcoBase`. -/
instance (g : Graph) (a b : Nat) : Decidable (EcoBase g a b) := by
  unfold EcoBase; infer_instance

/-- The edges of `po ∪ sw` join events of the graph. -/
theorem poSw_lt {g : Graph} {a b : Nat} (h : PoSw g a b) : a < g.size ∧ b < g.size := by
  rcases h with ⟨_, h2, h3, _⟩ | ⟨⟨_, h1, h2⟩, _⟩
  · exact ⟨Nat.lt_trans h2 h3, h3⟩
  · exact ⟨h1, h2⟩

/-- The edges of `rf ∪ mo ∪ rb` join events of the graph. -/
theorem ecoBase_lt {g : Graph} {a b : Nat} (h : EcoBase g a b) : a < g.size ∧ b < g.size := by
  rcases h with ⟨_, h1, h2⟩ | ⟨_, h1, h2⟩ | ⟨⟨w, -, ⟨_, -, ha⟩, ⟨_, -, hb⟩⟩, -⟩
  · exact ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · exact ⟨ha, hb⟩

/-- A transitive closure of a decidable relation on the events is decidable. -/
def decTransGen (g : Graph) (R : Nat → Nat → Prop) [∀ a b, Decidable (R a b)]
    (hR : ∀ a b, R a b → a < g.size ∧ b < g.size) (a b : Nat) :
    Decidable (Relation.TransGen R a b) :=
  have hR' : ∀ a b, decide (R a b) = true → a < g.size ∧ b < g.size :=
    fun a b h => hR a b (of_decide_eq_true h)
  have heq : (fun a b => decide (R a b) = true) = R := by
    funext a b; exact propext decide_eq_true_iff
  decidable_of_iff (reach g.size (fun a b => decide (R a b)) a b = true)
    (by rw [← transGen_iff_reach hR', heq])

/-- Decidability of the transitive closure of `po ∪ sw`. -/
instance (g : Graph) (a b : Nat) : Decidable (Relation.TransGen (PoSw g) a b) :=
  decTransGen g (PoSw g) (fun _ _ h => poSw_lt h) a b

/-- Decidability of `HB`. -/
instance (g : Graph) (a b : Nat) : Decidable (HB g a b) := by unfold HB; infer_instance

/-- Decidability of `ECO`. -/
instance (g : Graph) (a b : Nat) : Decidable (ECO g a b) :=
  decTransGen g (EcoBase g) (fun _ _ h => ecoBase_lt h) a b

/-! ## `EventConsistent` -/

/-- Conjunct 1, `rf` well formed (brief; WC5.1 corrigé C31): every `rf` edge goes from a
modification of `x` to a read of `x` with the same value, and every read of `x` has exactly one
source. -/
def RfWF (g : Graph) : Prop :=
  (∀ w ∈ List.range g.size, ∀ r ∈ List.range g.size, RF g w r →
      g.isMod w = true ∧ g.isReadX r = true ∧ g.valW w = g.valR r) ∧
    ∀ r ∈ List.range g.size, g.isReadX r = true →
      ∃ w ∈ List.range g.size, RF g w r ∧ ∀ w' ∈ List.range g.size, RF g w' r → w' = w

/-- Conjunct 2 (brief; WC5.1 corrigé C31): `mo` is a strict total order on the modifications of
`x`, the initial write included. -/
def MoTotal (g : Graph) : Prop :=
  (∀ a ∈ List.range g.size, ∀ b ∈ List.range g.size, MO g a b →
      g.isMod a = true ∧ g.isMod b = true) ∧
    (∀ a ∈ List.range g.size, ¬ MO g a a) ∧
    (∀ a ∈ List.range g.size, ∀ b ∈ List.range g.size, ∀ c ∈ List.range g.size,
      MO g a b → MO g b c → MO g a c) ∧
    ∀ a ∈ List.range g.size, ∀ b ∈ List.range g.size, g.isMod a = true → g.isMod b = true →
      a ≠ b → MO g a b ∨ MO g b a

/-- Conjunct 3, atomicity of the RMWs (brief; WC5.1 corrigé C31): the `rf` source of a successful
RMW is its immediate predecessor in `mo`. -/
def RmwAtomic (g : Graph) : Prop :=
  ∀ m ∈ List.range g.size, g.isRMW m = true → ∀ w ∈ List.range g.size, RF g w m →
    MO g w m ∧ ∀ c ∈ List.range g.size, ¬ (MO g w c ∧ MO g c m)

/-- Conjunct 4, coherence (brief): `hb ; eco?` is irreflexive. -/
def Coherent (g : Graph) : Prop :=
  ∀ a ∈ List.range g.size, ¬ HB g a a ∧ ∀ b ∈ List.range g.size, HB g a b → ¬ ECO g b a

/-- Conjunct 5 (brief): `hb` is irreflexive. -/
def HbIrrefl (g : Graph) : Prop := ∀ a ∈ List.range g.size, ¬ HB g a a

/-- `EventConsistent` (brief; WC5.1 corrigé C31, C33): the five conjuncts. -/
def EventConsistent (g : Graph) : Prop :=
  RfWF g ∧ MoTotal g ∧ RmwAtomic g ∧ Coherent g ∧ HbIrrefl g

/-- Decidability of `RfWF`. -/
instance (g : Graph) : Decidable (RfWF g) := by unfold RfWF; infer_instance
/-- Decidability of `MoTotal`. -/
instance (g : Graph) : Decidable (MoTotal g) := by unfold MoTotal; infer_instance
/-- Decidability of `RmwAtomic`. -/
instance (g : Graph) : Decidable (RmwAtomic g) := by unfold RmwAtomic; infer_instance
/-- Decidability of `Coherent`. -/
instance (g : Graph) : Decidable (Coherent g) := by unfold Coherent; infer_instance
/-- Decidability of `HbIrrefl`. -/
instance (g : Graph) : Decidable (HbIrrefl g) := by unfold HbIrrefl; infer_instance
/-- Decidability of `EventConsistent`. -/
instance (g : Graph) : Decidable (EventConsistent g) := by
  unfold EventConsistent; infer_instance

/-! ## Conflicts and races -/

/-- Conflict (brief; WC5.1 corrigé C30): two events of distinct contexts on the same location,
one of them at least a write or a modification. The initial write has no context and is in no
conflict. -/
def Conflict (g : Graph) (a b : Nat) : Prop :=
  g.ctx? a ≠ none ∧ g.ctx? b ≠ none ∧ g.ctx? a ≠ g.ctx? b ∧
    ((g.onX a = true ∧ g.onX b = true) ∨ (g.onD a = true ∧ g.onD b = true)) ∧
    (g.isWrite a = true ∨ g.isWrite b = true)

/-- Race on a pair (brief; WC5.1 corrigé C33): a conflict with a non-atomic member, without `hb`
in either direction. -/
def RaceOn (g : Graph) (a b : Nat) : Prop :=
  Conflict g a b ∧ (g.isAtomic a = false ∨ g.isAtomic b = false) ∧ ¬ HB g a b ∧ ¬ HB g b a

/-- The graph has a race. -/
def Racy (g : Graph) : Prop := ∃ a ∈ List.range g.size, ∃ b ∈ List.range g.size, RaceOn g a b

/-- Decidability of `Conflict`. -/
instance (g : Graph) (a b : Nat) : Decidable (Conflict g a b) := by
  unfold Conflict; infer_instance
/-- Decidability of `RaceOn`. -/
instance (g : Graph) (a b : Nat) : Decidable (RaceOn g a b) := by unfold RaceOn; infer_instance
/-- Decidability of `Racy`. -/
instance (g : Graph) : Decidable (Racy g) := by unfold Racy; infer_instance

end Ern.Concurrency.EventModel
