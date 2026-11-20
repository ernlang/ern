import Ern.ConcurrencyModel.EventGraph

/-!
# Theorem 10e: RC11 on the fence-free fragment, an object of comparison (C34; `OB-C23`, `OB-C26`)

The definitions of this module are **objects of comparison, not rules of ERN** (C34: RC11 "is a
**comparative reference**, not an adopted normative definition of ERN").

Sources:

* `rc11.cat` of herdtools7 7.58: at tag `7.58` of the herdtools7 repository (commit `1ca343e`),
  `herd/libdir/rc11.cat`, 40 lines, SHA-256
  `62a095a30700722d4cf08a5ca4ee5bf6e76466a4c056bea1047c4ea8cd4d6128`. Each definition below is a
  transcription of its line, without the fence factors of `sw` and the fence branches of `psc`;
* for what `rc11.cat` does not say, the herdtools7 source at the same tag (`herd/CAction.ml`,
  `herd/CSem.ml`, `lib/memOrder.ml`, `herd/mem.ml`), which is not part of this formalization and
  was not checked against it: `R` holds the reads, `W` the writes and the initial writes, `IW` the
  initial writes, `A` the events carrying an order annotation; with `-variant normw` an RMW is a
  read and a write related by `rmw`, both in `RMW`, the read carrying the read part of the order and
  the write its write part (`extract_read`, `extract_write`, `cxchg`); a failed CAS is a read;
* for the amended middle term of `scb`, the corrigendum named by C34 (O. Lahav, December 2025):
  `(sb \ rmw) ; hb ; (sb \ rmw)` in place of `sb|≠loc ; hb ; sb|≠loc`.

Nothing here is a claim about herd or about a compiler: the comparison is between definitions
written in Lean, on a declared fragment.

The fragment (`Frag`) is the fence-free fragment with the **two-event** representation of an RMW:
a read and a write related by `rmw`, as herd produces with `-variant normw`. The default one-event
representation of herd, an event both read and write, is **outside** the fragment: this is a limit
of the comparison. Locations are represented by natural numbers.
-/

namespace Ern.ConcurrencyModel.Rc11

open Relation

/-! ## Events -/

/-- The order annotations of `rc11.cat` (`RLX`, `REL`, `ACQ_REL`, `ACQ`, `SC`). -/
inductive Ann where
  | rlx
  | rel
  | acqRel
  | acq
  | sc
deriving DecidableEq, Repr

/-- The events of the fragment: an initial write, outside every thread, with no order annotation; a
read or a write, in a thread, with its location, value and annotation. No fence; no event is both a
read and a write. -/
inductive Lab (T V : Type) where
  | init (l : Nat) (v : V)
  | read (t : T) (l : Nat) (v : V) (a : Ann)
  | write (t : T) (l : Nat) (v : V) (a : Ann)
deriving DecidableEq, Repr

namespace Lab

variable {T V : Type}

/-- The location of a label (`loc` of `rc11.cat`). -/
def loc : Lab T V → Nat
  | .init l _ | .read _ l _ _ | .write _ l _ _ => l

/-- The value of a label. -/
def val : Lab T V → V
  | .init _ v | .read _ _ v _ | .write _ _ v _ => v

/-- The thread of a label; none for an initial write. -/
def thread? : Lab T V → Option T
  | .init .. => none
  | .read t .. | .write t .. => some t

/-- The order annotation of a label; none for an initial write. -/
def ann? : Lab T V → Option Ann
  | .init .. => none
  | .read _ _ _ a | .write _ _ _ a => some a

/-- `R` of herd: the reads. -/
def isR : Lab T V → Bool
  | .read .. => true
  | _ => false

/-- `W` of herd: the writes, the initial writes included. -/
def isW : Lab T V → Bool
  | .write .. | .init .. => true
  | _ => false

/-- `IW` of herd: the initial writes. -/
def isIW : Lab T V → Bool
  | .init .. => true
  | _ => false

end Lab

/-- A candidate execution of the fragment: labels, the pairing of the two components of an RMW
(`partner r = some w` for a pair `(r, w)` of `rmw`), and the relations `sb`, `rf`, `mo` (`mo` is
`co` in `rc11.cat`). -/
structure Graph (E T V : Type) where
  lab : E → Lab T V
  partner : E → Option E
  sb : E → E → Prop
  rf : E → E → Prop
  mo : E → E → Prop

namespace Graph

variable {E T V : Type} (G : Graph E T V)

/-! ## The sets and relations that `rc11.cat` names -/

/-- `R` of `rc11.cat`: the reads. -/
def R (e : E) : Prop := (G.lab e).isR = true
/-- `W` of `rc11.cat`: the writes, the initial writes included. -/
def W (e : E) : Prop := (G.lab e).isW = true
/-- `IW` of `rc11.cat`: the initial writes. -/
def IW (e : E) : Prop := (G.lab e).isIW = true
/-- `RLX` of `rc11.cat`. -/
def RLX (e : E) : Prop := (G.lab e).ann? = some .rlx
/-- `REL` of `rc11.cat`. -/
def REL (e : E) : Prop := (G.lab e).ann? = some .rel
/-- `ACQ_REL` of `rc11.cat`. -/
def ACQ_REL (e : E) : Prop := (G.lab e).ann? = some .acqRel
/-- `ACQ` of `rc11.cat`. -/
def ACQ (e : E) : Prop := (G.lab e).ann? = some .acq
/-- `SC` of `rc11.cat`. -/
def SC (e : E) : Prop := (G.lab e).ann? = some .sc
/-- `A`: the events that carry an order annotation, every event but the initial writes. -/
def A (e : E) : Prop := (G.lab e).ann?.isSome = true
/-- `RLX | REL | ACQ_REL | ACQ | SC`. -/
def Atomic (e : E) : Prop := G.RLX e ∨ G.REL e ∨ G.ACQ_REL e ∨ G.ACQ e ∨ G.SC e
/-- `rmw`: the pairs of the fragment. -/
def rmw (r w : E) : Prop := G.partner r = some w
/-- `RMW`: the components of the pairs. -/
def RMW (e : E) : Prop := (∃ w, G.rmw e w) ∨ ∃ r, G.rmw r e
/-- `loc`: same location. -/
def loc (a b : E) : Prop := (G.lab a).loc = (G.lab b).loc
/-- `ext`: events of distinct threads. -/
def ext (a b : E) : Prop := (G.lab a).thread? ≠ (G.lab b).thread?

/-! ## The fragment -/

/-- The five pair rows: the annotations of the read and write components of an RMW of order
`relaxed`, `acquire`, `release`, `acq_rel`, `seq_cst` (`extract_read`, `extract_write` of herd). -/
def PairAnn : Ann → Ann → Prop
  | .rlx, .rlx | .acq, .rlx | .rlx, .rel | .acq, .rel | .sc, .sc => True
  | _, _ => False

/-- The declared fragment, by its conditions and by them only:

* one initial write per location used, outside every thread, with no annotation;
* a read carries `RLX`, `ACQ` or `SC`; a write `RLX`, `REL` or `SC`; no event carries `ACQ_REL`;
* `rmw`: each pair `(r, w)` relates a read and a write of the same thread and location, `r`
  immediately `sb`-before `w`; an event belongs to at most one pair; the annotations of `r` and
  `w` form one of the five pair rows;
* `sb`: a strict order, total on the events of each thread, relating no two threads, with no edge
  into an initial write (edges from an initial write are neither required nor excluded);
* `rf`: each read has exactly one source, a write of the same location and value; `rf` relates
  only such pairs (the typing read into "each read has exactly one source, a write …");
* `mo`: a strict total order on the writes of each location, the initial write included; `mo`
  relates only two writes of the same location (the typing read into "on the writes of each
  location"). -/
structure Frag : Prop where
  init_exists : ∀ e, ∃ i v, G.lab i = .init (G.lab e).loc v
  init_unique : ∀ i j l v v', G.lab i = .init l v → G.lab j = .init l v' → i = j
  ann_read : ∀ e t l v a, G.lab e = .read t l v a → a = .rlx ∨ a = .acq ∨ a = .sc
  ann_write : ∀ e t l v a, G.lab e = .write t l v a → a = .rlx ∨ a = .rel ∨ a = .sc
  rmw_read : ∀ r w, G.rmw r w → G.R r
  rmw_write : ∀ r w, G.rmw r w → (G.lab w).isW = true ∧ (G.lab w).isIW = false
  rmw_thread : ∀ r w, G.rmw r w → (G.lab r).thread? = (G.lab w).thread?
  rmw_loc : ∀ r w, G.rmw r w → G.loc r w
  rmw_sb : ∀ r w, G.rmw r w → G.sb r w
  rmw_imm : ∀ r w z, G.rmw r w → ¬ (G.sb r z ∧ G.sb z w)
  rmw_inj : ∀ r r' w, G.rmw r w → G.rmw r' w → r = r'
  rmw_ann : ∀ r w a a', G.rmw r w → (G.lab r).ann? = some a → (G.lab w).ann? = some a' →
    PairAnn a a'
  sb_irrefl : ∀ a, ¬ G.sb a a
  sb_trans : ∀ a b c, G.sb a b → G.sb b c → G.sb a c
  sb_thread : ∀ a b t, G.sb a b → (G.lab a).thread? = some t → (G.lab b).thread? = some t
  sb_not_init : ∀ a b, G.sb a b → ¬ G.IW b
  sb_total : ∀ a b t, (G.lab a).thread? = some t → (G.lab b).thread? = some t → a ≠ b →
    G.sb a b ∨ G.sb b a
  rf_type : ∀ w r, G.rf w r → G.W w ∧ G.R r ∧ G.loc w r ∧ (G.lab w).val = (G.lab r).val
  rf_exists : ∀ r, G.R r → ∃ w, G.rf w r
  rf_unique : ∀ w w' r, G.rf w r → G.rf w' r → w = w'
  mo_type : ∀ a b, G.mo a b → G.W a ∧ G.W b ∧ G.loc a b
  mo_irrefl : ∀ a, ¬ G.mo a a
  mo_trans : ∀ a b c, G.mo a b → G.mo b c → G.mo a c
  mo_total : ∀ a b, G.W a → G.W b → G.loc a b → a ≠ b → G.mo a b ∨ G.mo b a

/-! ## The relations of `rc11.cat`, without fences -/

/-- The reflexive-transitive closure. -/
def RTC (Rel : E → E → Prop) (a b : E) : Prop := a = b ∨ TransGen Rel a b

/-- `myrmw = [RMW] | rmw`. -/
def myrmw (a b : E) : Prop := (G.RMW a ∧ a = b) ∨ G.rmw a b

/-- `rb = (rf^-1; mo) \ id`. -/
def rb (a b : E) : Prop := (∃ w, G.rf w a ∧ G.mo w b) ∧ a ≠ b

/-- `rf | mo | rb`. -/
def ecoBase (a b : E) : Prop := G.rf a b ∨ G.mo a b ∨ G.rb a b

/-- `eco = (rf | mo | rb)+`. -/
def eco (a b : E) : Prop := TransGen G.ecoBase a b

/-- `rf; myrmw`. -/
def rfMy (a b : E) : Prop := ∃ c, G.rf a c ∧ G.myrmw c b

/-- `rs = [W]; (sb & loc)?; [W & (RLX | REL | ACQ_REL | ACQ | SC)]; (rf; myrmw)*`. -/
def rs (a b : E) : Prop :=
  G.W a ∧ ∃ c, (a = c ∨ (G.sb a c ∧ G.loc a c)) ∧ G.W c ∧ G.Atomic c ∧ RTC G.rfMy c b

/-- `sw = [(REL | ACQ_REL | SC)]; rs; rf; [R & (RLX | REL | ACQ | ACQ_REL | SC)];
[(ACQ | ACQ_REL | SC)]`, the fence factors `([F]; sb)?` and `(sb; [F])?` removed. -/
def sw (a b : E) : Prop :=
  (G.REL a ∨ G.ACQ_REL a ∨ G.SC a) ∧ (∃ c, G.rs a c ∧ G.rf c b) ∧ G.R b ∧ G.Atomic b ∧
    (G.ACQ b ∨ G.ACQ_REL b ∨ G.SC b)

/-- `sb | sw`. -/
def sbsw (a b : E) : Prop := G.sb a b ∨ G.sw a b

/-- `hb = (sb | sw)+`. -/
def hb (a b : E) : Prop := TransGen G.sbsw a b

/-- `sbl = sb \ loc`. -/
def sbl (a b : E) : Prop := G.sb a b ∧ ¬ G.loc a b

/-- `hbl = hb & loc`. -/
def hbl (a b : E) : Prop := G.hb a b ∧ G.loc a b

/-- `scb = sb | sbl; hb; sbl | hbl | mo | rb`, the published model. -/
def scbPub (a b : E) : Prop :=
  G.sb a b ∨ (∃ x y, G.sbl a x ∧ G.hb x y ∧ G.sbl y b) ∨ G.hbl a b ∨ G.mo a b ∨ G.rb a b

/-- `sb \ rmw`. -/
def sbNoRmw (a b : E) : Prop := G.sb a b ∧ ¬ G.rmw a b

/-- The amended `scb` of the corrigendum: `sb | (sb \ rmw); hb; (sb \ rmw) | hbl | mo | rb`. -/
def scbAm (a b : E) : Prop :=
  G.sb a b ∨ (∃ x y, G.sbNoRmw a x ∧ G.hb x y ∧ G.sbNoRmw y b) ∨ G.hbl a b ∨ G.mo a b ∨ G.rb a b

/-- `psc = [SC]; scb; [SC]`, without the fence branches of `pscb` and `pscf`. -/
def psc (scb : E → E → Prop) (a b : E) : Prop := G.SC a ∧ scb a b ∧ G.SC b

/-- `sb | rf`. -/
def sbrf (a b : E) : Prop := G.sb a b ∨ G.rf a b

/-! ## The five checks -/

/-- `irreflexive hb; eco? as coherence1`. -/
def Coherence1 : Prop := ∀ a b, G.hb a b → ¬ (b = a ∨ G.eco b a)

/-- `irreflexive (myrmw; eco) as coherencermw`. -/
def CoherenceRmw : Prop := ∀ a b, G.myrmw a b → ¬ G.eco b a

/-- `empty (myrmw & (rb; mo)) as atomicity`. -/
def Atomicity : Prop := ∀ a b, G.myrmw a b → ¬ ∃ c, G.rb a c ∧ G.mo c b

/-- `acyclic psc as SC`, for a given `scb`. -/
def SCCheck (scb : E → E → Prop) : Prop := Events.Acyclic (G.psc scb)

/-- `acyclic (sb | rf) as no-thin-air`. -/
def NoThinAir : Prop := Events.Acyclic G.sbrf

/-- Consistency for the published `rc11.cat`: the five checks, with the published `scb`. -/
def ConsistentPub : Prop :=
  G.Coherence1 ∧ G.CoherenceRmw ∧ G.Atomicity ∧ G.SCCheck G.scbPub ∧ G.NoThinAir

/-- Consistency for RC11 with the amended `psc` of the corrigendum. -/
def ConsistentAm : Prop :=
  G.Coherence1 ∧ G.CoherenceRmw ∧ G.Atomicity ∧ G.SCCheck G.scbAm ∧ G.NoThinAir

/-! ## Races of `rc11.cat` -/

/-- `cnf = ((W * _) | (_ * W)) & loc \ ((IW * _) | (_ * IW))`, with `\` applied after `&`. -/
def cnf (a b : E) : Prop := ((G.W a ∨ G.W b) ∧ G.loc a b) ∧ ¬ (G.IW a ∨ G.IW b)

/-- The same line with `\` applied before `&`. -/
def cnf' (a b : E) : Prop := (G.W a ∨ G.W b) ∧ (G.loc a b ∧ ¬ (G.IW a ∨ G.IW b))

/-- `dr = (cnf & ext) \ (hb | hb^-1 | A * A)`. -/
def dr (a b : E) : Prop := (G.cnf a b ∧ G.ext a b) ∧ ¬ (G.hb a b ∨ G.hb b a ∨ (G.A a ∧ G.A b))

/-- In `cnf`, applying `\` before or after `&` gives the same set. -/
theorem cnf_iff (a b : E) : G.cnf a b ↔ G.cnf' a b := by
  unfold cnf cnf'; exact and_assoc

/-- `dr` is empty on every graph of the fragment's shape: `cnf` excludes every pair containing an
initial write, and `A * A` removes every pair of two annotated events. Neither the fragment nor
finiteness is used. -/
theorem dr_empty (a b : E) : ¬ G.dr a b := by
  rintro ⟨⟨⟨⟨-, -⟩, hiw⟩, -⟩, hno⟩
  apply hno
  refine .inr (.inr ⟨?_, ?_⟩) <;> unfold A <;> simp only [IW] at hiw
  · cases h : G.lab a <;> simp_all [Lab.isIW, Lab.ann?]
  · cases h : G.lab b <;> simp_all [Lab.isIW, Lab.ann?]

/-! ## What `[RMW]` changes on the fragment -/

/-- `rs`, `sw`, `coherencermw` and `atomicity` with `rmw` alone in place of `myrmw`. -/
def rfRmw (a b : E) : Prop := ∃ c, G.rf a c ∧ G.rmw c b

/-- `rs` with `rmw` alone in place of `myrmw` (the `[RMW]` lemma). -/
def rsR (a b : E) : Prop :=
  G.W a ∧ ∃ c, (a = c ∨ (G.sb a c ∧ G.loc a c)) ∧ G.W c ∧ G.Atomic c ∧ RTC G.rfRmw c b

/-- `sw` with `rmw` alone in place of `myrmw` (the `[RMW]` lemma). -/
def swR (a b : E) : Prop :=
  (G.REL a ∨ G.ACQ_REL a ∨ G.SC a) ∧ (∃ c, G.rsR a c ∧ G.rf c b) ∧ G.R b ∧ G.Atomic b ∧
    (G.ACQ b ∨ G.ACQ_REL b ∨ G.SC b)

/-- `coherencermw` with `rmw` alone in place of `myrmw` (the `[RMW]` lemma). -/
def CoherenceRmwR : Prop := ∀ a b, G.rmw a b → ¬ G.eco b a

/-- `atomicity` with `rmw` alone in place of `myrmw` (the `[RMW]` lemma). -/
def AtomicityR : Prop := ∀ a b, G.rmw a b → ¬ ∃ c, G.rb a c ∧ G.mo c b

variable {G}

/-- No event of the fragment is both a read and a write. -/
theorem not_R_W {e : E} (hr : G.R e) (hw : G.W e) : False := by
  unfold R at hr; unfold W at hw
  cases h : G.lab e <;> simp_all [Lab.isR, Lab.isW]

/-- On the fragment, a `(rf; myrmw)*` path ending at a write uses no `[RMW]` step: such a step ends
at the target of an `rf` edge, a read, and a read is the source of no `rf` edge. -/
theorem rtc_rfMy_write (hF : G.Frag) {c d : E} (h : RTC G.rfMy c d) (hd : G.W d) :
    RTC G.rfRmw c d := by
  rcases h with rfl | h
  · exact .inl rfl
  · refine .inr ?_
    have key : ∀ {x}, TransGen G.rfMy c x → G.W x → TransGen G.rfRmw c x := by
      intro x h
      induction h with
      | single h =>
        intro hx
        obtain ⟨y, hrf, hmy⟩ := h
        rcases hmy with ⟨-, rfl⟩ | hr
        · exact (not_R_W (hF.rf_type _ _ hrf).2.1 hx).elim
        · exact .single ⟨y, hrf, hr⟩
      | tail hp h ih =>
        intro hx
        obtain ⟨y, hrf, hmy⟩ := h
        rcases hmy with ⟨-, rfl⟩ | hr
        · exact (not_R_W (hF.rf_type _ _ hrf).2.1 hx).elim
        · exact .tail (ih (hF.rf_type _ _ hrf).1) ⟨y, hrf, hr⟩
    exact key h hd

/-- A `(rf; rmw)*` path is a `(rf; myrmw)*` path. -/
theorem rtc_rfMy_of_rfRmw {c d : E} (h : RTC G.rfRmw c d) : RTC G.rfMy c d := by
  rcases h with rfl | h
  · exact .inl rfl
  · refine .inr ?_
    induction h with
    | single h => obtain ⟨y, h₁, h₂⟩ := h; exact .single ⟨y, h₁, .inr h₂⟩
    | tail _ h ih => obtain ⟨y, h₁, h₂⟩ := h; exact .tail ih ⟨y, h₁, .inr h₂⟩

/-- `rs ; rf` is the same with `myrmw` and with `rmw` alone (on the fragment). `rs` itself changes:
with `myrmw` it can end at the read component of a pair. -/
theorem rs_rf_iff (hF : G.Frag) (a b : E) :
    (∃ c, G.rs a c ∧ G.rf c b) ↔ (∃ c, G.rsR a c ∧ G.rf c b) := by
  constructor
  · rintro ⟨c, ⟨hw, d, hd, hdw, hda, hdc⟩, hrf⟩
    exact ⟨c, ⟨hw, d, hd, hdw, hda, rtc_rfMy_write hF hdc (hF.rf_type _ _ hrf).1⟩, hrf⟩
  · rintro ⟨c, ⟨hw, d, hd, hdw, hda, hdc⟩, hrf⟩
    exact ⟨c, ⟨hw, d, hd, hdw, hda, rtc_rfMy_of_rfRmw hdc⟩, hrf⟩

/-- **The `[RMW]` lemma, `sw`** (`rc11.cat`, `let myrmw = [RMW] | rmw`): on the fragment, `sw` is the
same with `myrmw` and with `rmw` alone. The reason is not that `RMW` is empty: it is that no event
of the fragment is both a read and a write. -/
theorem sw_iff_swR (hF : G.Frag) (a b : E) : G.sw a b ↔ G.swR a b := by
  unfold sw swR; rw [rs_rf_iff hF]

/-- **The `[RMW]` lemma, `atomicity`**: on the fragment, `atomicity` is the same with `myrmw` and
with `rmw` alone: the `[RMW]` part would need an event that is both a read (the source of an `rb`
edge is the target of an `rf` edge) and a write (the target of an `mo` edge). -/
theorem atomicity_iff (hF : G.Frag) : G.Atomicity ↔ G.AtomicityR := by
  constructor
  · intro h a b hab; exact h a b (.inr hab)
  · rintro h a b (⟨-, rfl⟩ | hab) ⟨c, hrb, hmo⟩
    · obtain ⟨⟨w, hrf, -⟩, -⟩ := hrb
      exact not_R_W (hF.rf_type _ _ hrf).2.1 (hF.mo_type _ _ hmo).2.1
    · exact h a b hab ⟨c, hrb, hmo⟩

/-- The anchor of an event for `eco`: a write is its own anchor; a read is anchored at its `rf`
source. -/
private def Anchor (G : Graph E T V) (e w : E) : Prop := (G.W e ∧ w = e) ∨ (G.R e ∧ G.rf w e)

/-- Along `eco`, anchors increase in `mo`, except along a single `rf` edge. -/
private theorem eco_anchor (hF : G.Frag) {a b : E} (h : G.eco a b) :
    (∀ wa wb, Anchor G a wa → Anchor G b wb → G.mo wa wb) ∨ (G.W a ∧ G.R b ∧ G.rf a b) := by
  have uniq : ∀ {e w w'}, Anchor G e w → Anchor G e w' → w = w' := by
    rintro e w w' (⟨he, rfl⟩ | ⟨he, hw⟩) (⟨he', rfl⟩ | ⟨he', hw'⟩)
    · rfl
    · exact (not_R_W he' he).elim
    · exact (not_R_W he he').elim
    · exact hF.rf_unique _ _ _ hw hw'
  have aW : ∀ {e}, G.W e → Anchor G e e := fun he => .inl ⟨he, rfl⟩
  induction h with
  | single h =>
    rcases h with h | h | ⟨⟨w, hrf, hmo⟩, -⟩
    · exact .inr ⟨(hF.rf_type _ _ h).1, (hF.rf_type _ _ h).2.1, h⟩
    · refine .inl fun wa wb ha hb => ?_
      rw [← uniq (aW (hF.mo_type _ _ h).1) ha, ← uniq (aW (hF.mo_type _ _ h).2.1) hb]; exact h
    · refine .inl fun wa wb ha hb => ?_
      rw [← uniq (.inr ⟨(hF.rf_type _ _ hrf).2.1, hrf⟩) ha,
        ← uniq (aW (hF.mo_type _ _ hmo).2.1) hb]
      exact hmo
  | @tail c b _ h ih =>
    -- the anchor of `c` is defined
    rcases h with h | h | ⟨⟨w, hrf, hmo⟩, -⟩
    · -- `rf c b`: `c` is a write, the anchor of `b` is `c`
      have hc := (hF.rf_type _ _ h).1
      rcases ih with ih | ⟨-, hcR, -⟩
      · exact .inl fun wa wb ha hb => by
          rw [← uniq (.inr ⟨(hF.rf_type _ _ h).2.1, h⟩) hb]; exact ih wa c ha (aW hc)
      · exact (not_R_W hcR hc).elim
    · have hc := (hF.mo_type _ _ h).1
      rcases ih with ih | ⟨-, hcR, -⟩
      · refine .inl fun wa wb ha hb => ?_
        rw [← uniq (aW (hF.mo_type _ _ h).2.1) hb]
        exact hF.mo_trans _ _ _ (ih wa c ha (aW hc)) h
      · exact (not_R_W hcR hc).elim
    · have hcR := (hF.rf_type _ _ hrf).2.1
      refine .inl fun wa wb ha hb => ?_
      rw [← uniq (aW (hF.mo_type _ _ hmo).2.1) hb]
      rcases ih with ih | ⟨haW, -, hac⟩
      · exact hF.mo_trans _ _ _ (ih wa w ha (.inr ⟨hcR, hrf⟩)) hmo
      · rw [← uniq (aW haW) ha, hF.rf_unique _ _ _ hac hrf]; exact hmo

/-- On the fragment, `eco` is irreflexive: `rf` is typed, each read has one source, `mo` is a strict
order on the writes of each location, and no event is both a read and a write. -/
theorem eco_irrefl (hF : G.Frag) (a : E) : ¬ G.eco a a := by
  intro h
  rcases eco_anchor hF h with h' | ⟨haW, haR, -⟩
  · by_cases hw : G.W a
    · exact hF.mo_irrefl a (h' a a (.inl ⟨hw, rfl⟩) (.inl ⟨hw, rfl⟩))
    · have hr : G.R a := by
        unfold W at hw; unfold R
        cases hl : G.lab a <;> simp_all [Lab.isW, Lab.isR]
      obtain ⟨w, hrf⟩ := hF.rf_exists a hr
      exact hF.mo_irrefl w (h' w w (.inr ⟨hr, hrf⟩) (.inr ⟨hr, hrf⟩))
  · exact not_R_W haR haW

/-- **The `[RMW]` lemma, `coherencermw`**: on the fragment, `coherencermw` is the same with `myrmw`
and with `rmw` alone. The `[RMW]` part asks `eco` to be irreflexive on the components of pairs,
which holds on the fragment (`eco_irrefl`). -/
theorem coherenceRmw_iff (hF : G.Frag) : G.CoherenceRmw ↔ G.CoherenceRmwR := by
  constructor
  · intro h a b hab; exact h a b (.inr hab)
  · rintro h a b (⟨-, rfl⟩ | hab)
    · exact eco_irrefl hF a
    · exact h a b hab

end Graph

end Ern.ConcurrencyModel.Rc11
