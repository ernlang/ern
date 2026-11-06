import Ern.MemoryModel.Access.Main

/-!
# Access kernel: source leaves after an accepted `transfer` (§63.4, Q17)

Properties Q17 (a) and (b) of the grounding exemption of §63.4. With `g` any authority grounding
the `Modify` right over `source` (`Grounds`, §43) and the grounding chain `RightChain s g` (§63.4),
after an accepted `transfer` (§63) from a reachable state (§57):

* (a) every active authority covering a source leaf lies in the grounding chain (§43, §50);
* (b) every read (O9, §66) of a source leaf is rejected, through every authority, the leaf being
  `Moved` (§41, §63 `ok` effect, §63.3 disjointness); every access through a strict origin-chain
  ancestor of `g` is rejected, reads as above and writes (O10, §67) or shared writes (O11, §68)
  because `g` is an active `Modify` descendant covering the leaf (§43 case 3); a write through `g`
  itself is permitted, a re-initialization of the `Moved` leaf (§67 and §68 have no `Init`
  precondition; §41, §53), with the positive witness
  `TransferSourceWitness.write_through_ground_accepted`.

The derived-outside check of §63.4 is implied by §63.1 on reachable states
(`reachable_noOutsideDerived_of_right`).
-/

namespace Ern.MemoryModel.Access

/-- The grounding chain is unchanged by a transfer, which keeps every origin (§63 `ok` effect: no
authority is created or duplicated; §63.4). -/
theorem transfer_rightChain (s : S3) (src dst : Nat) :
    RightChain (transferEff s src dst) = RightChain s := by
  funext g j; simp only [RightChain, (transfer_skel s src dst).ancs]

/-- An effective mode permitting `Modify` on a leaf (§43, cases 1–2): the authority is active,
covers the leaf, has own mode `Modify`, and no active descendant covers the leaf. -/
private theorem allows_modify {s : S3} {g l : Nat} (h : Allows (effective s g l) .modify) :
    ∃ z, s.A[g]? = some z ∧ z.active = true ∧ l ∈ z.footprint ∧ z.mode = .modify ∧
      descModes s g l = [] := by
  cases he : effective s g l with
  | none => rw [he] at h; exact h.elim
  | some e =>
    rw [he] at h
    obtain ⟨z, hz, za, zl, hez⟩ := effective_some he
    have hm : e = .modify := by cases e <;> simp_all [Allows, OptP, Mode.le]
    subst hm
    rcases effOf_cases hez with ⟨h0, hzm⟩ | ⟨-, -, h⟩
    · exact ⟨z, hz, za, zl, hzm.symm, h0⟩
    · cases h

/-- §43 case 3: an active `Modify` descendant covering the leaf takes away the effective mode. -/
private theorem effective_none_of_modify_desc {s : S3} {a p : Nat}
    (h : Mode.modify ∈ descModes s a p) : effective s a p = none := by
  have hne : descModes s a p ≠ [] := fun e => by rw [e] at h; cases h
  unfold effective
  split
  · split
    · unfold effOf; simp [hne, h]
    · rfl
  · rfl

/-- Core of Q17 (a) (§63.4, §43, §50): under `I1`, if `g` grounds the `Modify` right over `q`, every
active authority covering a leaf of `q` is `g` or an origin-chain ancestor of `g`. A strict
descendant of `g` covering the leaf would take away the effective `Modify` of `g` (§43 cases 3–4);
an unrelated one would contradict `I1` (§50). -/
theorem grounds_cover_rightChain {s : S3} (h1 : I1 s) {q g : Nat} (hg : Grounds s .modify q g)
    {x : Nat} {y : Authority} (hy : s.A[x]? = some y) (ya : y.active = true) {l : Nat}
    (hl : l ∈ y.footprint) (hlq : l ∈ footprint s.P q) : RightChain s g x := by
  obtain ⟨z, hz, za, zl, zm, h0⟩ := allows_modify (hg.2.2 l hlq)
  by_cases hxg : x = g
  · exact .inl hxg
  by_cases hxa : x ∈ s.ancs g
  · exact .inr hxa
  by_cases hgx : g ∈ s.ancs x
  · have : y.mode ∈ descModes s g l := mem_descModes.2 ⟨x, y, hy, ya, hl, hgx, rfl⟩
    rw [h0] at this; cases this
  · have := (h1 x g y z l hxg hy hz ya za hl zl hxa hgx).2
    rw [zm] at this; cases this

/-- Q17 (a) under `I1` (§63.4, §43, §50): after an accepted `transfer` from a state satisfying `I1`,
for every authority `g` grounding the `Modify` right over `source` in the state before the step,
every authority active after the step whose footprint contains a source leaf belongs to the
grounding chain of `g` (§63 `ok` effect: activity, origins and footprints are unchanged). -/
theorem transfer_source_cover_chain_of_i1 {k : K} {s s' : S3} {src dst g : Nat} (h1 : I1 s)
    (ht : TransferStep k src dst s (.ok s')) (hg : Grounds s .modify src g) :
    ∀ (x : Nat) (y : Authority) (l : Nat), s'.A[x]? = some y → y.active = true →
      l ∈ y.footprint → l ∈ footprint s'.P src → RightChain s' g x := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 ht
  intro x y l hy ya hl hls
  rw [transfer_rightChain]; rw [transfer_footprint] at hls
  obtain ⟨y₀, hy₀, e⟩ := (transfer_skel s src dst).get hy
  simp only [skel, Prod.mk.injEq] at e
  exact grounds_cover_rightChain h1 hg hy₀ (e.2.2.2 ▸ ya) (e.2.2.1 ▸ hl) hls

/-- After an accepted `transfer`, every source leaf is `Moved` (§63 `ok` effect; §63.3: a source
leaf is not a destination leaf). -/
theorem transfer_source_moved {k : K} {s s' : S3} {src dst : Nat}
    (ht : TransferStep k src dst s (.ok s')) {l : Nat} (hl : l ∈ footprint s'.P src) :
    s'.I l = .moved := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 ht
  rw [transfer_footprint] at hl
  have hd : l ∉ footprint s.P dst := fun hd => hpre.disjoint ⟨l, hl, hd⟩
  simp [transferEff, hd, hl]

/-- Q17 (b), reads (§63.4, §66.1, §41, §53): after an accepted `transfer`, a read of a list
containing a source leaf is rejected through every authority, the leaf being `Moved`. No invariant
is needed. -/
theorem transfer_source_read_rejected {k : K} {s s' : S3} {src dst : Nat}
    (ht : TransferStep k src dst s (.ok s')) {l : Nat} (hl : l ∈ footprint s'.P src)
    {ls : List Nat} (hls : l ∈ ls) (a : Nat) {o : Outcome3 S3} (h : Read3Step a ls s' o) :
    o = .reject :=
  Guarded.det h (.reject fun hp => by
    have := hp.init l hls; rw [transfer_source_moved ht hl] at this; cases this)

/-- After an accepted `transfer`, a strict origin-chain ancestor of an authority `g` grounding the
`Modify` right over `source` has no effective mode on a source leaf: `g` remains an active
`Modify` descendant covering it (§43 case 3; §63 `ok` effect; §63.4). No invariant is needed. -/
theorem transfer_source_anc_effective {k : K} {s s' : S3} {src dst g : Nat}
    (ht : TransferStep k src dst s (.ok s')) (hg : Grounds s .modify src g) {x l : Nat}
    (hx : x ∈ s'.ancs g) (hl : l ∈ footprint s'.P src) : effective s' x l = none := by
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 ht
  rw [(transfer_skel s src dst).effective]
  rw [(transfer_skel s src dst).ancs] at hx; rw [transfer_footprint] at hl
  obtain ⟨z, hz, za, zl, zm, -⟩ := allows_modify (hg.2.2 l hl)
  exact effective_none_of_modify_desc (mem_descModes.2 ⟨g, z, hz, za, zl, hx, zm⟩)

/-- Q17 (b), ordinary writes (§63.4, §67.1, §43 case 3): after an accepted `transfer`, a write of a
list containing a source leaf through a strict origin-chain ancestor of an authority `g` grounding
the `Modify` right over `source` is rejected. -/
theorem transfer_source_anc_write_rejected {k : K} {s s' : S3} {src dst g : Nat}
    (ht : TransferStep k src dst s (.ok s')) (hg : Grounds s .modify src g) {l : Nat}
    (hl : l ∈ footprint s'.P src) {ls : List Nat} (hls : l ∈ ls) {x : Nat}
    (hx : x ∈ s'.ancs g)
    {o : Outcome3 S3} (h : Write3Step x ls s' o) : o = .reject :=
  Guarded.det h (.reject fun hp => by
    have := hp.effectiveModify l hls
    rw [transfer_source_anc_effective ht hg hx hl] at this; cases this)

/-- Q17 (b), shared writes (§63.4, §68.2, §43 case 3): after an accepted `transfer`, a shared write
of a list containing a source leaf through a strict origin-chain ancestor of an authority `g`
grounding the `Modify` right over `source` is rejected. -/
theorem transfer_source_anc_writeShared_rejected {k : K} {s s' : S3} {src dst g : Nat}
    (ht : TransferStep k src dst s (.ok s')) (hg : Grounds s .modify src g) {l : Nat}
    (hl : l ∈ footprint s'.P src) {ls : List Nat} (hls : l ∈ ls) {x : Nat}
    (hx : x ∈ s'.ancs g)
    {o : Outcome3 S3} (h : WriteSharedStep k x ls s' o) : o = .reject :=
  Guarded.det h (.reject fun hp =>
    hp.effectivePresent l hls (transfer_source_anc_effective ht hg hx hl))

/-- Q17 (a) and (b) on reachable states (§57; §63.4, §43, §50, §66–§68): for a state reachable under
`DDSound` (§80) from well-formed statics (§47), an accepted `transfer` of `src`, and every authority
`g` grounding the `Modify` right over `src` before the step: (a) every authority active after the
step covering a source leaf belongs to the grounding chain of `g`; (b) for every list `ls`
containing a source leaf, a read is rejected through every authority, and a write or shared write is
rejected through every strict origin-chain ancestor of `g`, so every access through a strict
ancestor is rejected. A write through `g` itself is permitted
(`TransferSourceWitness.write_through_ground_accepted`). -/
theorem transfer_source_q17 {k : K} {statics : Statics} {s s' : S3} {src dst g : Nat}
    (hdd : DDSound k) (hst : StaticsOK statics) (hr : Reachable k statics s)
    (ht : TransferStep k src dst s (.ok s')) (hg : Grounds s .modify src g) :
    (∀ (x : Nat) (y : Authority) (l : Nat), s'.A[x]? = some y → y.active = true →
      l ∈ y.footprint → l ∈ footprint s'.P src → RightChain s' g x) ∧
    ∀ (ls : List Nat) (l : Nat), l ∈ ls → l ∈ footprint s'.P src →
      (∀ (a : Nat) (o : Outcome3 S3), Read3Step a ls s' o → o = .reject) ∧
      (∀ x ∈ s'.ancs g, ∀ o : Outcome3 S3, Write3Step x ls s' o → o = .reject) ∧
      (∀ x ∈ s'.ancs g, ∀ o : Outcome3 S3, WriteSharedStep k x ls s' o → o = .reject) :=
  ⟨transfer_source_cover_chain_of_i1 (reachable_kinv hdd hst hr).2.1.1.1 ht hg,
   fun _ _ hls hl => ⟨fun a _ h => transfer_source_read_rejected ht hl hls a h,
    fun _ hx _ h => transfer_source_anc_write_rejected ht hg hl hls hx h,
    fun _ hx _ h => transfer_source_anc_writeShared_rejected ht hg hl hls hx h⟩⟩

/-- Redundancy of the derived-outside check of §63.4 on reachable states (§63.1, §63.4, §43, §50;
the clause is kept in `TransferPre`): on a state reachable under `DDSound` (§80) from well-formed
statics (§47), the `Modify` right over `src` (§63.1, `TransferPre.srcRight`) implies the
derived-outside check of §63.4 (`TransferPre.noOutsideDerived`), for an authority grounding that
right; so that check never rejects a `transfer` by itself on a reachable state. -/
theorem reachable_noOutsideDerived_of_right {k : K} {statics : Statics} {s : S3} {src : Nat}
    (hdd : DDSound k) (hst : StaticsOK statics) (hr : Reachable k statics s)
    (hR : HasRight s .modify src) :
    ∃ g ∈ List.range s.A.length, Grounds s .modify src g ∧
      ∀ j ∈ List.range s.A.length, ActiveDerivedOutside s src j → RightChain s g j := by
  obtain ⟨g, hgr, hex, hall⟩ := hR
  refine ⟨g, hgr, ⟨hgr, hex, hall⟩, fun j _ hj => ?_⟩
  cases hy : s.A[j]? with
  | none => simp only [ActiveDerivedOutside, hy, OptP] at hj
  | some y =>
    simp only [ActiveDerivedOutside, hy, OptP] at hj
    obtain ⟨ya, -, -, l, hl, hlq⟩ := hj
    exact grounds_cover_rightChain (reachable_kinv hdd hst hr).2.1.1.1 ⟨hgr, hex, hall⟩ hy ya hl
      hlq

namespace TransferSourceWitness

open Examples

/-- The state after `transfer(0, 1)` from `S3.init st` (§47, §63 `ok` effect): leaf 0 `Moved`,
leaf 1 `Init`. -/
def t1 : S3 := transferEff s0 0 1

/-- Writes through the grounding authority itself are accepted on a moved source leaf (§63.4, §67,
§68, §41, §53): under `K0` (`DDSound`, §80) and the well-formed statics `st` (§47), `S3.init st` is
reachable, `transfer(0, 1)` is accepted, root authority 0 grounds the `Modify` right over place 0,
leaf 0 is a `Moved` source leaf afterwards, and both a write (O10) and a shared write (O11) of leaf
0 through authority 0 are accepted, the resulting state being reachable. Positive witness of (b): a
write through the grounding authority itself is a permitted re-initialization of the `Moved` leaf.
-/
theorem write_through_ground_accepted : DDSound K0 ∧ StaticsOK st ∧ Reachable K0 st s0 ∧
    TransferStep K0 0 1 s0 (.ok t1) ∧ Grounds s0 .modify 0 0 ∧ 0 ∈ footprint t1.P 0 ∧
    t1.I 0 = .moved ∧ Write3Step 0 [0] t1 (.ok (write3Eff t1 [0])) ∧
    WriteSharedStep K0 0 [0] t1 (.ok (write3Eff t1 [0])) ∧
    Reachable K0 st (write3Eff t1 [0]) := by
  have ht : TransferStep K0 0 1 s0 (.ok t1) := .ok (by decide)
  have hw : Write3Step 0 [0] t1 (.ok (write3Eff t1 [0])) := .ok (by decide)
  exact ⟨fun _ _ h => h.elim, by decide, .init, ht, by decide, by decide, by decide, hw,
    .ok (by decide), .step (.step .init (.transfer ht)) (.write hw)⟩

end TransferSourceWitness

end Ern.MemoryModel.Access
