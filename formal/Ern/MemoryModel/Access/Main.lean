import Ern.MemoryModel.Access.Preserve.DeriveSplitRelease
import Ern.MemoryModel.Access.Preserve.Transfer
import Ern.MemoryModel.Access.Preserve.Small
import Ern.MemoryModel.Access.Preserve.Frames
import Ern.MemoryModel.Access.Preserve.EndFree
import Ern.MemoryModel.Access.Preserve.Alloc

/-!
# Access kernel: steps, reachable states and the main invariant

Assembles the per-operation results of `Ern.MemoryModel.Access.Preserve.*` into the statements of
§57, §58 and §59 of `specs/ERN_Memory_Model_Specification_v0.md`:

* kernel operations O1–O16 as data, their outcome relation, and the correspondence of `KStep` and
  `Reachable` with the labelled steps and their reflexive-transitive closure (§57, §58);
* preservation of `KInv` (§57) and `KAux` by every step except `transfer` (§63), and for
  `transfer` the exact condition: on states satisfying the auxiliary `HeldAnchored`, the step
  preserves the invariant iff the destination is usable afterwards;
* `HeldAnchored` holds initially and is preserved by every step from a `WF3` state;
* the initial state satisfies the invariant under `StaticsOK` (§47), and its `Init` leaves are the
  declared ones;
* the main invariant on reachable states (§57) is false as stated (`reachable_kinv_false`); it
  holds on runs whose transfers keep the destination usable (`reachableDU_kinv`);
* §59: only writes and transfers make a leaf `Init`, and every `Init` leaf of a reached state was
  declared or written on the run; §39: frame 0 stays at the bottom of the stack; §58: only `alloc`
  fails.
-/

namespace Ern.MemoryModel.Access

/-! ## Kernel operations as data (§58, §60–§75) -/

/-- A kernel operation O1–O16 with its arguments (§60–§75). -/
inductive KernelOp where
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
  /-- O10 `write` (§67). -/
  | write (a : Nat) (ls : List Nat)
  /-- O11 `writeShared` (§68). -/
  | writeShared (a : Nat) (ls : List Nat)
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

/-- Outcome relation of a kernel operation (§58, §60–§75): the step relation of the operation. -/
def KernelOp.Step (k : K) : KernelOp → S3 → Outcome3 S3 → Prop
  | .derive src region m => DeriveStep src region m
  | .split src rs => SplitStep k src rs
  | .release a => ReleaseStep a
  | .transfer src dst => TransferStep k src dst
  | .depend q x => DependStep q x
  | .enter ps ls => EnterStep ps ls
  | .exit => ExitStep k
  | .read a ls => Read3Step a ls
  | .write a ls => Write3Step a ls
  | .writeShared a ls => WriteSharedStep k a ls
  | .pin p => PinStep p
  | .unpin p => UnpinStep k p
  | .endUse p => EndUseStep k p
  | .free p auth => FreeStep k p auth
  | .alloc pr ow ls => AllocStep k pr ow ls
  | .store a p => StoreStep a p

/-- A kernel step is the `ok` outcome of some operation O1–O16 (§57, §58). -/
theorem kstep_iff {k : K} {s s' : S3} : KStep k s s' ↔ ∃ op : KernelOp, op.Step k s (.ok s') := by
  constructor
  · intro h
    cases h with
    | derive h => exact ⟨.derive _ _ _, h⟩
    | split h => exact ⟨.split _ _, h⟩
    | release h => exact ⟨.release _, h⟩
    | transfer h => exact ⟨.transfer _ _, h⟩
    | depend h => exact ⟨.depend _ _, h⟩
    | enter h => exact ⟨.enter _ _, h⟩
    | exit h => exact ⟨.exit, h⟩
    | read h => exact ⟨.read _ _, h⟩
    | write h => exact ⟨.write _ _, h⟩
    | writeShared h => exact ⟨.writeShared _ _, h⟩
    | pin h => exact ⟨.pin _, h⟩
    | unpin h => exact ⟨.unpin _, h⟩
    | endUse h => exact ⟨.endUse _, h⟩
    | free h => exact ⟨.free _ _, h⟩
    | alloc h => exact ⟨.alloc _ _ _, h⟩
    | store h => exact ⟨.store _ _, h⟩
  · rintro ⟨op, h⟩
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

/-- Finite runs of kernel steps from `s` (§57): the reflexive-transitive closure of `KStep`. -/
inductive KStar (k : K) (s : S3) : S3 → Prop where
  /-- The empty run (§57). -/
  | refl : KStar k s s
  /-- A run followed by one kernel step (§57). -/
  | tail {t u : S3} : KStar k s t → KStep k t u → KStar k s u

/-- The reachable states of §57 are the states reached from `S3.init statics` by a finite run of
kernel steps. -/
theorem reachable_iff {k : K} {statics : Statics} {s : S3} :
    Reachable k statics s ↔ KStar k (S3.init statics) s := by
  constructor
  · intro h
    induction h with
    | init => exact .refl
    | step _ h ih => exact .tail ih h
  · intro h
    induction h with
    | refl => exact .init
    | tail _ h ih => exact .step ih h

/-! ## Outcomes (§58) and the base frame (§39) -/

/-- Only `alloc` may produce `fail` among O1–O16 (§58). -/
theorem op_fail_only_alloc {k : K} {op : KernelOp} {s : S3} (h : op.Step k s .fail) :
    ∃ pr ow ls, op = .alloc pr ow ls := by
  cases op with
  | alloc pr ow ls => exact ⟨pr, ow, ls, rfl⟩
  | _ => exact (Alloc.guarded_ne_fail h).elim

/-- No kernel step changes the bottom of the frame stack (§39: the base frame never exits). -/
theorem kstep_base {k : K} {s s' : S3} (h : KStep k s s') : s'.F.getLast? = s.F.getLast? := by
  cases h with
  | derive h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | split h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | release h =>
    rename_i a
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    unfold releaseEff; split <;> rfl
  | transfer h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | depend h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | enter h => exact enter_keeps_base h
  | exit h => exact (exit_keeps_base h).2
  | read h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | write h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | writeShared h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | pin h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | unpin h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | endUse h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | free h => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; rfl
  | alloc h => cases h with | ok => rfl
  | store h =>
    rename_i a p
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    unfold storeEff; split <;> rfl

/-- On every reachable state, the bottom of the stack is the base frame 0 (§39, §47). -/
theorem reachable_base {k : K} {statics : Statics} {s : S3} (h : Reachable k statics s) :
    s.F.getLast? = some 0 := by
  induction h with
  | init => rfl
  | step _ h ih => rw [kstep_base h]; exact ih

/-- The base frame 0 is never removed from the stack of a reachable state (§39). -/
theorem reachable_base_mem {k : K} {statics : Statics} {s : S3} (h : Reachable k statics s) :
    0 ∈ s.F :=
  List.mem_of_getLast? (reachable_base h)

/-! ## Preservation by every step except `transfer` (§57, §58) -/

/-- Every operation other than `transfer` preserves `KInv` (§57) and `KAux` (§40, §49.7) from its
`ok` outcome, under `DDSound` (§80, used by `split`, §61). -/
theorem op_preserves {k : K} {op : KernelOp} {s s' : S3} (hdd : DDSound k) (hinv : KInv s)
    (haux : KAux s) (h : op.Step k s (.ok s')) (hnt : ∀ src dst, op ≠ .transfer src dst) :
    KInv s' ∧ KAux s' := by
  cases op with
  | derive => exact derive_preserves hinv haux h
  | split => exact split_preserves hdd hinv haux h
  | release => exact release_preserves hinv haux h
  | transfer src dst => exact absurd rfl (hnt src dst)
  | depend => exact depend_preserves hinv haux h
  | enter => exact enter_preserves hinv haux h
  | exit => exact exit_preserves hinv haux h
  | read => exact read_preserves hinv haux h
  | write => exact write_preserves hinv haux h
  | writeShared => exact writeShared_preserves hinv haux h
  | pin => exact pin_preserves hinv haux h
  | unpin => exact unpin_preserves hinv haux h
  | endUse => exact endUse_preserves hinv haux h
  | free => exact free_preserves hinv haux h
  | alloc => exact alloc_preserves hinv haux h
  | store => exact store_preserves hinv haux h

/-- Every kernel step from a state satisfying `KInv` (§57) and `KAux` (§40, §49.7) under `DDSound`
(§80) either preserves both or is an accepted `transfer` (§63), the one exception
(`transfer_breaks_kinv`). -/
theorem kstep_preserves {k : K} {s s' : S3} (hdd : DDSound k) (hinv : KInv s) (haux : KAux s)
    (h : KStep k s s') :
    (KInv s' ∧ KAux s') ∨ ∃ src dst, TransferStep k src dst s (.ok s') := by
  obtain ⟨op, hop⟩ := kstep_iff.1 h
  cases op with
  | transfer src dst => exact .inr ⟨src, dst, hop⟩
  | _ => exact .inl (op_preserves hdd hinv haux hop fun _ _ e => KernelOp.noConfusion e)

/-! ## `HeldAnchored` is preserved by every step (§44, §65, §63) -/

/-- An active derived authority of the resulting state held by place `q` is an anchor of `q`
(§44), or it was already such an authority before the step and the step keeps the anchors of `q`
when `q` was usable (§52). Under `WF3` (§49.8) this gives `HeldAnchored` after the step. -/
private theorem heldAnchored_of_step {s s' : S3} (hw : WF3 s) (hh : HeldAnchored s)
    (hstep : ∀ x y q, s'.A[x]? = some y → y.active = true → y.origin ≠ none →
      y.holder = .place q → x ∈ s'.D q ∨ ∃ y₀ : Authority, s.A[x]? = some y₀ ∧
        y₀.active = true ∧ y₀.origin ≠ none ∧ y₀.holder = .place q ∧
        (s.Usable q → x ∈ s.D q → x ∈ s'.D q)) : HeldAnchored s' := by
  intro x y q hy ya ho hhq _
  rcases hstep x y q hy ya ho hhq with h | ⟨y₀, hy₀, ya₀, ho₀, hh₀, himp⟩
  · exact h
  · have hu : s.Usable q := by have := hw.holders x y₀ hy₀ ya₀; rw [hh₀] at this; exact this
    exact himp hu (hh x y₀ q hy₀ ya₀ ho₀ hh₀ hu)

/-- An element of an appended list comes from one of the two parts (§42: authorities added by
`derive`, `split`, `enterFrame`, `alloc`). -/
private theorem getElem?_append_cases {α : Type} {l E : List α} {x : Nat} {y : α}
    (h : (l ++ E)[x]? = some y) : l[x]? = some y ∨ y ∈ E := by
  by_cases hx : x < l.length
  · rw [List.getElem?_append_left hx] at h; exact .inl h
  · rw [List.getElem?_append_right (by omega)] at h; exact .inr (List.mem_of_getElem? h)

/-- Every operation preserves `HeldAnchored` from a `WF3` state (§44; §60–§75 `ok` effects): new
authorities are held by frames or have no origin; `store` anchors what it stores (§65); a
`transfer` moves an authority with the anchors of its holder (§63); `exitFrame` maps a surviving
anchor to itself (§73); the other steps only release authorities or keep the anchors of the
places whose authorities stay active. -/
theorem op_preserves_heldAnchored {k : K} {op : KernelOp} {s s' : S3} (hw : WF3 s)
    (hh : HeldAnchored s) (h : op.Step k s (.ok s')) : HeldAnchored s' := by
  cases op with
  | derive src region m =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
    rcases addAuth_get hy with ⟨-, hy⟩ | ⟨-, rfl⟩
    · exact .inr ⟨y, hy, ya, ho, hhq, fun _ hx => hx⟩
    · cases hhq
  | split src rs =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
    rcases getElem?_append_cases hy with hy | hy
    · exact .inr ⟨y, hy, ya, ho, hhq, fun _ hx => hx⟩
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; cases hhq
  | release a =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    cases hx₀ : s.A[a]? with
    | none => simp only [releaseEff, hx₀]; exact hh
    | some x₀ =>
      rw [releaseEff_eq hx₀]
      refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
      simp only [set_get (lt_of_getElem? hx₀)] at hy
      split at hy
      · cases hy; cases ya
      · rename_i hax
        refine .inr ⟨y, hy, ya, ho, hhq, fun _ hx => ?_⟩
        simp only
        split
        · exact List.mem_filter.2 ⟨hx, by simpa using fun e => hax e.symm⟩
        · exact hx
  | transfer src dst => exact transfer_preserves_heldAnchored hw hh h
  | depend q₀ x₀ =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => .inr ⟨y, hy, ya, ho, hhq,
      fun _ hx => ?_⟩
    simp only [dependEff]
    split
    · rename_i e; subst e; exact List.mem_append_left _ hx
    · exact hx
  | enter ps ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
    rcases getElem?_append_cases hy with hy | hy
    · rw [getElem?_mapI] at hy
      obtain ⟨y₀, hy₀, e⟩ := Option.map_eq_some_iff.1 hy
      split at e
      · subst e; cases hhq
      · subst e
        refine .inr ⟨y₀, hy₀, ya, ho, hhq, fun hu hx => ?_⟩
        show x ∈ (if s.P.length ≤ q then [] else s.D q)
        split
        · exact absurd hu.lt (Nat.not_lt.2 ‹_›)
        · exact hx
    · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; exact absurd rfl ho
  | exit =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
    simp only [exitEff, getElem?_mapI, Nat.zero_add] at hy
    obtain ⟨y₀, hy₀, e⟩ := Option.map_eq_some_iff.1 hy
    unfold exitG at e
    split at e
    · rename_i hsv
      have ya₀ : y₀.active = true := by
        unfold Survives at hsv; rw [hy₀] at hsv; exact hsv.1
      split at e
      · subst e; exact absurd ‹_› ho
      · rename_i o ho₀
        subst e
        refine .inr ⟨y₀, hy₀, ya₀, (by rw [ho₀]; exact fun h => by cases h), hhq, fun _ hx => ?_⟩
        simp only [exitEff]
        refine List.mem_map.2 ⟨x, hx, ?_⟩
        show (firstSurv s s.F.tail (x :: s.ancs x)).getD x = x
        rw [firstSurv, List.find?_cons_of_pos (p := fun z => decide (Survives s s.F.tail z))
          (a := x) (decide_eq_true hsv)]
        rfl
    · subst e; cases ya
  | read a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact hh
  | write a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact heldAnchored_of_step hw hh fun x y q hy ya ho hhq =>
      .inr ⟨y, hy, ya, ho, hhq, fun _ hx => hx⟩
  | writeShared a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact heldAnchored_of_step hw hh fun x y q hy ya ho hhq =>
      .inr ⟨y, hy, ya, ho, hhq, fun _ hx => hx⟩
  | pin p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact heldAnchored_of_step hw hh fun x y q hy ya ho hhq =>
      .inr ⟨y, hy, ya, ho, hhq, fun _ hx => hx⟩
  | unpin p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    exact heldAnchored_of_step hw hh fun x y q hy ya ho hhq =>
      .inr ⟨y, hy, ya, ho, hhq, fun _ hx => hx⟩
  | endUse p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
    obtain ⟨hy₀, hnh, -⟩ := EndFree.endUse_active hy ya
    refine .inr ⟨y, hy₀, ya, ho, hhq, fun _ hx => ?_⟩
    rw [hhq] at hnh
    show x ∈ (if partOf s.P q p then [] else s.D q)
    split
    · exact absurd ‹_› hnh
    · exact hx
  | free p auth =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
    obtain ⟨hy₀, -, -⟩ := EndFree.free_active hy ya
    exact .inr ⟨y, hy₀, ya, ho, hhq, fun _ hx => hx⟩
  | alloc pr ow ls =>
    cases h with
    | ok _ _ =>
      refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
      rcases getElem?_append_cases hy with hy | hy
      · refine .inr ⟨y, hy, ya, ho, hhq, fun hu hx => ?_⟩
        show x ∈ (if s.P.length ≤ q then [] else s.D q)
        split
        · exact absurd hu.lt (Nat.not_lt.2 ‹_›)
        · exact hx
      · obtain ⟨r, -, rfl⟩ := List.mem_map.1 hy; exact absurd rfl ho
  | store a p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    cases hy₁ : s.A[a]? with
    | none => simp only [storeEff, hy₁]; exact hh
    | some y₁ =>
      have heq : storeEff s a p = { s with
          A := s.A.set a { y₁ with holder := .place p }
          D := fun q => if q = p then s.D p ++ [a] else s.D q
          I := fun l => if l = p then .init else s.I l } := by
        simp only [storeEff, hy₁]
      rw [heq]
      refine heldAnchored_of_step hw hh fun x y q hy ya ho hhq => ?_
      simp only [set_get (lt_of_getElem? hy₁)] at hy
      split at hy
      · rename_i e; subst e; cases hy
        cases hhq
        exact .inl (by simp)
      · refine .inr ⟨y, hy, ya, ho, hhq, fun _ hx => ?_⟩
        simp only
        split
        · rename_i e; subst e; exact List.mem_append_left _ hx
        · exact hx

/-- `HeldAnchored` is preserved by every kernel step from a `WF3` state (§44, §49, §57). -/
theorem kstep_preserves_heldAnchored {k : K} {s s' : S3} (hw : WF3 s) (hh : HeldAnchored s)
    (h : KStep k s s') : HeldAnchored s' := by
  obtain ⟨op, hop⟩ := kstep_iff.1 h
  exact op_preserves_heldAnchored hw hh hop

/-! ## The transfer step (§63, §57) -/

/-- After an accepted `transfer` (§63) from a `WF3` state (§49), `NoDangling` (§54) of the
resulting state forces the destination to be usable: an authority of the current frame with
`Modify` over the destination (§63.1) still covers its leaves. -/
theorem transfer_dst_usable_of_noDangling {k : K} {s s' : S3} {src dst : Nat} (hw : WF3 s)
    (h : TransferStep k src dst s (.ok s')) (hnd : NoDangling s') : s'.Usable dst := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  refine Decidable.byContradiction fun hu => ?_
  obtain ⟨a, -, -, hall⟩ := hpre.dstRight
  obtain ⟨l, hl⟩ := exists_mem_footprint hw (s.P.length - dst + 1) dst (by omega)
    hpre.dstUsable.lt
  have hal := hall l hl
  cases he : effective s a l with
  | none => rw [he] at hal; exact hal
  | some e =>
    obtain ⟨x, hx, xa, hlx, -⟩ := effective_some he
    have hx' : (transferEff s src dst).A[a]? = some (if heldIn s.P src x.holder then
        { x with holder := mvTo s.P src dst x.holder } else x) := by
      rw [transfer_A_get, hx]; rfl
    exact hnd a _ hx' (by split <;> exact xa) dst hu l (by rw [transfer_footprint]; exact hl)
      (by split <;> exact hlx)

/-- On a state satisfying `KInv` (§57), `KAux` (§40, §49.7) and `HeldAnchored` (auxiliary, not a
clause of §63 nor of §57), an accepted `transfer` (§63) preserves `KInv ∧ KAux` iff its
destination is usable in the resulting state. The destination usable afterwards is not a clause of
§63 (`transfer_breaks_kinv`); this states exactly when §57 holds after the step. -/
theorem transfer_kinv_iff {k : K} {s s' : S3} {src dst : Nat} (hinv : KInv s) (haux : KAux s)
    (hheld : HeldAnchored s) (h : TransferStep k src dst s (.ok s')) :
    KInv s' ∧ KAux s' ↔ s'.Usable dst :=
  ⟨fun hk => transfer_dst_usable_of_noDangling hinv.1 h hk.1.2.1.2.2,
    transfer_preserves_of_dst_usable_of_heldAnchored hinv haux hheld h⟩

/-- Every operation, `transfer` included when its destination stays usable (a hypothesis, not a
clause of §63), preserves `KInv` (§57), `KAux` (§40, §49.7) and `HeldAnchored` (auxiliary) under
`DDSound` (§80). -/
theorem op_preserves_of_dst_usable {k : K} {op : KernelOp} {s s' : S3} (hdd : DDSound k)
    (hinv : KInv s) (haux : KAux s) (hheld : HeldAnchored s) (h : op.Step k s (.ok s'))
    (hdu : ∀ src dst, op = .transfer src dst → s'.Usable dst) :
    KInv s' ∧ KAux s' ∧ HeldAnchored s' := by
  have hh' := op_preserves_heldAnchored hinv.1 hheld h
  cases op with
  | transfer src dst =>
    have h' := (transfer_kinv_iff hinv haux hheld h).2 (hdu src dst rfl)
    exact ⟨h'.1, h'.2, hh'⟩
  | _ =>
    have h' := op_preserves hdd hinv haux h fun _ _ e => KernelOp.noConfusion e
    exact ⟨h'.1, h'.2, hh'⟩

/-! ## The initial state (§47) -/

/-- The places of `S3.init statics` are the declared statics (§47). -/
private theorem initP_len (statics : Statics) : (S3.init statics).P.length = statics.length := by
  simp [S3.init, shapeP]

/-- The place of a static (§47): its declared parent, its owner (the owning static or frame 0),
its kind. -/
private theorem initP_get {statics : Statics} {i : Nat} (hi : i < statics.length) :
    (S3.init statics).P[i]? = some ⟨((statics.map (·.1))[i]?).bind (·.1),
      shapeOwner (statics.map (·.1)) (.frame 0) i,
      (((statics.map (·.1))[i]?).map (·.2.2)).getD 0⟩ := by
  simp only [S3.init, shapeP, List.nil_append, List.getElem?_map,
    List.getElem?_range (show i < (statics.map (·.1)).length by simpa using hi)]
  rfl

/-- A place of `S3.init statics` is a declared static (§47). -/
private theorem initP_get' {statics : Statics} {q : Nat} {pl : Place}
    (h : (S3.init statics).P[q]? = some pl) : q < statics.length ∧
      pl = ⟨((statics.map (·.1))[q]?).bind (·.1),
        shapeOwner (statics.map (·.1)) (.frame 0) q,
        (((statics.map (·.1))[q]?).map (·.2.2)).getD 0⟩ := by
  have hq : q < statics.length := by have := lt_of_getElem? h; rwa [initP_len] at this
  rw [initP_get hq] at h; cases h; exact ⟨hq, rfl⟩

/-- The authorities of `S3.init statics` are the root authorities of the root statics (§47). -/
private theorem initA_get {statics : Statics} {j : Nat} {z : Authority}
    (h : (S3.init statics).A[j]? = some z) : ∃ i, (rootIdx (statics.map (·.1)))[j]? = some i ∧
      z = ⟨.modify, none, footprint (S3.init statics).P i,
        shapeOwner (statics.map (·.1)) (.frame 0) i, true⟩ := by
  simp only [S3.init, List.getElem?_map] at h
  obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.1 h
  exact ⟨i, hi, rfl⟩

/-- A root static is a declared element with no parent (§40, §47). -/
private theorem rootIdx_get {ls : List (Option Nat × Option Nat × Nat)} {j i : Nat}
    (h : (rootIdx ls)[j]? = some i) : i < ls.length ∧ (ls[i]?).bind (·.1) = none := by
  have := List.mem_of_getElem? h
  simp only [rootIdx, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none] at this
  exact this

/-- The parent of a static is an earlier static with the same owner (`StaticsOK`, §47). -/
private theorem statics_parent {statics : Statics} (h : StaticsOK statics) {i r : Nat}
    (hi : i < statics.length) (hr : ((statics.map (·.1))[i]?).bind (·.1) = some r) :
    r < i ∧ ((statics.map (·.1))[i]?).bind (·.2.1) = ((statics.map (·.1))[r]?).bind (·.2.1) := by
  have h1 := (h i (List.mem_range.2 (by simpa using hi))).1
  rw [hr] at h1
  obtain ⟨-, h2, h3⟩ := h1
  exact ⟨by omega, by simpa using h3⟩

/-- The owning static of a static is an earlier static (`StaticsOK`, §47). -/
private theorem statics_owner {statics : Statics} (h : StaticsOK statics) {i o : Nat}
    (hi : i < statics.length) (ho : ((statics.map (·.1))[i]?).bind (·.2.1) = some o) : o < i := by
  have h2 := (h i (List.mem_range.2 (by simpa using hi))).2
  rw [ho] at h2
  have := h2.2
  omega

/-- Every static is usable in the initial state (§40, §47): its owners lead to frame 0. -/
private theorem init_usable {statics : Statics} (h : StaticsOK statics) :
    ∀ n i, i < n → i < statics.length → (S3.init statics).Usable i
  | 0, _, hn, _ => absurd hn (Nat.not_lt_zero _)
  | n + 1, i, hn, hi => by
    have hpl := initP_get hi
    cases ho : ((statics.map (·.1))[i]?).bind (·.2.1) with
    | none =>
      exact .frame (f := 0) hpl rfl (by unfold shapeOwner; rw [ho]) (List.mem_singleton_self _)
    | some o =>
      have := statics_owner h hi ho
      exact .place (o := o) hpl rfl (by unfold shapeOwner; rw [ho]) (init_usable h n o (by omega)
        (by omega))

/-- A place of `S3.init statics` is a declared static (§40, §47). -/
private theorem init_lt_of_mem_footprint {statics : Statics} {q l : Nat}
    (h : l ∈ footprint (S3.init statics).P q) : q < statics.length := by
  obtain ⟨hl, -, -, hlq⟩ := mem_footprint.1 h
  rw [initP_len] at hl
  rcases hlq with rfl | hc
  · exact hl
  · exact Nat.lt_trans (chain_lt hc) hl

/-- A root static is a root place of the initial state (§40, §47). -/
private theorem init_rootPlace {statics : Statics} {j i : Nat}
    (h : (rootIdx (statics.map (·.1)))[j]? = some i) : RootPlace (S3.init statics).P i := by
  obtain ⟨hil, hin⟩ := rootIdx_get h
  have hi : i < statics.length := by simpa using hil
  exact ⟨by rw [initP_len]; exact hi,
    by simp only [parentOf, initP_get hi, Option.bind_some]; exact hin⟩

/-- Root authorities of distinct positions are roots of distinct statics (§47: one root authority
per root static). -/
private theorem init_root_inj {statics : Statics} {j j' i : Nat}
    (h : (rootIdx (statics.map (·.1)))[j]? = some i)
    (h' : (rootIdx (statics.map (·.1)))[j']? = some i) : j = j' :=
  Frames.getElem?_inj_of_lt ((Frames.range_pairwise_lt _).filter _) h h'

/-- The initial state satisfies `KInv` (§57), `KAux` (§40, §49.7) and `HeldAnchored` (auxiliary)
for a well-formed statics declaration (§47; `StaticsOK` is a hypothesis, not stated by §47). -/
theorem init_kinv {statics : Statics} (hst : StaticsOK statics) :
    KInv (S3.init statics) ∧ KAux (S3.init statics) ∧ HeldAnchored (S3.init statics) := by
  have hus : ∀ i, i < statics.length → (S3.init statics).Usable i :=
    fun i hi => init_usable hst (i + 1) i (Nat.lt_succ_self _) hi
  have hof : ∀ (q : Nat) (pl : Place) (f : Nat), (S3.init statics).P[q]? = some pl →
      pl.owner = .frame f → f < (S3.init statics).nF := by
    intro q pl f hq ho
    obtain ⟨-, rfl⟩ := initP_get' hq
    simp only [shapeOwner] at ho
    split at ho
    · cases ho
    · cases ho; exact Nat.zero_lt_one
  have hop : ∀ (q : Nat) (pl : Place) (o : Nat), (S3.init statics).P[q]? = some pl →
      pl.owner = .place o → o < (S3.init statics).P.length := by
    intro q pl o hq ho
    obtain ⟨hql, rfl⟩ := initP_get' hq
    simp only [shapeOwner] at ho
    split at ho
    · rename_i o' ho'
      cases ho
      rw [initP_len]; exact Nat.lt_trans (statics_owner hst hql ho') hql
    · cases ho
  have hw : WF3 (S3.init statics) := {
    frames := ⟨by simp [S3.init], by simp [S3.init], by simp [S3.init]⟩
    places := fun q pl r hq hp => by
      obtain ⟨hql, rfl⟩ := initP_get' hq
      obtain ⟨hrq, hown⟩ := statics_parent hst hql hp
      exact ⟨_, initP_get (by omega), hrq, by simp only [shapeOwner, hown], rfl⟩
    owners := ⟨hof, hop, fun _ hq => hq.frameOf⟩
    footprints := fun a x ha l hl => by
      obtain ⟨i, -, rfl⟩ := initA_get ha
      exact ⟨(mem_footprint.1 hl).1, (mem_footprint.1 hl).2.1⟩
    origins := fun b y a hb ho => by
      obtain ⟨i, -, rfl⟩ := initA_get hb; cases ho
    rootChain := fun a y l ha hl _ => by
      obtain ⟨i, hi, rfl⟩ := initA_get ha
      exact ⟨a, _, i, .inl rfl, ha, rfl, init_rootPlace hi, (mem_footprint.1 hl).2.2,
        fun _ => Iff.rfl⟩
    rootHeld := fun r hr _ => by
      have hrl : r < statics.length := by have := hr.1; rwa [initP_len] at this
      have hpn : ((statics.map (·.1))[r]?).bind (·.1) = none := by
        have := hr.2; simp only [parentOf, initP_get hrl, Option.bind_some] at this; exact this
      have hmem : r ∈ rootIdx (statics.map (·.1)) := by
        simp only [rootIdx, List.mem_filter, List.mem_range, List.length_map, hrl, hpn,
          Option.isNone_none, and_self]
      obtain ⟨j, hj⟩ := Frames.exists_getElem?_of_mem hmem
      refine ⟨j, ⟨.modify, none, footprint (S3.init statics).P r,
        shapeOwner (statics.map (·.1)) (.frame 0) r, true⟩, _, ?_, rfl, rfl, rfl, initP_get hrl,
        rfl, fun _ => Iff.rfl⟩
      simp only [S3.init, List.getElem?_map, hj]; rfl
    holders := fun a y ha _ => by
      obtain ⟨i, hi, rfl⟩ := initA_get ha
      have hil : i < statics.length := by simpa using (rootIdx_get hi).1
      show HolderLive _ (shapeOwner (statics.map (·.1)) (.frame 0) i)
      unfold shapeOwner
      cases ho : ((statics.map (·.1))[i]?).bind (·.2.1) with
      | none => exact List.mem_singleton_self _
      | some o => exact hus o (Nat.lt_trans (statics_owner hst hil ho) hil) }
  have hconv : RootHeldConv (S3.init statics) := fun x z l r hx _ hl hrp hlr => by
    obtain ⟨i, hi, rfl⟩ := initA_get hx
    obtain rfl := rootOf_unique hrp (init_rootPlace hi) hlr (mem_footprint.1 hl).2.2
    have hil : r < statics.length := by simpa using (rootIdx_get hi).1
    exact ⟨_, initP_get hil, rfl⟩
  have hi1 : I1 (S3.init statics) := fun a b x y p hab ha hb _ _ xp yp _ _ => by
    obtain ⟨i, hi, rfl⟩ := initA_get ha
    obtain ⟨i', hi', rfl⟩ := initA_get hb
    have hii : i ≠ i' := fun e => hab (init_root_inj hi (e ▸ hi'))
    exact absurd (rootOf_unique (init_rootPlace hi) (init_rootPlace hi') (mem_footprint.1 xp).2.2
      (mem_footprint.1 yp).2.2) hii
  have hnd : NoDangling (S3.init statics) := fun _ _ _ _ q hq l hl _ =>
    hq (hus q (init_lt_of_mem_footprint hl))
  have haoh : AnchorOrderHeld (S3.init statics) := fun q hq x y hy _ hhq => by
    obtain ⟨i, -, rfl⟩ := initA_get hy
    have hex : (S3.init statics).effAnchor x = x := by
      have : (S3.init statics).org x = none := by simp [S3.org, hy]
      simp [S3.effAnchor, S3.ancs, chain_none this]
    obtain ⟨f, hf, hfF⟩ := hq.frameOf
    have hf0 : f = 0 := List.mem_singleton.1 hfF
    subst hf0
    have hhq' : shapeOwner (statics.map (·.1)) (.frame 0) i = .place q := hhq
    unfold EffAnchorOK
    rw [hex, hy]
    simp only [OptP, hhq', S3.hframe, pframe_iff.2 hf]
    exact hfF
  refine ⟨kInv_of hw ⟨⟨hi1, ?_, fun _ _ x hx => ?_, i4_always _⟩, fun _ _ x hx => ?_, hnd⟩ haoh,
    hconv, fun x y q hy _ ho _ _ => ?_⟩
  · intro b y a hb ho
    obtain ⟨i, -, rfl⟩ := initA_get hb; cases ho
  · cases hx
  · cases hx
  · obtain ⟨i, -, rfl⟩ := initA_get hy; exact absurd rfl ho

/-- The `Init` leaves of the initial state are exactly the statics declared `Init` (§47, §59). -/
theorem init_statics (statics : Statics) (l : Nat) :
    (S3.init statics).I l = .init ↔ ∃ e, statics[l]? = some e ∧ e.2 = true := by
  show (if ((statics[l]?).map (·.2)).getD false then InitSt.init else .uninit) = .init ↔ _
  cases statics[l]? with
  | none => simp
  | some e => cases he : e.2 <;> simp [he]

/-! ## Reachable states (§57) -/

/-- §57 as stated is false: under a contract satisfying `DDSound` (§80) and well-formed statics
(§47), a reachable state violates `KInv`, after an accepted `transfer` (§63,
`transfer_breaks_kinv`). -/
theorem reachable_kinv_false : ¬ ∀ (k : K) (statics : Statics) (s : S3), DDSound k →
    StaticsOK statics → Reachable k statics s → KInv s := by
  intro hall
  obtain ⟨hdd, s, s', hr, -, -, ht, hn⟩ := transfer_breaks_kinv
  exact hn (hall _ _ _ hdd (by decide) (.step hr (.transfer ht)))

/-- A kernel step whose `transfer`, if it is one, leaves its destination usable (§63). The
condition is a hypothesis on runs, not a clause of §63 nor of §57. -/
def KStepDU (k : K) (s s' : S3) : Prop :=
  ∃ op : KernelOp, op.Step k s (.ok s') ∧ ∀ src dst, op = .transfer src dst → s'.Usable dst

/-- States reached from `S3.init statics` by runs whose transfers keep the destination usable
(§57, restricted by the hypothesis of `KStepDU`, which is not a clause of §63). -/
inductive ReachableDU (k : K) (statics : Statics) : S3 → Prop where
  /-- The initial state (§47). -/
  | init : ReachableDU k statics (S3.init statics)
  /-- One more step of `KStepDU` (§57). -/
  | step {s s' : S3} : ReachableDU k statics s → KStepDU k s s' → ReachableDU k statics s'

/-- From a state satisfying `KInv` (§57), `KAux` (§40, §49.7) and `HeldAnchored` under
`DDSound` (§80), the steps of `KStepDU` are exactly the kernel steps whose resulting state
satisfies `KInv`: the restriction of `ReachableDU` keeps exactly the runs along which §57
holds. -/
theorem kstepDU_iff {k : K} {s s' : S3} (hdd : DDSound k) (hinv : KInv s) (haux : KAux s)
    (hheld : HeldAnchored s) : KStepDU k s s' ↔ KStep k s s' ∧ KInv s' := by
  constructor
  · rintro ⟨op, hop, hdu⟩
    exact ⟨kstep_iff.2 ⟨op, hop⟩, (op_preserves_of_dst_usable hdd hinv haux hheld hop hdu).1⟩
  · rintro ⟨h, hk⟩
    obtain ⟨op, hop⟩ := kstep_iff.1 h
    refine ⟨op, hop, fun src dst e => ?_⟩
    subst e
    exact transfer_dst_usable_of_noDangling hinv.1 hop hk.2.1.2.2

/-- A state of `ReachableDU` is reachable (§57). -/
theorem ReachableDU.reachable {k : K} {statics : Statics} {s : S3}
    (h : ReachableDU k statics s) : Reachable k statics s := by
  induction h with
  | init => exact .init
  | step _ h ih =>
    obtain ⟨op, hop, -⟩ := h
    exact .step ih (kstep_iff.2 ⟨op, hop⟩)

/-- The main invariant of §57 (`WF3 ∧ Inv3 ∧ AnchorOrderHeld ∧ NoOrphan`, with `KAux` and
`HeldAnchored`) on the states reached by runs whose transfers keep the destination usable, under
`DDSound` (§80) and well-formed statics (`StaticsOK`, a hypothesis not stated by §47). The
restriction of the runs is not a clause of §63: without it the statement is false
(`reachable_kinv_false`). -/
theorem reachableDU_kinv {k : K} {statics : Statics} {s : S3} (hdd : DDSound k)
    (hst : StaticsOK statics) (h : ReachableDU k statics s) :
    KInv s ∧ KAux s ∧ HeldAnchored s := by
  induction h with
  | init => exact init_kinv hst
  | step _ h ih =>
    obtain ⟨op, hop, hdu⟩ := h
    exact op_preserves_of_dst_usable hdd ih.1 ih.2.1 ih.2.2 hop hdu

/-! ## Initialization history (§59) -/

/-- Operation `op` writes leaf `l` from state `s` (§59): `write3` or `writeShared` of a list
containing `l`, `store` into `l`, or a `transfer` of which `l` is a destination leaf
corresponding to a source leaf `Init` before the step. -/
def KernelOp.Writes (s : S3) (l : Nat) : KernelOp → Prop
  | .write _ ls => l ∈ ls
  | .writeShared _ ls => l ∈ ls
  | .store _ p => l = p
  | .transfer src dst => l ∈ footprint s.P dst ∧
      ∃ l' ∈ footprint s.P src, corr s.P src dst l' = some l ∧ s.I l' = .init
  | _ => False

/-- In every `ok` step, a leaf that becomes `Init` is written by the step (§59): a permitted write
(`write3`, `writeShared`, `store`) or a transfer from a corresponding source leaf already
`Init`. -/
theorem init_only_by_writes {k : K} {op : KernelOp} {s s' : S3} {l : Nat}
    (h : op.Step k s (.ok s')) (hl : s.I l ≠ .init) (hl' : s'.I l = .init) : op.Writes s l := by
  cases op with
  | derive => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | split => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | release a =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    unfold releaseEff at hl'; split at hl' <;> exact absurd hl' hl
  | transfer src dst =>
    obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
    have e : (transferEff s src dst).I l = if l ∈ footprint s.P dst then .init
        else if l ∈ footprint s.P src then .moved else s.I l := rfl
    rw [e] at hl'
    split at hl'
    · rename_i hld
      obtain ⟨hlP, hleaf, hlp⟩ := mem_footprint.1 hld
      obtain ⟨r, hr, hrs, hc⟩ := hpre.sameShape.2 l (List.mem_range.2 hlP) hlp
      have h1 := hpre.sameShape.1 r hr hrs
      rw [hc] at h1
      have hkr : kids s.P r = [] := by
        have : (kids s.P l).length = 0 := by rw [kids_nil_iff.2 hleaf]; rfl
        exact List.eq_nil_of_length_eq_zero (by simp only [OptP] at h1; omega)
      have hrf : r ∈ footprint s.P src :=
        mem_footprint.2 ⟨List.mem_range.1 hr, kids_nil_iff.1 hkr, hrs⟩
      exact ⟨hld, r, hrf, hc, hpre.srcInit r hrf⟩
    · split at hl'
      · cases hl'
      · exact absurd hl' hl
  | depend => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | enter ps ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    have e : (enterEff s ps ls).I l = if s.P.length ≤ l then .uninit else s.I l := rfl
    rw [e] at hl'; split at hl'
    · cases hl'
    · exact absurd hl' hl
  | exit => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | read => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | write a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    have e : (write3Eff s ls).I l = if l ∈ ls then .init else s.I l := rfl
    rw [e] at hl'; split at hl'
    · assumption
    · exact absurd hl' hl
  | writeShared a ls =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    have e : (write3Eff s ls).I l = if l ∈ ls then .init else s.I l := rfl
    rw [e] at hl'; split at hl'
    · assumption
    · exact absurd hl' hl
  | pin => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | unpin => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | endUse p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    have e : (endUseEff s p).I l = if l ∈ footprint s.P p then .uninit else s.I l := rfl
    rw [e] at hl'; split at hl'
    · cases hl'
    · exact absurd hl' hl
  | free => obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h; exact absurd hl' hl
  | alloc pr ow ls =>
    cases h with
    | ok _ _ =>
      have e : (allocEff s ow ls).I l = if s.P.length ≤ l then .uninit else s.I l := rfl
      rw [e] at hl'; split at hl'
      · cases hl'
      · exact absurd hl' hl
  | store a p =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 h
    show l = p
    refine Decidable.byContradiction fun ne => hl ?_
    unfold storeEff at hl'
    split at hl'
    · simpa [ne] using hl'
    · exact hl'

/-- Every `Init` leaf of a state reached by a run from `S3.init statics` was declared `Init`
(§47) or was made `Init` by a write step of that run (§59): a step `t → t'` of the run, through
an operation writing the leaf, after which the run continues from `t'` to the final state. -/
theorem init_history {k : K} {statics : Statics} {s : S3} {l : Nat}
    (h : KStar k (S3.init statics) s) (hl : s.I l = .init) :
    (∃ e, statics[l]? = some e ∧ e.2 = true) ∨
      ∃ (t t' : S3) (op : KernelOp), KStar k (S3.init statics) t ∧ op.Step k t (.ok t') ∧
        t.I l ≠ .init ∧ t'.I l = .init ∧ op.Writes t l ∧ KStar k t' s := by
  induction h with
  | refl => exact .inl ((init_statics statics l).1 hl)
  | tail ht hst ih =>
    rename_i t u
    by_cases htl : t.I l = .init
    · rcases ih htl with hd | ⟨t₀, t₀', op, h₀, hs₀, hn₀, hi₀, hw₀, h₀'⟩
      · exact .inl hd
      · exact .inr ⟨t₀, t₀', op, h₀, hs₀, hn₀, hi₀, hw₀, .tail h₀' hst⟩
    · obtain ⟨op, hop⟩ := kstep_iff.1 hst
      exact .inr ⟨t, u, op, ht, hop, htl, hl, init_only_by_writes hop htl hl, .refl⟩

end Ern.MemoryModel.Access
