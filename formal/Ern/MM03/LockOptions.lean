import Ern.MM03.Horrors

/-!
# Measure of the `NoLock` options (jalon 3, step 4)

The options of the jalon-3 material (`ERN_Jalon3_materiel.md` v2, §5), measured on the kernel as it
is (option 1, no rule), without modifying it:

* option 2, a local rule: an operation does not place an authority into a place it covers
  (`SelfLock`); `store` already rejects it (O8.3), so the rule is measured on `transfer` and
  `issue` (`opt2`);
* option 3, `NoLock`: no self-lock, as a separate clause, and the relation "`b` blocks `a`"
  (`Blocks`) acyclic, checked on the arrival state of `transfer`, `issue` and `store` (`opt3`).

For each case of the list "doit être accepté" of §5 (H11, H19, H29b, H35 to H37, H44 to H47, W1
to W3) and for H49 to H51, `decisions` gives the decision of an option on each `transfer`, `issue`
and `store` of the run of the case (`Ern.MM03.Horrors`), decided on the state where the step runs;
`true` is acceptance. The cost, measured as the brief asks (from the authorities and places the
operation touches, or the whole state): option 2 on `transfer` depends on the state only through the
places and the authorities the transfer moves (`opt2_transfer_local`), on `issue` only through the
region and the destination (`opt2_issue_local`); option 3 depends on authorities the operation does
not touch (`opt3_not_local`). Whether option 3 needs more than the function where the operation runs
(material §5, "locale à une fonction") is not settled here (report, (g)). No option is adopted
(material §5: "la décision revient à l'arbitrage").
-/

namespace Ern.MM03.LockOptions

open Ern.MM03 Ern.HandlePool Ern.MM03.Horrors

/-! ## Option 2: self-lock -/

/-- The leaves of a holder (MM-03.3.4): those of a place, none for a frame. -/
def holderLeaves (s : S3) : Holder → List Nat
  | .place p => footprint s.P p
  | .frame _ => []

/-- Self-lock of the authority `a` (material §5, options 2 and 3): `a` is active and held by a place
one of whose leaves it covers. -/
def SelfLock (s : S3) (a : Nat) : Prop :=
  OptP (s.A[a]?) (fun y => y.active = true ∧ ∃ l ∈ y.footprint, l ∈ holderLeaves s y.holder) False

instance (s : S3) (a : Nat) : Decidable (SelfLock s a) := by unfold SelfLock; infer_instance

/-- Option 2 on `transfer src dst` (material §5): no authority moved by the transfer, one held within
the source, is self-locked in the arrival state. -/
def Opt2Transfer (s : S3) (src dst : Nat) : Prop :=
  ∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (fun y => heldIn s.P src y.holder) False →
    ¬ SelfLock (transferEff s src dst) j

instance (s : S3) (src dst : Nat) : Decidable (Opt2Transfer s src dst) := by
  unfold Opt2Transfer; infer_instance

/-- Option 2 on `issue` of `region` to `dst` (material §5): the block, the new authority, is not
self-locked in the arrival state. -/
def Opt2Issue (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) : Prop :=
  ¬ SelfLock (issueEff s ar region dst).1 s.A.length

instance (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) :
    Decidable (Opt2Issue s ar region dst) := by
  unfold Opt2Issue; infer_instance

/-! ## Option 3: `NoLock` -/

/-- "`b` bloque `a`" (material §5, option 3): `b ≠ a`, both active, and the footprint of `b` contains
a leaf of the holder of `a`. -/
def Blocks (s : S3) (b a : Nat) : Prop :=
  b ≠ a ∧ s.Active b ∧ s.Active a ∧
    OptP (s.A[a]?) (fun y => ∃ l ∈ s.afp b, l ∈ holderLeaves s y.holder) False

instance (s : S3) (b a : Nat) : Decidable (Blocks s b a) := by unfold Blocks; infer_instance

/-- The authorities blocked by one of `xs`. -/
def blockedBy (s : S3) (xs : List Nat) : List Nat :=
  (List.range s.A.length).filter fun a => decide (∃ b ∈ xs, Blocks s b a)

/-- The authorities reached from `xs` by at most `n` steps of `Blocks`, `xs` included. -/
def blockReach (s : S3) : Nat → List Nat → List Nat
  | 0, xs => xs
  | n + 1, xs => blockReach s n (xs ++ blockedBy s xs)

/-- Acyclicity of `Blocks` (material §5, option 3): no authority is reached from itself by one or
more steps. Every step leads to an authority of `A`, so a cycle has at most `A.length` steps and the
search with that bound is complete (report, (f)). -/
def BlocksAcyclic (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, a ∉ blockReach s s.A.length (blockedBy s [a])

instance (s : S3) : Decidable (BlocksAcyclic s) := by unfold BlocksAcyclic; infer_instance

/-- `NoLock` (material §5, option 3): no self-lock (separate clause) and `Blocks` acyclic. -/
def NoLock (s : S3) : Prop :=
  (∀ a ∈ List.range s.A.length, ¬ SelfLock s a) ∧ BlocksAcyclic s

instance (s : S3) : Decidable (NoLock s) := by unfold NoLock; infer_instance

/-! ## Decisions along the runs -/

/-- Option 2 on an operation from the extended state `ps` (`true`: accepted by the rule). Only
`transfer` and `issue` are checked; `store` is left to O8.3. -/
def opt2 (ps : PS) : Op → Bool
  | .transfer src dst => decide (Opt2Transfer ps.s src dst)
  | .issue i _ region dst =>
    match ps.s.arenas[i]? with
    | some ar => decide (Opt2Issue ps.s ar region dst)
    | none => true
  | _ => true

/-- Option 3 on an operation from `ps` (`true`: accepted by the rule): `NoLock` of the arrival
state of `transfer`, `issue` and `store`. -/
def opt3 (ps : PS) : Op → Bool
  | .transfer src dst => decide (NoLock (transferEff ps.s src dst))
  | .issue i _ region dst =>
    match ps.s.arenas[i]? with
    | some ar => decide (NoLock (arenaSet (issueEff ps.s ar region dst).1 i
        (issueEff ps.s ar region dst).2))
    | none => true
  | .store a p => decide (NoLock (storeEff ps.s a p))
  | _ => true

/-- The operations checked by the options: `transfer`, `issue`, `store`. -/
def checked : Op → Bool
  | .transfer .. => true
  | .issue .. => true
  | .store .. => true
  | _ => false

/-- The decisions of the option `D` on the checked steps of a run of `K0` from `ps`, each on the
state where the step runs, in order, as long as the steps are `ok` in the kernel. -/
def decisions (D : PS → Op → Bool) (ps : PS) : List Op → List Bool
  | [] => []
  | o :: os =>
    match pexec K0 ps o with
    | some ps' => (if checked o then [D ps o] else []) ++ decisions D ps' os
    | none => []

/-- The run from `S3.init []` of a case. -/
def dec2 (os : List Op) : List Bool := decisions opt2 (PS.init []) os
def dec3 (os : List Op) : List Bool := decisions opt3 (PS.init []) os

/-! ## Cases that must be accepted (material §5) -/

/-- The runs of the cases that must be accepted, with their names: each is a run of
`Ern.MM03.Horrors` reached under `K0`, except H21's arena which is not on the list. -/
def mustAccept : List (String × List Op) :=
  [("H11", h11p ++ [.endUse 3, .endUse 6, .reset 0 0]),
   ("H19", h19p ++ [.endUse 2, .reset 0 0]),
   ("H29b", h29bo), ("H35", h35o), ("H36", h36o), ("H37", h37o), ("H44", h44o),
   ("H45", h45o), ("H46", h46o), ("H47", h47o), ("W1", w1o),
   ("W2", w2o ++ [.release 12, .release 11, .release 10, .transfer 9 16, .transfer 12 19]),
   ("W3", w3o ++ [.endUse 5, .endUse 2, .endUse 3, .endUse 4, .reset 0 0, .issue 0 0 [10] 2]),
   ("W3v", w3vo ++ [.endUse 2, .reset 0 0, .issue 0 0 [10] 3])]

/-- Every run of the list is `ok` in the kernel at each step, so the decisions cover all its
checked steps. -/
theorem mustAccept_runs : mustAccept.all (fun c => (prun K0 (PS.init []) c.2).isSome) = true := by
  decide

/-- The decisions of option 2 on the checked steps of each case. -/
theorem opt2_decisions : mustAccept.map (fun c => (c.1, dec2 c.2)) =
    [("H11", [true, true, true]), ("H19", [true]), ("H29b", [true]), ("H35", []),
     ("H36", []), ("H37", [true]), ("H44", [true]), ("H45", [true, true, true, true]),
     ("H46", [true]), ("H47", [true]), ("W1", []), ("W2", [true, true]),
     ("W3", [true, true, true, true, true, true, true]), ("W3v", [true, true, true, true, true, true, true])] := by
  decide

/-- The decisions of option 3 on the checked steps of each case. -/
theorem opt3_decisions : mustAccept.map (fun c => (c.1, dec3 c.2)) =
    [("H11", [true, true, true]), ("H19", [true]), ("H29b", [true]), ("H35", []),
     ("H36", []), ("H37", [true]), ("H44", [true]), ("H45", [true, true, true, true]),
     ("H46", [true]), ("H47", [true]), ("W1", []), ("W2", [true, true]),
     ("W3", [true, true, true, true, true, true, true]), ("W3v", [true, true, true, true, true, true, true])] := by
  decide

/-- No false rejection (material §5, criterion): neither option rejects a checked step of a case that
must be accepted. -/
theorem no_false_rejection : mustAccept.all (fun c => (dec2 c.2).all id && (dec3 c.2).all id) =
    true := by
  decide

/-! ## Residual blockings (H49 to H51) -/

/-- H49 (the cycle closed through a helper then its `release`): option 2 accepts every checked step,
so the blocking of H49 remains; option 3 rejects the `store` that closes the cycle (the fourth checked
step), the helper notwithstanding. -/
theorem H49_options : dec2 h49o = [true, true, true, true] ∧
    dec3 h49o = [true, true, true, false] := by
  decide

/-- The state and the step of H49 where option 3 rejects: `store 8 6` with the helper 9 active; in
its arrival state, 7 and 8 block each other. -/
theorem H49_cycle : Blocks (storeEff (run K0 [] (h48o ++ [.derive 7 6 .modify])).s 8 6) 7 8 ∧
    Blocks (storeEff (run K0 [] (h48o ++ [.derive 7 6 .modify])).s 8 6) 8 7 :=
  by decide

/-- H50 (an authority transferred or issued into the place it covers): both options reject the
`transfer` and the `issue`, by the self-lock. -/
theorem H50_options : dec2 h50ao = [true, false] ∧ dec3 h50ao = [true, false] ∧
    dec2 h50bo = [false] ∧ dec3 h50bo = [false] := by
  decide

/-- H51 (an element of a storage owned by `v` holds a view on `v`): option 2 accepts the `store`, and
would even if it checked `store`: the view is not self-locked, the configuration being a cycle of
two authorities, which option 2 does not cover (material §5); the blocking remains. Option 3 rejects
the `store`: in its arrival state, the root of the storage, held by `v`, and the view, held by the
element, block each other. -/
theorem H51_options : dec2 h51o = [true] ∧ dec3 h51o = [false] ∧
    ¬ SelfLock (storeEff (run K0 [] (h51o.take 6)).s 4 3) 4 ∧
    Blocks (storeEff (run K0 [] (h51o.take 6)).s 4 3) 2 4 ∧
    Blocks (storeEff (run K0 [] (h51o.take 6)).s 4 3) 4 2 := by
  decide

/-! ## Cost of the check -/

/-- Locality of option 2 on `transfer`: the decision depends on the state only through the places and
the authorities held within the source, the ones the transfer moves. Two states with the same places
and the same such authorities, at the same identities, get the same decision. -/
theorem opt2_transfer_local {s s' : S3} {src dst : Nat} (hP : s'.P = s.P)
    (hA : ∀ (j : Nat) (y : Authority), (s.A[j]? = some y ∨ s'.A[j]? = some y) →
      heldIn s.P src y.holder → s'.A[j]? = s.A[j]?) :
    Opt2Transfer s' src dst ↔ Opt2Transfer s src dst := by
  have key : ∀ (t t' : S3), t'.P = t.P →
      (∀ (j : Nat) (y : Authority), (t.A[j]? = some y ∨ t'.A[j]? = some y) →
        heldIn t.P src y.holder → t'.A[j]? = t.A[j]?) →
      Opt2Transfer t src dst → Opt2Transfer t' src dst := by
    intro t t' hP hA h j hj hheld hsl
    obtain ⟨y, hy, hh⟩ := optP_false_iff.1 hheld
    rw [hP] at hh
    have e := hA j y (.inr hy) hh
    have hy' : t.A[j]? = some y := e.symm.trans hy
    refine h j (List.mem_range.2 (lt_of_getElem? hy')) (optP_false_iff.2 ⟨y, hy', hh⟩) ?_
    have ga : (transferEff t' src dst).A[j]? = (transferEff t src dst).A[j]? := by
      rw [transfer_A_get, transfer_A_get, e, hP]
    have gl : holderLeaves (transferEff t' src dst) = holderLeaves (transferEff t src dst) := by
      funext hd
      cases hd with
      | place p => simp only [holderLeaves, transferEff, hP]
      | frame f => rfl
    unfold SelfLock at hsl ⊢
    rw [ga, gl] at hsl
    exact hsl
  refine ⟨key s' s hP.symm (fun j y hy hh => ?_), key s s' hP hA⟩
  rw [hP] at hh
  exact (hA j y hy.symm hh).symm

/-- Option 2 on `issue` reads only the region and the destination: the block is self-locked exactly
when the destination's footprint meets the region. -/
theorem opt2_issue_local (s : S3) (ar : Arena) (region : List Nat) (dst : Nat) :
    Opt2Issue s ar region dst ↔ ¬ ∃ l ∈ region, l ∈ footprint s.P dst := by
  unfold Opt2Issue SelfLock
  simp only [issueEff, S3.addAuth, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self,
    List.getElem?_cons_zero, OptP, true_and, holderLeaves]

/-- The states of `opt3_not_local`: the state of H48 with the helper 9 (`Modify` on the node 6,
derived from 7), and the same run without the `store` of 7, which stays held by the frame. -/
def nl1 : PS := run K0 [] (h48o ++ [.derive 7 6 .modify])
def nl2 : PS := run K0 [] (fao ++ [.derive 6 6 .modify, .derive 5 5 .modify, .derive 7 6 .modify])

/-- Option 3 is not local to the operation: in two reached states where the kernel accepts
`store 8 6`, with the same places, the same stored authority 8 and as many authorities, the decisions
differ. The states differ by the authority 7, which the step does not touch (stored into the node 5
in the first, held by the frame in the second), and by the initialisation and anchors of the node 5,
which option 3 does not read. Both states are in one frame (report, (g)). -/
theorem opt3_not_local :
    PReach K0 [] nl1 ∧ PReach K0 [] nl2 ∧
    StoreStep 8 6 nl1.s (.ok (storeEff nl1.s 8 6)) ∧ StoreStep 8 6 nl2.s (.ok (storeEff nl2.s 8 6)) ∧
    nl1.s.P = nl2.s.P ∧ nl1.s.A[8]? = nl2.s.A[8]? ∧ nl1.s.A.length = nl2.s.A.length ∧
    nl1.s.A[7]? ≠ nl2.s.A[7]? ∧ nl1.s.F = nl2.s.F ∧
    ¬ NoLock (storeEff nl1.s 8 6) ∧ NoLock (storeEff nl2.s 8 6) :=
  ⟨run_reach (by decide) (by decide), run_reach (by decide) (by decide), .ok (by decide),
    .ok (by decide), by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

end Ern.MM03.LockOptions
