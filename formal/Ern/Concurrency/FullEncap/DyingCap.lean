import Ern.Concurrency.FullEncap.LastAcquire

/-!
# No other context has a capacity on a dying leaf

Brief of milestone 4, slice 3, complement, task 3, second fact (`corpus-spec2-m3.md` v14
§2 terdecies, "Feuilles qui meurent"): in the state before a step of a context `c`, no context
other than `c` has a `cap5` (WC5.2 C43) on a leaf that dies in the step.

After the step, no context has a `cap5` on such a leaf: an attaining authority would be active
and cover it, against `NoDangling` (Spec 1 §54) after the step. A context other than `c` with a
`cap5` before the step would then have lost it in a step of `c`, which L1 forbids
(`cap5_drop_own`, WC5.2 C45, proved for the 28 kinds on `EncapsulatedTrace5`, which every prefix
of a `RunFull` is).
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal
open SyncPreserveAux SyncInitAux TransferPreserveAux

/-- After a step, no context has a `cap5` on a leaf that died in it, when `NoDangling` holds after
the step (Spec 1 §54) and the step keeps leaves leaves (`PSkel`). -/
theorem cap5_none_after {s s' : SC} {reg : SyncReg} {c l : Nat} (hP : PSkel s.P s'.P)
    (hnd : NoDangling s'.flat) (hd : Dying s s' l) : cap5 s' reg c l = none := by
  cases hc : cap5 s' reg c l with
  | none => rfl
  | some m =>
    exfalso
    have hal : Allows (cap5 s' reg c l) .observe := by rw [hc]; exact Or.inl rfl
    obtain ⟨x, -, -, hex⟩ := cap5_attained hal
    obtain ⟨z, hz, za, hlz, -⟩ := eff_present (ne_none_of_allows hex)
    obtain ⟨hleaf, hu, hu'⟩ := hd
    have hlt := hu.lt
    have hleaf' : isLeaf s'.P l := (hP.isLeaf hlt).2 hleaf
    have hmem : l ∈ footprint s'.flat.P l :=
      (Arena.mem_footprint_leaf hleaf' (Nat.lt_of_lt_of_le hlt hP.1)).2 rfl
    exact hnd x z hz za l hu' l hmem hlz

/-- A prefix of a `RunFull` is a `Run5R`. -/
theorem run5R_take {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunFull k L σ lbls) (n : Nat) : Run5R k L σ (lbls.take n) :=
  fun i hi => by
    have hi' : i < lbls.length := by simp at hi; omega
    have e : (lbls.take n)[i] = lbls[i] := List.getElem_take
    rw [e]
    exact ⟨(h i hi').1.1.1, (h i hi').2⟩

/-- Brief of the complement, task 3, second fact: on a `RunFull` from the initial state, under
`DDSound`, in the state before a step, no context other than the acting one has a `cap5` on a
leaf that dies in the step. Invariants and results used: `NoDangling` after the step (Spec 1
§54), `PSkel` of the step, and L1 (`cap5_drop_own`, WC5.2 C45). -/
theorem other_cap_dying_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) {c' l : Nat}
    (hc' : c' ≠ lbls[i].ctx) (hd : Dying (σ i).1 (σ (i + 1)).1 l) :
    cap5 (σ i).1 (σ i).2.1 c' l = none := by
  obtain ⟨hk, hlib⟩ := runFull_inv hdd hstat h0 h (Nat.le_of_lt hi)
  obtain ⟨hk', -⟩ := runFull_inv hdd hstat h0 h hi
  obtain ⟨-, hP⟩ := shape_step hk hlib.2.1 (h i hi).1.1.1.1.1 (h i hi).2
  have hafter := cap5_none_after (reg := (σ (i + 1)).2.1) (c := c') hP hk'.1.2.1.2.2 hd
  cases hb : cap5 (σ i).1 (σ i).2.1 c' l with
  | none => rfl
  | some m =>
    exfalso
    have htr5R := run5R_trace (run5R_take h i)
    have hlen : (lbls.take i).length = i := by simp; omega
    rw [hlen, h0] at htr5R
    have htr := encapsulatedTrace5C_imp (encapsulatedTrace5R_imp htr5R)
    have he5C := (h i hi).1.1.1.1
    have he5 : Encap5 L ((σ i).1, (σ i).2.1) lbls[i] :=
      ⟨he5C.1, chainExcl_guardedExcl he5C.2.1, he5C.2.2⟩
    have hdrop : capRank (cap5 (σ (i + 1)).1 (σ (i + 1)).2.1 c' l) <
        capRank (cap5 (σ i).1 (σ i).2.1 c' l) := by
      rw [hafter, hb]; cases m <;> decide
    exact hc' (cap5_drop_own hdd statics (lbls.take i) (σ i) (σ (i + 1)) lbls[i] c' l hstat htr
      he5 (h i hi).2 hdrop).symm

/-- `OtherCapFree`, the decidable form checked by the sweep, holds at every step of a `RunFull`
from the initial state under `DDSound` (brief of the complement, task 3, second fact). -/
theorem otherCapFree_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {i : Nat} (hi : i < lbls.length) :
    OtherCapFree (σ i) lbls[i] (σ (i + 1)) :=
  fun _ _ hc' _ _ hd => other_cap_dying_run hdd hstat h0 h hi hc' hd

end Ern.Concurrency.FullEncap
