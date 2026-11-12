import Ern.Concurrency.FullEncap.Capacity
import Ern.Concurrency.FullEncap.Witness

/-!
# The `resetLock` exception

Brief of milestone 4, slice 3, task 6 (WC5.2 C22 item 6, `resetLock` exception; C18 items 1 and
4): on a `RunFull` from the initial state, every `resetLock(e)` step has a right on the `slot` of
`e`, and on its controller, whose holder chain contains the `guarded` of no live entry other than
`e`.

The guard-free form of C18 item 1 (`ResetExerG`) poses the chain condition by definition; what is
proved is that it yields a right on the `slot`: the `guarded` of a live entry is held by a usable
place (WC5.2 C21 item 1, `SyncInv`), so its exercise goes through the third clause of Spec 1 §43.
The controller right has a chain without any live `guarded` (`CtrlRight5`, the guard-free form of
C18 item 4), a fortiori without that of another live entry.
-/

set_option autoImplicit false

namespace Ern.Concurrency.FullEncap

open Ern.MemoryModel Ern.MemoryModel.Access Ern.Concurrency Ern.Concurrency.MutexReal

/-- `Exer5` is antitone in the registry: removing entries removes exclusions. -/
theorem exer5_of_sub {s : SC} {reg reg' : SyncReg} {c a : Nat} {m : Mode}
    (hsub : ∀ e ∈ reg', e ∈ reg) (h : Exer5 s reg c a m) : Exer5 s reg' c a m := by
  induction h with
  | base hg hy ha hm hf => exact .base (fun e he => hg e (hsub e he)) hy ha hm hf
  | held hg hy ha hm hp _ hc ih => exact .held (fun e he => hg e (hsub e he)) hy ha hm hp ih hc

/-- The argument of an `Exer5` exists. -/
theorem exer5_lt {s : SC} {reg : SyncReg} {c a : Nat} {m : Mode} (h : Exer5 s reg c a m) :
    a < s.A.length := by
  cases h with
  | base _ hy => exact lt_of_getElem? hy
  | held _ hy => exact lt_of_getElem? hy

/-- The right of the step on the `slot` of entry `i` and on its controller, each by a holder chain
containing the `guarded` of no live entry other than entry `i` (`Exer5` over the registry without
entry `i`; WC5.2 C22 item 6, `resetLock` exception). -/
def ResetRights (L : MutexLayout) (st : SC × SyncReg) (c i : Nat) : Prop :=
  OptP (st.2[i]?) (fun e =>
    OptP (slotOf st.1 e.guarded) (fun q => ∃ b ∈ List.range st.1.A.length,
      Exer5 st.1 (st.2.eraseIdx i) c b .modify ∧
        ∀ l ∈ footprint st.1.P q, Allows (effective st.1.flat b l) .modify) False ∧
    OptP (ControlOf L st.1 e) (fun ctl => ∃ a ∈ List.range st.1.A.length,
      Exer5 st.1 (st.2.eraseIdx i) c a .observe ∧ effective st.1.flat a ctl ≠ none) False) False

/-- Decidability of `ResetRights`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (c i : Nat) : Decidable (ResetRights L st c i) := by
  unfold ResetRights; infer_instance

/-- Step form of task 6: under `SyncInv` (WC5.2 C21 item 1), the guard-free forms of C18 items 1
and 4 give the rights of `ResetRights`. -/
theorem resetRights_of_premG {k : K} {L : MutexLayout} {st : SC × SyncReg × ArenaReg} {c i : Nat}
    (hinv : SyncInv L st.1 st.2.1) (hp : PremG k L st (.resetLock c i)) :
    ResetRights L (st.1, st.2.1) c i := by
  obtain ⟨s, reg, ar⟩ := st
  obtain ⟨hx, hc⟩ := hp
  simp only [ResetExerG] at hx
  show OptP (reg[i]?) _ False
  revert hx hc
  cases hi : reg[i]? with
  | none => exact fun h _ => h
  | some e =>
    intro hx₀ hc₀
    have hx : Exer5 s (reg.eraseIdx i) c e.guarded .modify := hx₀
    have hc : CtrlRight5 L (s, reg) e c := hc₀
    have he : e ∈ reg := List.mem_of_getElem? hi
    refine ⟨?_, ?_⟩
    · cases hx with
      | @base _ _ y hg hy ha hm hf =>
        have hl : e.Live s := ⟨y, hy, ha⟩
        have hg' := hinv.guarded e he hl
        rw [hy] at hg'
        have hg2 : PlaceUsable s.flat y.holder := hg'.2
        rw [hf] at hg2
        exact hg2.elim
      | @held _ q b _ y hg hy ha hm hq hb hall =>
        have hs : slotOf s e.guarded = some q := by
          unfold slotOf; rw [hy]; simp [hq]
        rw [hs]
        exact ⟨b, List.mem_range.2 (exer5_lt hb), hb, hall⟩
    · unfold CtrlRight5 at hc
      revert hc
      cases ControlOf L s e with
      | none => exact id
      | some ctl =>
        rintro ⟨a, ha, hx', he'⟩
        exact ⟨a, ha, exer5_of_sub (fun x hx => List.mem_of_mem_eraseIdx hx) hx', he'⟩

/-- Brief of slice 3, task 6: on a `RunFull` from the initial state, under `DDSound`, every step
`resetLock(i)` by `c` has a right on the `slot` of entry `i` and on its controller whose holder
chain contains the `guarded` of no live entry other than entry `i`. -/
theorem resetLock_rights {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (h : RunFull k L σ lbls) {j : Nat} (hj : j < lbls.length) {c i : Nat}
    (hl : lbls[j] = .resetLock c i) : ResetRights L ((σ j).1, (σ j).2.1) c i := by
  have hinv := (runFull_inv hdd hstat h0 h (Nat.le_of_lt hj)).2.1.1
  have hp := (h j hj).1.2
  rw [hl] at hp
  exact resetRights_of_premG hinv hp

/-- `corpus-spec2-m3.md` v13 §2 duodecies W-RX: in twin B, the `resetLock(e_n)` step has both
rights through `g`; in step A, neither right exists without the `guarded` of `e`, and W-RL's
`resetLock(e)` has both through `root_M`. -/
theorem resetRights_witnesses :
    ResetRights Traces.L0 (Witness.rx5, Witness.rxRegG) 0 0 ∧
    ¬ ResetRights Traces.L0 (Witness.rx4, Witness.rxReg) 0 0 ∧
    ResetRights Traces.L0 ((Corpus.MutexEdge.rlσ 9).1, (Corpus.MutexEdge.rlσ 9).2.1) 0 0 := by
  decide

end Ern.Concurrency.FullEncap
