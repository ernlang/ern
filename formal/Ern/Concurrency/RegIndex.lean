import Ern.Concurrency.Encap5C

/-!
# Stability of the index of a registry entry

Brief of milestone 4, strict mutex edge, task 6 (`formal/reports/spec2-m4-events.md`, écart 5 of
the event pass): along the `ok` steps of a trace, the synchronization registry never shortens, and
the entry at a given index keeps the same `guarded` identity. `NewMutexOk` registers the entry of
WC5.1 C13 at the end; `AcquireOk`, `UnlockOk` and `ResetLockOk` record the grant of WC5.1 C16, C17,
C18 in the entry at their index, in place; every other step keeps the registry.
-/

namespace Ern.Concurrency

open Ern.MemoryModel.Access

/-- Rewriting an entry in place with the same `guarded` identity keeps the length of the registry
and the `guarded` identity at every index. -/
theorem reg_set_guarded {reg : SyncReg} {i : Nat} {e e' : SyncEntry} (he : reg[i]? = some e)
    (hg : e'.guarded = e.guarded) : reg.length ≤ (reg.set i e').length ∧
      ∀ j : Nat, j < reg.length →
        ((reg.set i e')[j]?).map SyncEntry.guarded = (reg[j]?).map SyncEntry.guarded := by
  refine ⟨Nat.le_of_eq List.length_set.symm, fun j _ => ?_⟩
  by_cases hij : i = j
  · subst hij
    have hi : i < reg.length := (List.getElem?_eq_some_iff.1 he).1
    rw [List.getElem?_set_self hi, he, Option.map_some, Option.map_some, hg]
  · rw [List.getElem?_set_ne hij]

/-- One `ok` step never shortens the registry and keeps the `guarded` identity at every existing
index. -/
theorem lstep_reg {k : K} {L : MutexLayout} {lbl : Label} {st st' : SC × SyncReg × ArenaReg}
    (h : LStep k L lbl st st') : st.2.1.length ≤ st'.2.1.length ∧
      ∀ j : Nat, j < st.2.1.length →
        (st'.2.1[j]?).map SyncEntry.guarded = (st.2.1[j]?).map SyncEntry.guarded := by
  cases h with
  | newMutex hn =>
    obtain ⟨-, -, rfl⟩ := hn
    refine ⟨by simp, fun j hj => ?_⟩
    show ((_ ++ _)[j]?).map _ = _
    rw [List.getElem?_append_left hj]
  | acquire ha =>
    obtain ⟨-, e, he, -, -, rfl⟩ := ha
    exact reg_set_guarded he rfl
  | unlock hu =>
    obtain ⟨-, e, _, he, -, -, -, -, rfl⟩ := hu
    exact reg_set_guarded he rfl
  | resetLock hr =>
    obtain ⟨-, e, he, -, -, -, rfl⟩ := hr
    exact reg_set_guarded he rfl
  | kernel => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | spawn => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | terminate => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | join => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | deriveSync => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | spawnVal => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | newArena => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | issue => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | reset => exact ⟨Nat.le_refl _, fun _ _ => rfl⟩

/-- Brief, task 6: along the `ok` steps of a trace, from position `a` to any later position `b`,
the registry never shortens and the entry at every index existing at `a` keeps its `guarded`
identity. -/
theorem reg_stable {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hs : ∀ i (h : i < lbls.length), LStep k L lbls[i] (σ i) (σ (i + 1)))
    {a : Nat} : ∀ b, a ≤ b → b ≤ lbls.length → (σ a).2.1.length ≤ (σ b).2.1.length ∧
      ∀ j : Nat, j < (σ a).2.1.length →
        ((σ b).2.1[j]?).map SyncEntry.guarded = ((σ a).2.1[j]?).map SyncEntry.guarded
  | 0, hab, _ => by
    obtain rfl := Nat.le_zero.1 hab
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  | b + 1, hab, hb => by
    rcases Nat.lt_or_ge b a with h | h
    · obtain rfl : a = b + 1 := by omega
      exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    · obtain ⟨h1, h2⟩ := reg_stable hs b h (by omega)
      obtain ⟨h3, h4⟩ := lstep_reg (hs b (by omega))
      exact ⟨Nat.le_trans h1 h3, fun j hj => (h4 j (Nat.lt_of_lt_of_le hj h1)).trans (h2 j hj)⟩

/-- Brief, task 6: `reg_stable` along every `Run5C`. -/
theorem reg_stable_run5C {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (hr : Run5C k L σ lbls) {a b : Nat} (hab : a ≤ b) (hb : b ≤ lbls.length) :
    (σ a).2.1.length ≤ (σ b).2.1.length ∧ ∀ j : Nat, j < (σ a).2.1.length →
      ((σ b).2.1[j]?).map SyncEntry.guarded = ((σ a).2.1[j]?).map SyncEntry.guarded :=
  reg_stable (fun i h => (hr i h).2) b hab hb

end Ern.Concurrency
