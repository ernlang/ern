import Ern.Concurrency.MutexReal.Final
import Ern.Concurrency.MutexReal.ResetAmend

/-!
# Authority of the protocol in a final amended execution

Brief of milestone 4, slice 2, layer R, final pass, task 5: in a final amended execution, every
`newMutex` step is made by a frame with exercisable `Modify` and effective `Modify` on the
controller (proposed C13 item 11), and every `acquire`, `unlock` or `resetLock` step by a frame with
a present effective mode on the controller (WC5.1 corrigé C14 item 3, C17 item 4; proposed C18
item 4).
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency

/-- Brief, final pass, task 5: in a final amended execution, every step `newMutex(g)` by `c` is made
by a frame with an authority exercisable in `Modify` and of effective `Modify` on the controller
`ControlOf(⟨g, none⟩)` of the registered entry (proposed C13 item 11). -/
theorem runAmF_newMutex_authority {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {j : Nat} (hj : j < lbls.length) {c g : Nat}
    (hl : lbls[j] = .newMutex c g) : NewMutexRight L (σ j).1 c g := by
  have ha := h.2 j hj
  rw [hl] at ha
  exact ha

/-- Brief, final pass, task 5: in a final amended execution, every step `acquire(i)`, `unlock(i)` or
`resetLock(i)` by `c` is made by a frame with a present effective mode on `ControlOf(i)`
(`protocol_authority`: C14 item 3 and C17 item 4 in the step relation, the proposed C18 item 4 in
`AmCondF`). -/
theorem runAmF_protocol_authority {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : RunAmF k L σ lbls) {j : Nat} (hj : j < lbls.length) {c i : Nat}
    (hp : lbls[j] = .acquire c i ∨ lbls[j] = .unlock c i ∨ lbls[j] = .resetLock c i) :
    OptP ((σ j).2.1[i]?) (fun e => CtrlRight L (σ j).1 e ((σ j).1.view c).top) False :=
  ResetAmend.protocol_authority (h.1 j hj).2 (amCond_of_amCondF (h.2 j hj)) hp

end Ern.Concurrency.MutexReal
