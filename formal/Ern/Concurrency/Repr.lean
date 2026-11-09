import Ern.MemoryModel.Refinement
import Ern.Concurrency.Context

/-!
# Representation relation of the concurrent state (WC4 C2, C25; Spec 1 §82.1)

* `ReprC`: the representation relation `Repr` of `Ern.MemoryModel.Refinement` (Spec 1 §82.1,
  §82.3–§82.5) read on the kernel components of `S_C` with the globally live frames
  (`SC.flat`, WC4 C2).
* `repr_congr`, `repr_frames_congr`: `Repr` reads the frame stack only through membership; it
  depends neither on the order of the frames of `flat` nor on the executing context
  (`reprC_view`). Spec 1 §39: frames have "no particular runtime representation"; §9: "The
  abstract machine is *flat*".
-/

namespace Ern.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-- The representation relation of `S_C` (WC4 C2, C25; Spec 1 §82.1, §82.3, §82.4, §82.5): `Repr`
of `Ern.MemoryModel.Refinement` between the kernel components of `s`, with the globally live
frames as the stack (`SC.flat`), and a state of the memory machine. -/
def ReprC (L : Layout) (rtok : Nat → Nat) (s : SC) (m : Machine.State) : Prop :=
  Repr L rtok s.flat m

/-- `Repr` (Spec 1 §82.1, §82.3–§82.5) reads the places, the initialization states, the death
markers and the stack, the stack only through membership (Spec 1 §40: usability). -/
theorem repr_congr {L : Layout} {rtok : Nat → Nat} {t t' : S3} {m : Machine.State}
    (hR : Repr L rtok t m) (hP : t'.P = t.P) (hI : t'.I = t.I) (hd : t'.dead = t.dead)
    (hF : ∀ f, f ∈ t'.F ↔ f ∈ t.F) : Repr L rtok t' m :=
  hR.transport hR.adm (Dom.refl _) (by rw [hP]) (by rw [hP])
    (fun r hr hu => hR.live r hr
      (S3.Usable.mono (s := t) (s' := t') hP (fun f hf => (hF f).1 hf) (fun q h => hd ▸ h) hu))
    fun _ _ _ h => .inl (hI ▸ h)

/-- `Repr` depends on the stack only through membership (Spec 1 §39, §9): it holds for the same kernel components with any stack
listing the same frames, in any order. -/
theorem repr_frames_congr {L : Layout} {rtok : Nat → Nat} {t : S3} {F' : Frames}
    {m : Machine.State} (hF : ∀ f, f ∈ F' ↔ f ∈ t.F) :
    Repr L rtok { t with F := F' } m ↔ Repr L rtok t m :=
  ⟨fun h => repr_congr (t' := t) h rfl rfl rfl fun f => (hF f).symm,
   fun h => repr_congr (t' := { t with F := F' }) h rfl rfl rfl hF⟩

/-- `ReprC` does not depend on the executing context (WC4 C2; Spec 1 §39, §9): it is `Repr` on the
view of any context. -/
theorem reprC_view {L : Layout} {rtok : Nat → Nat} {s : SC} {m : Machine.State} (c : Nat) :
    ReprC L rtok s m ↔ Repr L rtok (s.view c) m :=
  (repr_frames_congr (t := s.flat) (F' := (s.view c).F) fun _ => SC.mem_view_F).symm

/-- `ReprC` after writing back kernel components `t` that list the globally live frames (WC4 C2):
it is `Repr` on `t`. -/
theorem reprC_set {L : Layout} {rtok : Nat → Nat} {s : SC} {t : S3} {m : Machine.State}
    (hF : ∀ f, f ∈ t.F ↔ f ∈ s.frames) : ReprC L rtok (s.set t) m ↔ Repr L rtok t m :=
  repr_frames_congr (t := t) (F' := s.frames) fun f => (hF f).symm

/-- `ReprC` of a single-context state is `Repr` of its projection (WC4 C24). -/
theorem reprC_ofS3 {L : Layout} {rtok : Nat → Nat} {t : S3} {m : Machine.State} :
    ReprC L rtok (SC.ofS3 t) m ↔ Repr L rtok t m := by
  have hF : (SC.ofS3 t).flat = { t with F := (SC.ofS3 t).frames } := rfl
  unfold ReprC
  rw [hF]
  exact repr_frames_congr fun f => by simp [SC.frames, SC.ofS3, SC.stk]

end Ern.Concurrency
