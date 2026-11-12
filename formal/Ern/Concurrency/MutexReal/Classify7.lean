import Ern.Concurrency.MutexReal.Final
import Ern.Concurrency.MutexReal.Classify6

/-!
# The classification replayed under the final footprint

Brief of milestone 4, slice 2, layer R, final pass, task 4
(`formal/reports/spec2-m4-mutexreal.md`, § Passe finale):

* `classified7_sound`: under `Encap7`, the kinds `exclu` and `fin de vie` and the three former
  counter-examples (`store`, `alloc`, `issue`) do not have the controller of an entry live before
  and after the step in their final footprint, and keep it. The first half is the final
  restriction itself (final C22 item 4); the second is proved (`classified_sound`,
  `cex_ctl_same`);
* `moveF_not_touch`: a move admitted by C22 item 3 that keeps the controller (hypothesis 3) does
  not have it in its final footprint;
* `completeness7`, `completeness7_run`: completeness without restriction of kind, stated on the
  final footprint alone, under hypothesis 3.

The proofs go through the lemmas at the level of `Encap5R` of the previous passes; the final
footprint is `Touches` on every label that is no `alloc` (`touchesF_of_not_alloc`).
-/

set_option autoImplicit false

namespace Ern.Concurrency.MutexReal

open Ern.MemoryModel.Access Ern.Concurrency
open SyncPreserveAux SyncInitAux

/-- Under the final restriction, a step that is no protocol step of entry `i` and no move admitted
by C22 item 3, after which entry `i` is still live, does not have its controller in its final
footprint (final C22 item 4). -/
theorem restrF_not_touch {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg} {lbl : Label}
    (h : CtlRestrF L st lbl st') {i : Nat} {x : SyncEntry} (hx : st.2.1[i]? = some x)
    (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl)
    (hp : ctlOp i lbl = none) (hm : ¬ C223Move L (st.1, st.2.1) lbl) :
    ¬ TouchesF L st lbl ctl := fun ht => by
  rcases h.apply hx hl hc ht with h1 | h1 | h1
  · exact h1 hp
  · exact hm h1
  · exact h1 hl'

/-- Brief, final pass, task 4: under `Encap7`, from a state satisfying `KInvCA`, `SyncState` and the
separation of the registries, to a state satisfying `WF3`, an `ok` step of a kind `exclu` or
`fin de vie`, or of a former counter-example kind, with entry `i` live before and after it, does
not have the controller of entry `i` in its final footprint and does not change it. The first
conclusion is the final restriction (final C22 item 4); the second is `classified_sound` and
`cex_ctl_same`. -/
theorem classified7_sound {k : K} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (hk : KInvCA st.1) (hw' : WF3 st'.1.flat)
    (hs : SyncState L st.1 st.2.1) (hsep : AdminSep st.1 st.2.1 st.2.2)
    (hkind : ExclKind lbl ∨ FinKind lbl ∨ CexKind lbl) (he : Encap7 k L st lbl st')
    (h : LStep k L lbl st st') {i : Nat} {x : SyncEntry} (hx : st.2.1[i]? = some x)
    (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat} (hc : ControlOf L st.1 x = some ctl) :
    ¬ TouchesF L st lbl ctl ∧ ControlOf L st'.1 x = some ctl := by
  obtain ⟨hp, hm⟩ := kind_not_proto (L := L) hkind
  refine ⟨restrF_not_touch he.2 hx hl hl' hc (hp i) (hm _), ?_⟩
  rcases hkind with hkind | hkind | hkind
  · exact (classified_sound hk hw' hs hsep (.inl hkind) he.1 h (List.mem_of_getElem? hx) hl hl'
      hc).2
  · exact (classified_sound hk hw' hs hsep (.inr hkind) he.1 h (List.mem_of_getElem? hx) hl hl'
      hc).2
  · exact cex_ctl_same hk hsep hkind he.1 h hl' hc

/-- A move admitted by C22 item 3 (`transfer`, by-value `spawn`) that keeps the controller of an
entry live before and after it (hypothesis 3) does not have it in its final footprint, which is
`Touches` on these labels: `transfer_fixed_sound`, `spawnVal_fixed_sound` (`move_not_touch`). -/
theorem moveF_not_touch {k : K} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep k L lbl st st') (he : Encap5R k L st lbl)
    (hm : C223Move L (st.1, st.2.1) lbl) (hk : KInvCA st.1) (hs : SyncState L st.1 st.2.1)
    {x : SyncEntry} (hx : x ∈ st.2.1) (hl : x.Live st.1) (hl' : x.Live st'.1) {ctl : Nat}
    (hc : ControlOf L st.1 x = some ctl) (hfix : ControlOf L st'.1 x = some ctl) :
    ¬ TouchesF L st lbl ctl := fun ht => by
  have hna : ∀ c pr ow ls, lbl ≠ .kernel c (.alloc pr ow ls) := by
    rintro c pr ow ls rfl
    simp [C223Move] at hm
  exact move_not_touch h he hm hk hs hx hl hl' hc hfix
    (Or.inl ((touchesF_of_not_alloc hna ctl).1 ht))

/-- Brief, final pass, task 4, completeness without restriction of kind: at a step `i` taken under
`Encap7`, from a state satisfying `KInvCA` and `SyncState`, while entry `e` is live before and
after the step and its controller is unchanged by the step (hypothesis 3), a step whose final
footprint contains the controller is a protocol step on `e`, hence the event `ctlIdx e lbls i` of
the controller graph. By the final restriction, the step is a protocol step of `e`, a move
admitted by C22 item 3 (excluded by `moveF_not_touch`), or ends the entry. `KInvCA`, `SyncState`
and hypothesis 3 are used only for the moves. -/
theorem completeness7 {k : K} {L : MutexLayout} {σ : Nat → SC × SyncReg × ArenaReg}
    {lbls : List Label} {i : Nat} (hi : i < lbls.length) (hst : LStep k L lbls[i] (σ i) (σ (i + 1)))
    (he : Encap7 k L (σ i) lbls[i] (σ (i + 1))) (hk : KInvCA (σ i).1)
    (hs : SyncState L (σ i).1 (σ i).2.1) {e : Nat} {x : SyncEntry}
    (hx : (σ i).2.1[e]? = some x) (hl : x.Live (σ i).1) (hl' : x.Live (σ (i + 1)).1)
    {ctl : Nat} (hc : ControlOf L (σ i).1 x = some ctl)
    (hfix : ControlOf L (σ (i + 1)).1 x = some ctl) (ht : TouchesF L (σ i) lbls[i] ctl)
    (o : Ords) :
    ∃ c op, ctlOp e lbls[i] = some (c, op) ∧
      (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  rcases he.2.apply hx hl hc ht with hp | hm | hd
  · cases hop : ctlOp e lbls[i] with
    | none => exact absurd hop hp
    | some p => exact ⟨p.1, p.2, rfl, ctlGraph_ev o e hi hop⟩
  · exact absurd ht (moveF_not_touch hst he.1 hm hk hs (List.mem_of_getElem? hx) hl hl' hc hfix)
  · exact absurd hl' hd

/-- Brief, final pass, task 4, completeness without restriction of kind on a `Run7` from the
initial state of Spec 1 §47, under `DDSound` (Spec 1 §80) and hypothesis 3 (`CtlFixed`): a step
whose final footprint contains the controller of an entry live before and after it is an event of
the controller graph. -/
theorem completeness7_run {k : K} {L : MutexLayout} {statics : Statics}
    {σ : Nat → SC × SyncReg × ArenaReg} {lbls : List Label} (hdd : DDSound k)
    (hstat : StaticsOK statics) (h0 : σ 0 = (SC.ofS3 (S3.init statics), [], []))
    (hr : Run7 k L σ lbls) {e : Nat} (h3 : CtlFixed σ L lbls e) {i : Nat} (hi : i < lbls.length)
    {x : SyncEntry} (hx : (σ i).2.1[e]? = some x) (hl : x.Live (σ i).1)
    (hl' : x.Live (σ (i + 1)).1) {ctl : Nat} (hc : ControlOf L (σ i).1 x = some ctl)
    (ht : TouchesF L (σ i) lbls[i] ctl) (o : Ords) :
    ∃ c op, ctlOp e lbls[i] = some (c, op) ∧
      (ctlGraph o e lbls).ev? (ctlIdx e lbls i) = some ⟨c, op.kind o⟩ := by
  have htr := run5R_prefix (run7_run5R hr) (Nat.le_of_lt hi)
  rw [h0] at htr
  obtain ⟨hk₀, hs₀⟩ := init_inv (k := k) hdd hstat L
  obtain ⟨hk, hs, -, -⟩ := trace_inv hdd htr hk₀ hs₀
  have hst := (hr i hi).2
  obtain ⟨y, hy, hyg⟩ := entry_kept hst hx
  obtain ⟨ctl₀, hctl⟩ := h3
  have h1 := hctl i (Nat.le_of_lt hi) (by rw [hx]; rfl)
  have h2 := hctl (i + 1) hi (by rw [hy]; rfl)
  simp only [ctlAt, hx, hy, Option.bind_some] at h1 h2
  rw [hc] at h1
  cases h1
  rw [controlOf_guarded_eq hyg] at h2
  exact completeness7 hi hst (hr i hi).1 hk hs hx hl hl' hc h2 ht o

end Ern.Concurrency.MutexReal
