import Ern.Concurrency.Realize
import Ern.MemoryModel.RefinementArena

/-!
# Sequential conservativity of the arena operations (WC4 C24)

On single-context states (`SC.Single`) whose frame structure satisfies `FramesC`, the arena
operations executed by the context coincide with the derived operations of
`Ern.MemoryModel.Arena` (`specs/ERN_Memory_Model_Specification_v0.1.md` §76–§78, Part XIV) on the
projection `SC.toS3` with the same arena registry, outcome by outcome (extension of theorem 1):

* `newArena` with `Arena.NewArenaStep`, the synchronization registry being the other registry
  of live administrations consulted by the guard (Spec 1 §56, §76.4) (`conservative_newArena`);
* `issue` with `Arena.IssueD` (`conservative_issue`);
* `reset` with `Arena.ResetD` (`conservative_reset`);

and their realizations are those of `Ern.MemoryModel.RefinementArena.lopsOf` on the projection
(extension of R5, `r5_arena`).
-/

namespace Ern.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement

/-- Projection of a kernel state and an arena registry to the library state of
`Ern.MemoryModel.Arena` (Spec 1 §46; WC4 C24). -/
def projL (p : SC × ArenaReg) : Arena.LState := ⟨p.1.toS3, p.2⟩

section Single

variable {k : K} {s : SC}

/-- On a single-context state, the preconditions of `newArena` executed by the context are those
of `Arena.NewArenaPre` on the projection, the other registry of live administrations being the
synchronization registry (Spec 1 §56, §76; WC4 C24). -/
theorem newArenaPreC_single (hs : s.Single) (hfr : FramesC s) (reg : SyncReg) (ar : ArenaReg)
    (st i : Nat) :
    NewArenaPreC s reg ar 0 st i ↔ Arena.NewArenaPre s.toS3 ar [liveGuardeds s reg] st i := by
  have hd := single_decreasing hs hfr
  have hv := single_view hs
  have hf := single_flat hs
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩
    rw [hv] at h1 h2 h4
    rw [hf] at h6 h7 h8 h9 h10 h13 h14
    exact ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, (single_anchorOrderC hs hd).1 h11,
      (single_anchorOrderHeldC hs hd).1 h12, h13⟩, h14⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩, h14⟩
    refine ⟨by rw [hv]; exact h1, by rw [hv]; exact h2, h3, by rw [hv]; exact h4, h5,
      by rw [hf]; exact h6, by rw [hf]; exact h7, by rw [hf]; exact h8, by rw [hf]; exact h9,
      by rw [hf]; exact h10, (single_anchorOrderC hs hd).2 h11,
      (single_anchorOrderHeldC hs hd).2 h12, by rw [hf]; exact h13, by rw [hf]; exact h14⟩

/-- Theorem 1 for `newArena` (WC4 C24; Spec 1 §76, §58): on a single-context state with the frame
structure `FramesC`, `newArena` executed by the context has exactly the outcomes of
`Arena.NewArenaStep` on the projection, the synchronization registry being the other registry of
live administrations. -/
theorem conservative_newArena (hs : s.Single) (hfr : FramesC s) (reg : SyncReg) (ar : ArenaReg)
    (st i : Nat) :
    (∀ o, NewArenaStepC s reg ar 0 st i o →
      Arena.NewArenaStep [liveGuardeds s reg] st i ⟨s.toS3, ar⟩ (omap projL o)) ∧
    (∀ o₃, Arena.NewArenaStep [liveGuardeds s reg] st i ⟨s.toS3, ar⟩ o₃ →
      ∃ o, NewArenaStepC s reg ar 0 st i o ∧ omap projL o = o₃) := by
  have hp := newArenaPreC_single hs hfr reg ar st i
  refine ⟨fun o ⟨_, h⟩ => ?_, fun o₃ h => ?_⟩
  · cases h with
    | ok hpre => exact Guarded.ok (hp.1 hpre)
    | reject hn => exact Guarded.reject fun h => hn (hp.2 h)
  · cases h with
    | ok hpre => exact ⟨_, ⟨single_live hs, .ok (hp.2 hpre)⟩, rfl⟩
    | reject hn => exact ⟨_, ⟨single_live hs, .reject fun h => hn (hp.1 h)⟩, rfl⟩

/-- Writing back kernel components with the same frame counter keeps `FramesC` (WC4 C3, C20). -/
theorem framesC_set {t : S3} (hn : t.nF = s.nF) (hfr : FramesC s) : FramesC (s.set t) :=
  ⟨hfr.initial, hfr.nonempty, hfr.nodup,
    fun f hf => by show f < t.nF; rw [hn]; exact hfr.bound f hf, hfr.rooted, hfr.parent⟩

/-- An `ok` `split` of the context of a single-context state writes back the `split` of its view
(Spec 1 §61 effect), and keeps a single-context state with the frame structure `FramesC`. -/
theorem split_single {src : Nat} {rs : List (List Nat)} {s₁ : SC} (hs : s.Single)
    (h : opStepC k (.split src rs) 0 s (.ok s₁)) :
    s₁ = s.set (splitEff (s.view 0) src rs) ∧ s₁.Single := by
  obtain ⟨t, hR, rfl⟩ := SyncPreserveAux.viewStep_ok h
  have hR' : SplitStep k src rs (s.view 0) (.ok t) := hR
  obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hR'
  exact ⟨rfl, hs⟩

/-- Theorem 1 for `issue` (WC4 C24; Spec 1 §77, §58, Part XIV): on a single-context state with
the frame structure `FramesC`, `issue` executed by the context has exactly the outcomes of the
derived operation `Arena.IssueD` on the projection, outcome by outcome, `fail` included. -/
theorem conservative_issue (hs : s.Single) (hfr : FramesC s) (ar : ArenaReg) (i : Nat)
    (region : List Nat) (dst : Nat) :
    (∀ o, IssueStepC k s ar 0 i region dst o →
      Arena.IssueD k i region dst ⟨s.toS3, ar⟩ (omap projL o)) ∧
    (∀ o₃, Arena.IssueD k i region dst ⟨s.toS3, ar⟩ o₃ →
      ∃ o, IssueStepC k s ar 0 i region dst o ∧ omap projL o = o₃) := by
  have hv := single_view hs
  have hst_iff : ∀ E, Arena.IssueStatic (s.view 0) E region dst ↔
      Arena.IssueStatic s.toS3 E region dst := fun E => by rw [hv]
  have hlive := single_live hs
  refine ⟨fun o h => ?_, fun o₃ h => ?_⟩
  · cases h with
    | noEntry _ hE => exact .noEntry hE
    | static _ hE hn => exact .static hE fun h => hn ((hst_iff _).2 h)
    | fail _ hE hst hav => exact .fail hE ((hst_iff _).1 hst) hav
    | split hE hst hav hsp =>
      exact .split hE ((hst_iff _).1 hst) hav ((conservative_op hs hfr _).1 _ hsp)
    | @store E s₁ hE hst hav hsp hsto =>
      have h1 := (conservative_op hs hfr _).1 _ hsp
      obtain ⟨rfl, hs₁⟩ := split_single hs hsp
      exact .store hE ((hst_iff _).1 hst) hav h1
        ((conservative_op hs₁ (framesC_set rfl hfr) _).1 _ hsto)
    | @ok E s₁ s₂ hE hst hav hsp hsto =>
      have h1 := (conservative_op hs hfr _).1 _ hsp
      obtain ⟨rfl, hs₁⟩ := split_single hs hsp
      exact .ok hE ((hst_iff _).1 hst) hav h1
        ((conservative_op hs₁ (framesC_set rfl hfr) _).1 _ hsto)
  · cases h with
    | noEntry hE => exact ⟨_, .noEntry hlive hE, rfl⟩
    | static hE hn => exact ⟨_, .static hlive hE fun h => hn ((hst_iff _).1 h), rfl⟩
    | fail hE hst hav => exact ⟨_, .fail hlive hE ((hst_iff _).2 hst) hav, rfl⟩
    | @split E hE hst hav hsp =>
      obtain ⟨o, ho, he⟩ := (conservative_op hs hfr (.split E.internal [region])).2 _ hsp
      cases o with
      | reject => exact ⟨_, .split hE ((hst_iff _).2 hst) hav ho, rfl⟩
      | ok _ => cases he
      | fail => cases he
    | @store E t₁ hE hst hav hsp hsto =>
      obtain ⟨o, ho, he⟩ := (conservative_op hs hfr (.split E.internal [region])).2 _ hsp
      cases o with
      | ok s₁ =>
        cases he
        obtain ⟨rfl, hs₁⟩ := split_single hs ho
        obtain ⟨o', ho', he'⟩ :=
          (conservative_op hs₁ (framesC_set rfl hfr) (.store s.A.length dst)).2 _ hsto
        cases o' with
        | reject => exact ⟨_, .store hE ((hst_iff _).2 hst) hav ho ho', rfl⟩
        | ok _ => cases he'
        | fail => cases he'
      | reject => cases he
      | fail => cases he
    | @ok E t₁ t₂ hE hst hav hsp hsto =>
      obtain ⟨o, ho, he⟩ := (conservative_op hs hfr (.split E.internal [region])).2 _ hsp
      cases o with
      | ok s₁ =>
        cases he
        obtain ⟨rfl, hs₁⟩ := split_single hs ho
        obtain ⟨o', ho', he'⟩ :=
          (conservative_op hs₁ (framesC_set rfl hfr) (.store s.A.length dst)).2 _ hsto
        cases o' with
        | ok s₂ =>
          cases he'
          exact ⟨_, .ok hE ((hst_iff _).2 hst) hav ho ho', rfl⟩
        | reject => cases he'
        | fail => cases he'
      | reject => cases he
      | fail => cases he

/-- An `ok` outcome of `Arena.ResetD` keeps the stack (Spec 1 §60, §62 effects). -/
theorem resetD_F {i : Nat} {L L' : Arena.LState} (h : Arena.ResetD i L (.ok L')) :
    L'.kern.F = L.kern.F := by
  cases h with
  | ok _ hd hrl _ =>
    obtain ⟨-, rfl⟩ := Guarded.ok_iff.1 hd
    obtain ⟨hp, rfl⟩ := Guarded.ok_iff.1 hrl
    obtain ⟨x, hx, -⟩ := hp.active
    rw [releaseEff_eq hx]; rfl

/-- Theorem 1 for `reset` (WC4 C24; Spec 1 §78, §58, Part XIV): on a single-context state,
`reset` executed by the context has exactly the outcomes of the derived operation `Arena.ResetD`
on the projection, outcome by outcome. -/
theorem conservative_reset (hs : s.Single) (ar : ArenaReg) (i : Nat) :
    (∀ o, ResetStepC s ar 0 i o → Arena.ResetD i ⟨s.toS3, ar⟩ (omap projL o)) ∧
    (∀ o₃, Arena.ResetD i ⟨s.toS3, ar⟩ o₃ → ∃ o, ResetStepC s ar 0 i o ∧ omap projL o = o₃) := by
  have hv := single_view hs
  have back : ∀ o₃, Arena.ResetD i ⟨s.toS3, ar⟩ o₃ →
      omap projL (omap (fun L' : Arena.LState => (s.set L'.kern, L'.arenas)) o₃) = o₃ := by
    intro o₃ h
    cases o₃ with
    | ok L' =>
      have hF := resetD_F h
      show Outcome3.ok (⟨(s.set L'.kern).toS3, L'.arenas⟩ : Arena.LState) = .ok L'
      rw [toS3_set hF]
    | reject => rfl
    | fail => rfl
  refine ⟨fun o ⟨_, o₃, h, ho⟩ => ?_, fun o₃ h => ⟨_, ⟨single_live hs, o₃, ?_, rfl⟩, back o₃ h⟩⟩
  · have h' : Arena.ResetD i ⟨s.toS3, ar⟩ o₃ := by rw [← hv]; exact h
    rw [ho, back o₃ h']; exact h'
  · rw [hv]; exact h

end Single

/-- R5 for the arena operations (WC4 C24; Spec 1 §82.7): on a single-context state, the
realization of `newArena`, `issue` and `reset` executed by the context is the realization
`RefinementArena.lopsOf` of the corresponding library operation on the projection. -/
theorem r5_arena {Ty : Type} (π : Refinement.Params Ty) (w : Nat → Nat → UInt8 × Option Nat)
    {s : SC} (hs : s.Single) (ar : ArenaReg) (m : Machine.State) (others : List (List Nat))
    (st i dst : Nat) (region : List Nat) :
    realize π w (.newArena 0 st i) s ar m =
        RefinementArena.lopsOf π (.newArena others st i) ⟨s.toS3, ar⟩ m ∧
      realize π w (.issue 0 i region dst) s ar m =
        RefinementArena.lopsOf π (.issue i region dst) ⟨s.toS3, ar⟩ m ∧
      realize π w (.reset 0 i) s ar m = RefinementArena.lopsOf π (.reset i) ⟨s.toS3, ar⟩ m := by
  have hv := single_view hs
  refine ⟨rfl, ?_, ?_⟩
  · simp only [realize, RefinementArena.lopsOf, RefinementArena.kexp]
    cases ar[i]? with
    | none => rfl
    | some E =>
      dsimp only
      rw [SC.view_set (s := s) (c := 0) (t := splitEff (s.view 0) E.internal [region]) rfl, hv]
      simp [RefinementArena.ktrace, kopOf]
      rfl
  · simp only [realize, RefinementArena.lopsOf, RefinementArena.kexp]
    cases ar[i]? with
    | none => rfl
    | some E =>
      dsimp only
      rw [SC.view_set (s := s) (c := 0)
        (t := deriveEff (s.view 0) E.internal (footprint s.P E.storage) .modify) rfl, hv]
      simp [RefinementArena.ktrace, kopOf, opsOf]

end Ern.Concurrency
