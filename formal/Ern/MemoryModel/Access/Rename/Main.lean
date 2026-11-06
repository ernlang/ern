import Ern.MemoryModel.Access.Rename.OpsSmall
import Ern.MemoryModel.Access.Rename.OpsTransfer
import Ern.MemoryModel.Access.Rename.OpsFrames
import Ern.MemoryModel.Access.Rename.OpsEndFree
import Ern.MemoryModel.Access.Rename.Invariants
import Ern.MemoryModel.Access.Rename.Init

/-!
# Renaming of identities: the kernel bisimulation

Assembly of the renaming bisimulation of the access kernel for
`specs/ERN_Memory_Model_Specification_v0.1.md` §49, last paragraph: per operation O1–O16
(§58, §60–§75), per run (§57, §58), on reachable states (§57) from the initial states of two
`StaticsOK` numberings of one declaration (§47; §63.2), and the transfer of `KInv`, `I5` (§57)
and `DDSound` (§80): `StaticsOK` (b), under the interface obligation `KExt` on `Satisfiable` (§71,
§42). Any two numberings given by `StaticsOK` (a) (`StaticsConf.exists_renumber`) are related
(`renumber_renumbered`).
-/

namespace Ern.MemoryModel.Access.Rename

variable {π α : Ren} {s s' t t' : S3} {k : K}

/-! ## One operation (§58, §60–§75) -/

/-- Every operation O1–O16 and its renamed arguments have corresponding outcomes on related
states (§58, §60–§75; §49, last paragraph). -/
theorem op_corr (hk : KExt k) (hS : Sim π α s s') (op : KernelOp) :
    StepCorr π α (op.Step k s) ((op.ren π α).Step (k.rename π α) s') := by
  cases op with
  | derive src region m => exact derive_corr hS src region m
  | split src rs => exact split_corr hS src rs
  | release a => exact release_corr hS a
  | transfer src dst => exact transfer_corr hS src dst
  | depend q x => exact depend_corr hS q x
  | enter ps ls => exact enter_corr hS ps ls
  | exit => exact exit_corr hS
  | read a ls => exact read_corr hS a ls
  | write a ls => exact write_corr hS a ls
  | writeShared a ls => exact writeShared_corr hS a ls
  | pin p => exact pin_corr hS p
  | unpin o => exact unpin_corr hS o
  | endUse p => exact endUse_corr hS
  | free p auth => exact free_corr hS
  | alloc pr ow ls => exact alloc_corr hk hS
  | store a p => exact store_corr hS a p

/-- An `ok` step keeps parent and origin links downward (§49.2, §49.5; §49, last paragraph). -/
theorem op_down {op : KernelOp} (hd : Down s) (hop : op.Step k s (.ok t)) : Down t := by
  cases op with
  | derive => exact derive_down hd hop
  | split => exact split_down hd hop
  | release => exact release_down hd hop
  | transfer => exact transfer_down hd hop
  | depend => exact depend_down hd hop
  | enter => exact enter_down hd hop
  | exit => exact exit_down hd hop
  | read => exact read_down hd hop
  | write => exact write_down hd hop
  | writeShared => exact writeShared_down hd hop
  | pin => exact pin_down hd hop
  | unpin => exact unpin_down hd hop
  | endUse => exact endUse_down hd hop
  | free => exact free_down hd hop
  | alloc => exact alloc_down hd hop
  | store => exact store_down hd hop

/-- An `ok` step keeps the field order of the parts of every place under `π` (§63.2; §49, last
paragraph). -/
theorem op_sib {op : KernelOp} (hP : PRel π s.P s'.P) (hs : SibMono π s.P)
    (hop : op.Step k s (.ok t)) : SibMono π t.P := by
  cases op with
  | derive => exact derive_sib hs hop
  | split => exact split_sib hs hop
  | release => exact release_sib hs hop
  | transfer => exact transfer_sib hs hop
  | depend => exact depend_sib hs hop
  | enter => exact enter_sib hP hs hop
  | exit => exact exit_sib hP hs hop
  | read => exact read_sib hs hop
  | write => exact write_sib hs hop
  | writeShared => exact writeShared_sib hs hop
  | pin => exact pin_sib hs hop
  | unpin => exact unpin_sib hs hop
  | endUse => exact endUse_sib hP hs hop
  | free => exact free_sib hP hs hop
  | alloc => exact alloc_sib hP hs hop
  | store => exact store_sib hs hop

/-- An outcome related to an `ok` outcome is `ok` with a related state (§58). -/
private theorem outRel_ok_eq {o : Outcome3 S3} (h : OutRel π α (.ok t) o) :
    ∃ t', o = .ok t' ∧ SRel π α t t' := by
  cases o with
  | ok t' => exact ⟨t', rfl, h⟩
  | reject => exact h.elim
  | fail => exact h.elim

/-- An `ok` step has a corresponding `ok` step of the renamed operation under the renamed
contract, and the simulation invariant holds after both (§57, §58; §49, last paragraph). -/
theorem Sim.step (hk : KExt k) (hS : Sim π α s s') {op : KernelOp} (hop : op.Step k s (.ok t)) :
    ∃ t', (op.ren π α).Step (k.rename π α) s' (.ok t') ∧ Sim π α t t' := by
  obtain ⟨o', ho', hr⟩ := (op_corr hk hS op).1 _ hop
  obtain ⟨t', rfl, hr⟩ := outRel_ok_eq hr
  exact ⟨t', ho', hr, op_down hS.down hop, op_down hS.down' ho', op_sib hS.rel.P hS.sib hop⟩

/-- An `ok` step of the renamed operation under the renamed contract has a corresponding `ok`
step, and the simulation invariant holds after both (§57, §58; §49, last paragraph). -/
theorem Sim.step_back (hk : KExt k) (hS : Sim π α s s') {op : KernelOp}
    (hop : (op.ren π α).Step (k.rename π α) s' (.ok t')) :
    ∃ t, op.Step k s (.ok t) ∧ Sim π α t t' := by
  obtain ⟨o, ho, hr⟩ := (op_corr hk hS op).2 _ hop
  cases o with
  | ok t => exact ⟨t, ho, hr, op_down hS.down ho, op_down hS.down' hop, op_sib hS.rel.P hS.sib ho⟩
  | reject => exact hr.elim
  | fail => exact hr.elim

/-! ## Runs (§57, §58) -/

/-- A run (§57, §58): the verdicts of a list of operations in order; `ok` continues from its
state, `fail` from the unchanged state (§58), and `reject` from the unchanged state too. The
continuation after `reject` is a device of the bisimulation statement, not a rule of §58 (which
gives `reject` no successor state); it only strengthens the statement, and `Reachable` (§57) does
not depend on it. -/
inductive Run (k : K) : S3 → List KernelOp → List (Outcome3 Unit) → S3 → Prop
  | nil {s : S3} : Run k s [] [] s
  | ok {s t u : S3} {op : KernelOp} {ops : List KernelOp} {vs : List (Outcome3 Unit)} :
      op.Step k s (.ok t) → Run k t ops vs u → Run k s (op :: ops) (.ok () :: vs) u
  | reject {s u : S3} {op : KernelOp} {ops : List KernelOp} {vs : List (Outcome3 Unit)} :
      op.Step k s .reject → Run k s ops vs u → Run k s (op :: ops) (.reject :: vs) u
  | fail {s u : S3} {op : KernelOp} {ops : List KernelOp} {vs : List (Outcome3 Unit)} :
      op.Step k s .fail → Run k s ops vs u → Run k s (op :: ops) (.fail :: vs) u

/-- Every run from a state has a run of the renamed operations under the renamed contract from a
related state, with the same verdicts, ending in related states (§57, §58; §49, last
paragraph). -/
theorem Sim.run (hk : KExt k) {ops : List KernelOp} {vs : List (Outcome3 Unit)} {u : S3}
    (hS : Sim π α s s') (hr : Run k s ops vs u) :
    ∃ u', Run (k.rename π α) s' (ops.map (KernelOp.ren π α)) vs u' ∧ Sim π α u u' := by
  induction hr generalizing s' with
  | nil => exact ⟨s', .nil, hS⟩
  | ok hop _ ih =>
    obtain ⟨t', ho', hS'⟩ := hS.step hk hop
    obtain ⟨u', hr', hu⟩ := ih hS'
    exact ⟨u', .ok ho' hr', hu⟩
  | @reject s₀ u₀ op _ _ hop _ ih =>
    obtain ⟨o', ho', hr⟩ := (op_corr hk hS op).1 _ hop
    obtain ⟨u', hr', hu⟩ := ih hS
    cases o' with
    | reject => exact ⟨u', .reject ho' hr', hu⟩
    | ok _ => exact hr.elim
    | fail => exact hr.elim
  | @fail s₀ u₀ op _ _ hop _ ih =>
    obtain ⟨o', ho', hr⟩ := (op_corr hk hS op).1 _ hop
    obtain ⟨u', hr', hu⟩ := ih hS
    cases o' with
    | fail => exact ⟨u', .fail ho' hr', hu⟩
    | ok _ => exact hr.elim
    | reject => exact hr.elim

/-- Every run of renamed operations under the renamed contract from a related state has a run of
the operations from the state, with the same verdicts, ending in related states (§57, §58; §49,
last paragraph). Every list of operations is such a renaming (`run_back_any`). -/
theorem Sim.run_back (hk : KExt k) {ops : List KernelOp} {vs : List (Outcome3 Unit)} {u' : S3}
    (hS : Sim π α s s') (hr : Run (k.rename π α) s' (ops.map (KernelOp.ren π α)) vs u') :
    ∃ u, Run k s ops vs u ∧ Sim π α u u' := by
  induction ops generalizing s s' vs with
  | nil => cases hr; exact ⟨s, .nil, hS⟩
  | cons op ops ih =>
    cases hr with
    | ok hop hr =>
      obtain ⟨t, ho, hS'⟩ := hS.step_back hk hop
      obtain ⟨u, hr, hu⟩ := ih hS' hr
      exact ⟨u, .ok ho hr, hu⟩
    | reject hop hr =>
      obtain ⟨o, ho, ho'⟩ := (op_corr hk hS op).2 _ hop
      obtain ⟨u, hr, hu⟩ := ih hS hr
      cases o with
      | reject => exact ⟨u, .reject ho hr, hu⟩
      | ok _ => exact ho'.elim
      | fail => exact ho'.elim
    | fail hop hr =>
      obtain ⟨o, ho, ho'⟩ := (op_corr hk hS op).2 _ hop
      obtain ⟨u, hr, hu⟩ := ih hS hr
      cases o with
      | fail => exact ⟨u, .fail ho hr, hu⟩
      | ok _ => exact ho'.elim
      | reject => exact ho'.elim

/-- `Sim.run_back` for any list of operations of the renamed side, the renaming of its inverse
renaming (§57, §58; §49, last paragraph). -/
theorem Sim.run_back_any (hk : KExt k) {ops' : List KernelOp} {vs : List (Outcome3 Unit)}
    {u' : S3} (hS : Sim π α s s') (hr : Run (k.rename π α) s' ops' vs u') :
    ∃ u, Run k s (ops'.map (KernelOp.ren π.symm α.symm)) vs u ∧ Sim π α u u' := by
  refine hS.run_back hk ?_
  rwa [List.map_map, Function.comp_def, funext (KernelOp.ren_symm_ren π α), List.map_id']

/-! ## Two numberings of one declaration (§47, §57; §49, last paragraph; §63.2) -/

variable {statics : Statics} {σ : List Nat}

/-- Every run from the initial state of `statics` has a run of the renamed operations under the
renamed contract from the initial state of its renumbering, with the same verdicts, ending in
related states (§47, §57, §58; §49, last paragraph). -/
theorem Renumbered.run (hk : KExt k) (h : Renumbered statics σ) {ops : List KernelOp}
    {vs : List (Outcome3 Unit)} {u : S3} (hr : Run k (S3.init statics) ops vs u) :
    ∃ u', Run (k.rename h.π h.α) (S3.init (renumber σ statics))
      (ops.map (KernelOp.ren h.π h.α)) vs u' ∧ Sim h.π h.α u u' :=
  h.initSim.run hk hr

/-- Every run of renamed operations under the renamed contract from the initial state of the
renumbering has a run from the initial state of `statics`, with the same verdicts, ending in
related states (§47, §57, §58; §49, last paragraph). -/
theorem Renumbered.run_back (hk : KExt k) (h : Renumbered statics σ) {ops : List KernelOp}
    {vs : List (Outcome3 Unit)} {u' : S3}
    (hr : Run (k.rename h.π h.α) (S3.init (renumber σ statics))
      (ops.map (KernelOp.ren h.π h.α)) vs u') :
    ∃ u, Run k (S3.init statics) ops vs u ∧ Sim h.π h.α u u' :=
  h.initSim.run_back hk hr

/-- Every state reachable from the initial state of `statics` has a related state reachable under
the renamed contract from the initial state of the renumbering (§47, §57; §49, last
paragraph). -/
theorem Renumbered.reachable (hk : KExt k) (h : Renumbered statics σ)
    (hs : Reachable k statics s) :
    ∃ s', Reachable (k.rename h.π h.α) (renumber σ statics) s' ∧ Sim h.π h.α s s' := by
  induction hs with
  | init => exact ⟨_, .init, h.initSim⟩
  | step _ hst ih =>
    obtain ⟨s', hr', hS⟩ := ih
    obtain ⟨op, hop⟩ := kstep_iff.1 hst
    obtain ⟨t', ho', hS'⟩ := hS.step hk hop
    exact ⟨t', .step hr' (kstep_iff.2 ⟨_, ho'⟩), hS'⟩

/-- Every state reachable under the renamed contract from the initial state of the renumbering
has a related state reachable from the initial state of `statics` (§47, §57; §49, last
paragraph). -/
theorem Renumbered.reachable_back (hk : KExt k) (h : Renumbered statics σ)
    (hs' : Reachable (k.rename h.π h.α) (renumber σ statics) s') :
    ∃ s, Reachable k statics s ∧ Sim h.π h.α s s' := by
  induction hs' with
  | init => exact ⟨_, .init, h.initSim⟩
  | step _ hst ih =>
    obtain ⟨s, hr, hS⟩ := ih
    obtain ⟨op', hop'⟩ := kstep_iff.1 hst
    rw [← KernelOp.ren_symm_ren h.π h.α op'] at hop'
    obtain ⟨t, ho, hS'⟩ := hS.step_back hk hop'
    exact ⟨t, .step hr (kstep_iff.2 ⟨_, ho⟩), hS'⟩

/-- The properties proved of the kernel do not change under a consistent renumbering (§57, §80;
§49, last paragraph): `DDSound` holds for the renamed contract exactly when it holds for the
contract, and `KInv` and `I5` hold on every reachable state of one numbering exactly when they
hold on every reachable state of the other. -/
theorem Renumbered.properties (hk : KExt k) (h : Renumbered statics σ) :
    (DDSound (k.rename h.π h.α) ↔ DDSound k) ∧
    ((∀ s, Reachable k statics s → KInv s ∧ I5 k s) ↔
      ∀ s', Reachable (k.rename h.π h.α) (renumber σ statics) s' →
        KInv s' ∧ I5 (k.rename h.π h.α) s') := by
  refine ⟨ddSound_rename h.π h.α k, fun hP s' hs' => ?_, fun hP s hs => ?_⟩
  · obtain ⟨s, hs, hS⟩ := h.reachable_back hk hs'
    exact ⟨hS.kinv.2 (hP s hs).1, hS.i5.2 (hP s hs).2⟩
  · obtain ⟨s', hs', hS⟩ := h.reachable hk hs
    exact ⟨hS.kinv.1 (hP s' hs').1, hS.i5.1 (hP s' hs').2⟩

/-! ## Any two numberings given by point (a) are related (§47; §49, last paragraph; §63.2) -/

/-- A static with a structural parent is declared (§40, §47). -/
private theorem lt_of_staticParent {st : Statics} {x p : Nat}
    (h : staticParent st x = some p) : x < st.length := by
  unfold staticParent at h
  cases hx : st[x]? with
  | none => rw [hx] at h; cases h
  | some _ => exact (List.getElem?_eq_some_iff.1 hx).1

/-- A permutation of the indices is duplicate-free. -/
private theorem perm_nodup {τ : List Nat} {n : Nat} (hτ : τ.Perm (List.range n)) : τ.Nodup :=
  hτ.nodup_iff.2 List.nodup_range

/-- Positions in a permutation of the indices invert its entries. -/
private theorem idxOf_getElem {τ : List Nat} {n : Nat} (hτ : τ.Perm (List.range n)) {i : Nat}
    (hi : i < τ.length) : τ.idxOf τ[i] = i :=
  (List.Nodup.getElem_inj (perm_nodup hτ)).1
    (List.getElem_idxOf (List.idxOf_lt_length_of_mem (List.getElem_mem hi)))

/-- Entry of a renumbering at a position (§49, last paragraph). -/
private theorem renumber_getElem? {τ : List Nat} {st : Statics}
    (hτ : τ.Perm (List.range st.length)) {i : Nat} (hi : i < τ.length) :
    (renumber τ st)[i]? = (st[τ[i]]?).map (mapRefs τ.idxOf) := by
  have hx : τ[i] < st.length := List.mem_range.1 (hτ.mem_iff.1 (List.getElem_mem hi))
  simp [renumber, hi, hx]

/-- Every renumbering by a permutation satisfies the entry clause of `ConsistentRenumbering`
(§49, last paragraph). -/
private theorem renumber_entry {τ : List Nat} {st : Statics}
    (hτ : τ.Perm (List.range st.length)) {x : Nat} (hx : x < st.length) :
    (renumber τ st)[τ.idxOf x]? = (st[x]?).map (mapRefs τ.idxOf) := by
  have hm := List.idxOf_lt_length_of_mem (hτ.mem_iff.2 (List.mem_range.2 hx))
  rw [renumber_getElem? hτ hm, List.getElem_idxOf hm]

/-- Structural parents in a renumbering (§40; §49, last paragraph). -/
private theorem renumber_parent {τ : List Nat} {st : Statics}
    (hτ : τ.Perm (List.range st.length)) {i : Nat} (hi : i < τ.length) :
    staticParent (renumber τ st) i = (staticParent st τ[i]).map τ.idxOf := by
  unfold staticParent
  rw [renumber_getElem? hτ hi]
  cases st[τ[i]]? <;> rfl

/-- Mapping references twice maps them by the composition (§49, last paragraph). -/
private theorem mapRefs_mapRefs (f g : Nat → Nat) (e : (Option Nat × Option Nat × Nat) × Bool) :
    mapRefs f (mapRefs g e) = mapRefs (fun x => f (g x)) e := by
  obtain ⟨⟨p, o, k⟩, b⟩ := e
  cases p <;> cases o <;> rfl

/-- Any two consistent renumberings of a conforming declaration satisfying `StaticsOK`, as given by
`StaticsOK` (a) (`StaticsConf.exists_renumber`), are related by a consistent renumbering: the second
is the renumbering of the first by `σ₂.map σ₁.idxOf`, and both are `Renumbered` (§47; §49, last
paragraph; §63.2). -/
theorem renumber_renumbered {C : Statics} (hC : StaticsConf C) {σ₁ σ₂ : List Nat}
    (hp₁ : σ₁.Perm (List.range C.length)) (hc₁ : ConsistentRenumbering σ₁ C)
    (hok₁ : StaticsOK (renumber σ₁ C)) (hp₂ : σ₂.Perm (List.range C.length))
    (hc₂ : ConsistentRenumbering σ₂ C) (hok₂ : StaticsOK (renumber σ₂ C)) :
    ∃ τ, Renumbered (renumber σ₁ C) τ ∧ renumber τ (renumber σ₁ C) = renumber σ₂ C := by
  have hl₁ : σ₁.length = C.length := by simpa using hp₁.length_eq
  have hl₂ : σ₂.length = C.length := by simpa using hp₂.length_eq
  have hlen : (renumber σ₁ C).length = C.length := by simp [renumber, hl₁]
  let τ := σ₂.map σ₁.idxOf
  have hmem : ∀ {σ : List Nat}, σ.Perm (List.range C.length) → ∀ x, x ∈ σ ↔ x < C.length :=
    fun hp x => by rw [hp.mem_iff, List.mem_range]
  have hidx : ∀ {σ : List Nat}, σ.Perm (List.range C.length) → ∀ x, x < C.length →
      σ.idxOf x < C.length := fun hp x hx => by
    have := List.idxOf_lt_length_of_mem ((hmem hp x).2 hx)
    rwa [hp.length_eq, List.length_range] at this
  have hinj : ∀ {σ : List Nat}, σ.Perm (List.range C.length) → ∀ x y, x < C.length →
      y < C.length → σ.idxOf x = σ.idxOf y → x = y := fun hp x y hx hy e => by
    rw [← List.getElem_idxOf (List.idxOf_lt_length_of_mem ((hmem hp x).2 hx)),
      ← List.getElem_idxOf (List.idxOf_lt_length_of_mem ((hmem hp y).2 hy))]
    exact getElem_congr rfl e _
  -- τ is a permutation of the indices of `renumber σ₁ C`
  have hτ : τ.Perm (List.range (renumber σ₁ C).length) := by
    rw [hlen]
    apply perm_range_of_nodup
    · unfold List.Nodup
      rw [List.pairwise_map]
      exact (perm_nodup hp₂).imp_of_mem fun {a b} ha hb hab e =>
        hab (hinj hp₁ a b ((hmem hp₂ a).1 ha) ((hmem hp₂ b).1 hb) e)
    · intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
      exact hidx hp₁ x ((hmem hp₂ x).1 hx)
    · simp [τ, hl₂]
  -- positions in τ compose the positions in σ₁ into the positions in σ₂
  have hτidx : ∀ p, τ.idxOf (σ₁.idxOf p) = σ₂.idxOf p := by
    intro p
    by_cases hp : p < C.length
    · have hi := List.idxOf_lt_length_of_mem ((hmem hp₂ p).2 hp)
      have hi' : σ₂.idxOf p < τ.length := by simpa [τ] using hi
      have : τ[σ₂.idxOf p] = σ₁.idxOf p := by
        simp only [τ, List.getElem_map, List.getElem_idxOf hi]
      rw [← this, idxOf_getElem hτ hi']
    · have hn : ∀ {σ : List Nat}, σ.Perm (List.range C.length) → σ.idxOf p = C.length :=
        fun hp' => by
          rw [List.idxOf_eq_length fun hm => hp ((hmem hp' p).1 hm), hp'.length_eq,
            List.length_range]
      rw [hn hp₁, hn hp₂, List.idxOf_eq_length]
      · simp [τ, hl₂]
      · intro hm
        obtain ⟨x, hx, e⟩ := List.mem_map.1 hm
        exact absurd (e ▸ hidx hp₁ x ((hmem hp₂ x).1 hx)) (Nat.lt_irrefl _)
  -- the renumbering of the first numbering by τ is the second numbering
  have heq : renumber τ (renumber σ₁ C) = renumber σ₂ C := by
    simp only [renumber, τ, List.map_map, Function.comp_def]
    refine List.map_congr_left fun j hj => ?_
    have hjC := (hmem hp₂ j).1 hj
    have := renumber_entry hp₁ hjC
    simp only [renumber] at this
    rw [this, List.getElem?_eq_getElem hjC, Option.map_some, Option.getD_some,
      Option.getD_some, mapRefs_mapRefs, funext hτidx]
  -- field order: siblings keep their order from the first to the second numbering
  have hfo : ∀ x y p, staticParent (renumber σ₁ C) x = some p →
      staticParent (renumber σ₁ C) y = some p → x < y → τ.idxOf x < τ.idxOf y := by
    intro x y p hx hy hxy
    have hxl : x < σ₁.length := hl₁ ▸ hlen ▸ lt_of_staticParent hx
    have hyl : y < σ₁.length := hl₁ ▸ hlen ▸ lt_of_staticParent hy
    have hx0 : σ₁[x] < C.length := (hmem hp₁ _).1 (List.getElem_mem hxl)
    have hy0 : σ₁[y] < C.length := (hmem hp₁ _).1 (List.getElem_mem hyl)
    rw [renumber_parent hp₁ hxl] at hx
    rw [renumber_parent hp₁ hyl] at hy
    obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.1 hx
    obtain ⟨b, hb, hab⟩ := Option.map_eq_some_iff.1 hy
    have hab : b = a := hinj hp₁ b a (hC.parent_lt _ _ hb) (hC.parent_lt _ _ ha) hab
    subst hab
    have ex : σ₁.idxOf σ₁[x] = x := idxOf_getElem hp₁ hxl
    have ey : σ₁.idxOf σ₁[y] = y := idxOf_getElem hp₁ hyl
    have hlt : σ₁[x] < σ₁[y] := by
      rcases Nat.lt_trichotomy σ₁[x] σ₁[y] with h | h | h
      · exact h
      · rw [← ex, ← ey, h] at hxy; exact absurd hxy (Nat.lt_irrefl _)
      · have := hc₁.field_order _ _ _ hb ha h
        rw [ex, ey] at this; omega
    have := hc₂.field_order _ _ _ ha hb hlt
    rw [← ex, ← ey, hτidx, hτidx]
    exact this
  refine ⟨τ, ⟨hτ, ⟨fun x hx => renumber_entry hτ hx, hfo⟩, hok₁, heq ▸ hok₂⟩, heq⟩

/-! ## Non-vacuity (§47, §48, §57, §58; §49, last paragraph) -/

namespace MainExamples

open Examples InitExamples

/-- `KExt` is satisfiable: `K0.Satisfiable` is constantly true (§48, §71). -/
theorem k0_ext : KExt K0 := fun _ _ _ _ _ _ => trivial

/-- A run of `n1` (§47) with an accepted `pin` and a rejected `unpin` (§74, §75) has the renamed
run with the same verdicts on the renumbering `[3, 0, 1, 2]` of `n1` (§49, last paragraph). -/
example : ∃ u', Run (K0.rename n1_renumbered.π n1_renumbered.α)
    (S3.init (renumber [3, 0, 1, 2] n1))
    ([KernelOp.pin 1, .unpin 1].map (KernelOp.ren n1_renumbered.π n1_renumbered.α))
    [.ok (), .reject] u' ∧ Sim n1_renumbered.π n1_renumbered.α (pinEff (S3.init n1) 1) u' :=
  n1_renumbered.run k0_ext
    (.ok (show PinStep 1 (S3.init n1) (.ok (pinEff (S3.init n1) 1)) from .ok (by decide))
      (.reject (show UnpinStep K0 1 (pinEff (S3.init n1) 1) .reject from .reject (by decide))
        .nil))

end MainExamples

end Ern.MemoryModel.Access.Rename
