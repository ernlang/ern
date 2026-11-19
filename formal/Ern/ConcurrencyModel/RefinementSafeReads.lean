import Ern.ConcurrencyModel.RefinementPinning

/-!
# Theorem 9, safe reads (Spec 1 §82.2, §15; R1 of the memory model)

`Refinement.r1_read` states, for a `read` of the memory model, that the raw read of each leaf finds
a live allocation whose range is initialized and returns the bytes of that range. Theorem 9a
(`refinement_step`) carries this result for every labelled step without writing it. This module
writes it, at the grain of abstract steps, for every raw read of `rawOps` of a step executed by any
context (C2):

* the memory state is the one that immediately precedes the read in the execution of `rawOps`: the
  state reached by the raw operations before it, `run m ((rawOps π w lbl st m).take i)`, not the
  state where the step starts. The reads of a `transfer` (Spec 1 §63, §82.3) and of the transfer
  phases of the by-value composite (C5.2) are covered;
* the reads of `read` (Spec 1 §66), `readShared` (C37), the failed CAS and the reads of an RMW and
  of a successful CAS (C38, C39) are covered, the preconditions of the step taking the place of
  `Read3Pre`: C37.1 and C37.2 for `readShared` and the failed CAS (`ReadSharedPre.read`); the O11
  preconditions and `rmwInit` for an RMW and a successful CAS (`WriteSharedCPre`); Spec 1 §63.1 and
  §63.3 for a transfer;
* `safe_read_direct`: every label but the by-value composite, with the hypotheses of `r1_read`
  transposed: `ReprC` at the start of the step, `WF3` of the flat state with `FramesC` (which give
  `WF3` of every view, C2, C20), the step, and the obligations of the read itself (Spec 1 §15);
* `safe_read_spawnVal`: the by-value composite. The state where a transfer phase starts is related
  to its abstract state only once the creations and the earlier phases have run: as 9a does for
  them, the statement takes the obligations of the raw operations up to the read, the placement
  and geometry of the creations, the layout of the new locals, and `KInvCA`, from which the
  invariant of each phase is carried (`KBase`, as in `vals_realized`). The preconditions of a phase
  are read in the state where it starts (C5.2, `ValTransfersPre`), as in 9e;
* `safe_read`: every label; `reached_safe_read`: on the states of a translated run, without
  invariant hypothesis.

What these statements say is about the bytes the raw read returns. They say nothing of the observed
value carried by the label of a `readShared`, a CAS or an RMW: no tranche links it to the bytes read
so far, and the link depends on C31 to C34. For an RMW over more than one leaf, admitted under a
composite contract (C38), the reads of every leaf of the region are an auxiliary construction of
`rawOps`, not physical events; the clauses do not say what such a step reads, and that reserve
stays open (`composite_rmw_restricts`).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access Ern.MemoryModel.Refinement
open PreservationAux TransferPreserveAux ReparentAux

section SafeReads

variable {Ty : Type} {ObR : Machine.ReadOblSpec Ty} {ObW : Machine.WriteOblSpec Ty}
  {π : Params Ty} {w : WriteRepr}

/-! ## The conclusion of R1 for one raw read -/

/-- The conclusion of R1 for the raw read `read ac t` in the memory state `s` (Spec 1 §82.2, §15):
it is the read of a leaf `l` at the type of `l`, the allocation of `l` is live, the range of `l` is
initialized, and the raw read returns the bytes of that range. -/
def SafeRead (ObR : Machine.ReadOblSpec Ty) (π : Params Ty) (s : Machine.State)
    (ac : Machine.Access) (t : Ty) : Prop :=
  ∃ l al, ac = leafAcc s π.L .read l ∧ t = π.ty l ∧ s.allocs (π.L l).alloc = some al ∧
    al.live = true ∧ al.InitRange (π.L l).off (π.L l).len ∧
    Machine.ReadStep ObR ac t s (.ok (al.bytesAt (π.L l).off (π.L l).len))

/-- R1 after raw operations that deallocate nothing (Spec 1 §82.2, §15, §13 ¶3, §16 ¶2): under
`Repr` and `WF3` of `t` and the memory state `s0`, for a usable `Init` leaf `l` of `t`, in the
memory state reached from `s0` by raw operations without deallocation, the raw read of `l` is safe.
The proof of `Refinement.r1_read`, with the liveness and the initialized bytes carried along the
raw operations (`liveWithin_run`, `dom_run`). -/
theorem leaf_safe {t : S3} {s0 : Machine.State} {ops : List (Machine.Op Ty)} {l : Nat}
    (hR : Repr π.L π.rtok t s0) (hw : WF3 t) (hlP : l < t.P.length) (hlf : isLeaf t.P l)
    (hu : t.Usable l) (hI : t.I l = .init) (hn : ∀ o ∈ ops, NoDealloc o)
    (hob : ObR.dec (run s0 ops) (leafAcc (run s0 ops) π.L .read l) (π.ty l) ∧
      ObR.stat (run s0 ops) (leafAcc (run s0 ops) π.L .read l) (π.ty l)) :
    SafeRead ObR π (run s0 ops) (leafAcc (run s0 ops) π.L .read l) (π.ty l) := by
  have hwf := hR.adm.wf
  obtain ⟨al, hal, hlive, hsz⟩ :=
    RefinementArena.liveWithin_run hwf hn (hR.leaf_live hw hlP hlf hu)
  obtain ⟨al', hal', hi⟩ := (hR.init l hlP hlf hI).dom_init (dom_run ops s0 hwf)
  rw [hal] at hal'; cases hal'
  refine ⟨l, al, rfl, rfl, hal, hlive, hi, ?_⟩
  have hc := canRead_leaf hal hlive hsz hi
  have hst := Machine.ReadStep.ok (ObR := ObR) (t := π.ty l) hal ⟨hc, hob.1, hob.2⟩
  rw [leafAcc_of hal] at hst ⊢
  simpa only [Nat.add_sub_cancel_left] using hst

/-! ## Positions of the raw reads -/

/-- The obligation of the raw operation at index `i`, in the state reached by the raw operations
before it, from the obligations of the raw operations up to it (Spec 1 §20.3). -/
theorem obl_take_at {s : Machine.State} {ops : List (Machine.Op Ty)} {i : Nat}
    {o : Machine.Op Ty} (ho : ops[i]? = some o) (h : OblAlong ObR ObW s (ops.take (i + 1))) :
    Obl ObR ObW (run s (ops.take i)) o := by
  rw [List.take_add_one, ho] at h
  exact ((along_append (p := Obl ObR ObW)).1 h).2.1

/-- The prefix of a concatenation that extends past its first part. -/
theorem take_length_add {α : Type} (l₁ l₂ : List α) (j : Nat) :
    (l₁ ++ l₂).take (l₁.length + j) = l₁ ++ l₂.take j := by
  rw [List.take_append, List.take_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- The raw writes contain no read (Spec 1 §16, §82.2). -/
theorem writeOps_noRead {s2 : Machine.State} {L : Layout} {ty : Nat → Ty}
    {wr : Nat → Nat → UInt8 × Option Nat} {ls : List Nat} {ac : Machine.Access} {t : Ty} :
    Machine.Op.read ac t ∉ writeOps s2 L ty wr ls := fun h => by
  obtain ⟨_, -, e⟩ := List.mem_map.1 h
  cases e

/-- The deallocations contain no read (Spec 1 §17, §82.5). -/
theorem deallocOps_noRead {L : Layout} {rtok : Nat → Nat} {rs : List Nat}
    {ac : Machine.Access} {t : Ty} : Machine.Op.read ac t ∉ deallocOps (Ty := Ty) L rtok rs :=
  fun h => by
    obtain ⟨_, -, e⟩ := List.mem_map.1 h
    cases e

/-- A raw read among the reads of the leaves `ls` followed by raw operations without read: it is
the read of a leaf of `ls`, in the memory state where the reads start, which they leave unchanged
(Spec 1 §66, §82.2, §20.2 ¶1). -/
theorem readOps_read_at {s : Machine.State} {L : Layout} {ty : Nat → Ty} {ls : List Nat}
    {rest : List (Machine.Op Ty)} (hrest : ∀ ac t, Machine.Op.read ac t ∉ rest) {i : Nat}
    {ac : Machine.Access} {t : Ty} (hi : (readOps s L ty ls ++ rest)[i]? = some (.read ac t)) :
    ∃ l ∈ ls, ac = leafAcc s L .read l ∧ t = ty l ∧
      run s ((readOps s L ty ls ++ rest).take i) = s := by
  have hlen : (readOps s L ty ls).length = ls.length := List.length_map ..
  by_cases hil : i < ls.length
  · rw [List.getElem?_append_left (by rw [hlen]; exact hil)] at hi
    simp only [readOps, List.getElem?_map] at hi
    cases hli : ls[i]? with
    | none => rw [hli] at hi; cases hi
    | some l =>
      rw [hli] at hi
      simp only [Option.map_some, Option.some.injEq, Machine.Op.read.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      refine ⟨l, List.mem_iff_getElem?.2 ⟨i, hli⟩, rfl, rfl, ?_⟩
      rw [List.take_append_of_le_length (by rw [hlen]; exact Nat.le_of_lt hil), readOps,
        ← List.map_take]
      exact run_readOps s L ty _ s
  · rw [List.getElem?_append_right (by rw [hlen]; exact Nat.le_of_not_lt hil)] at hi
    exact absurd (List.mem_iff_getElem?.2 ⟨_, hi⟩) (hrest ac t)

/-- A raw read among the copies of a transfer (Spec 1 §63 effect, §82.3) is the read of the first
leaf of one of the pairs, in the memory state reached by the copies before it. -/
theorem copyOps_read_at (L : Layout) (ty : Nat → Ty) :
    ∀ (s2 : Machine.State) (ps : List (Nat × Nat)) (i : Nat) {ac : Machine.Access} {t : Ty},
      (copyOps L ty s2 ps)[i]? = some (.read ac t) →
      ∃ q ∈ ps, ac = leafAcc (run s2 ((copyOps L ty s2 ps).take i)) L .read q.1 ∧ t = ty q.1
  | _, [], _, _, _, h => by simp [copyOps] at h
  | s2, (l, l') :: ps, 0, _, _, h => by
    simp only [copyOps, List.getElem?_cons_zero, Option.some.injEq, Machine.Op.read.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨(l, l'), List.mem_cons_self .., rfl, rfl⟩
  | s2, (l, l') :: ps, 1, _, _, h => by simp [copyOps] at h
  | s2, (l, l') :: ps, j + 2, _, _, h => by
    simp only [copyOps, List.getElem?_cons_succ] at h
    obtain ⟨q, hq, rfl, rfl⟩ := copyOps_read_at L ty _ ps j h
    exact ⟨q, List.mem_cons_of_mem _ hq, rfl, rfl⟩

/-- The kernel operations whose raw operations read are `read` and `transfer` (Spec 1 §82.2,
§82.3). -/
theorem opsOf_read_cases {t : S3} {m : Machine.State} {op : KernelOp} {ac : Machine.Access}
    {ty' : Ty} (hm : Machine.Op.read ac ty' ∈ opsOf π (kopOf op w) t m) :
    (∃ a ls, op = .read a ls) ∨ (∃ src dst, op = .transfer src dst) := by
  cases op with
  | read a ls => exact .inl ⟨a, ls, rfl⟩
  | transfer src dst => exact .inr ⟨src, dst, rfl⟩
  | enter => exact (allocOps_noRead _ _ _ _ _ _ hm).elim
  | exit => exact (deallocOps_noRead hm).elim
  | write => exact (writeOps_noRead hm).elim
  | writeShared => exact (writeOps_noRead hm).elim
  | alloc => exact (allocOps_noRead _ _ _ _ _ _ hm).elim
  | store => exact (writeOps_noRead hm).elim
  | free => simp [kopOf, opsOf, freeOps] at hm
  | derive => simp [kopOf, opsOf] at hm
  | split => simp [kopOf, opsOf] at hm
  | release => simp [kopOf, opsOf] at hm
  | depend => simp [kopOf, opsOf] at hm
  | pin => simp [kopOf, opsOf] at hm
  | unpin => simp [kopOf, opsOf] at hm
  | endUse => simp [kopOf, opsOf] at hm

/-! ## Safe reads of the reads of leaves and of the copies -/

/-- The reads of the leaves `ls` under `Read3Pre` (Spec 1 §66), followed by raw operations without
read: each raw read is safe in the memory state that precedes it (`r1_read`). -/
theorem readOps_safe {t3 : S3} {m : Machine.State} {a : Nat} {ls : List Nat}
    {ops rest : List (Machine.Op Ty)} (hops : ops = readOps m π.L π.ty ls ++ rest)
    (hR : Repr π.L π.rtok t3 m) (hw : WF3 t3) (hpre : Read3Pre t3 a ls)
    (hrest : ∀ ac t, Machine.Op.read ac t ∉ rest) {i : Nat} {ac : Machine.Access} {t : Ty}
    (hi : ops[i]? = some (.read ac t))
    (hob : ObR.dec (run m (ops.take i)) ac t ∧ ObR.stat (run m (ops.take i)) ac t) :
    SafeRead ObR π (run m (ops.take i)) ac t := by
  subst hops
  obtain ⟨l, hl, rfl, rfl, hrun⟩ := readOps_read_at hrest hi
  rw [hrun] at hob ⊢
  obtain ⟨al, hal, hlive, hinit, hst⟩ := r1_read hR hw hpre hl hob
  exact ⟨l, al, rfl, rfl, hal, hlive, hinit, hst⟩

/-- The copies of a transfer from §63.1 (usable source) and §63.3 (source leaves `Init`): each raw
read is safe in the memory state reached by the copies before it (Spec 1 §63, §82.2, §82.3). -/
theorem transfer_safe {t : S3} {m : Machine.State} {src dst : Nat} (hR : Repr π.L π.rtok t m)
    (hw : WF3 t) (hsu : t.Usable src) (hsi : ∀ l ∈ footprint t.P src, t.I l = .init) {i : Nat}
    {ac : Machine.Access} {ty' : Ty}
    (hi : (transferOps π.L π.ty m t src dst)[i]? = some (.read ac ty'))
    (hob : ObR.dec (run m ((transferOps π.L π.ty m t src dst).take i)) ac ty' ∧
      ObR.stat (run m ((transferOps π.L π.ty m t src dst).take i)) ac ty') :
    SafeRead ObR π (run m ((transferOps π.L π.ty m t src dst).take i)) ac ty' := by
  obtain ⟨⟨l, l'⟩, hq, rfl, rfl⟩ := copyOps_read_at π.L π.ty m _ i hi
  obtain ⟨hl, -⟩ := mem_transferPairs.1 hq
  obtain ⟨hlP, hlf, hls⟩ := mem_footprint.1 hl
  have hu := usable_of_partOf hw (l + 1) l src (Nat.lt_succ_self l) hls hsu
  exact leaf_safe hR hw hlP hlf hu (hsi l hl)
    (fun o ho => copyOps_noDealloc _ _ _ _ o (List.mem_of_mem_take ho)) hob

/-! ## The labels other than the by-value composite -/

/-- **Theorem 9**, safe reads for every label but the by-value composite (Spec 1 §82.2, §15, §66,
§63; C2, C37–C39), at the grain of abstract steps, on the model of `Refinement.r1_read`: for a step
executed by any context, every raw read of `rawOps` (at index `i`) is the read of a leaf whose
allocation is live and whose range is initialized, and it returns the bytes of that range, in the
memory state reached by the raw operations before it.

Hypotheses, those of `r1_read` transposed: `ReprC` at the start of the step (Spec 1 §82; C2);
`FramesC` and `WF3` of the flat state (Spec 1 §49; C20), which give `WF3` of the view of the
executing context; the step, whose preconditions take the place of `Read3Pre` (Spec 1 §66 for
`read`; §63.1, §63.3 for `transfer`; C37.1, C37.2 for `readShared` and the failed CAS; the O11
preconditions and the initialized leaves of C39 for an RMW and a successful CAS); the obligations
of the read itself (Spec 1 §15). Fragment: every state satisfying these hypotheses, every executing
context, every label but `spawnVal`.

The statement is about the bytes the raw read returns. It says nothing of the observed value
carried by the label of a `readShared`, a CAS or an RMW (C31–C34). For an RMW over more than one
leaf (C38), the reads of every leaf are an auxiliary construction of `rawOps`, not physical
events. -/
theorem safe_read_direct {ks : KShared} {ML : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {m : Machine.State} (hR : ReprC π.L π.rtok st.1 m)
    (hfr : FramesC st.1) (hw : WF3 st.1.flat) (h : LStep ks ML lbl st st')
    (hsv : ∀ c ps ls vs, lbl ≠ .spawnVal c ps ls vs) {i : Nat} {ac : Machine.Access} {ty' : Ty}
    (hi : (rawOps π w lbl st m)[i]? = some (.read ac ty'))
    (hob : ObR.dec (run m ((rawOps π w lbl st m).take i)) ac ty' ∧
      ObR.stat (run m ((rawOps π w lbl st m).take i)) ac ty') :
    SafeRead ObR π (run m ((rawOps π w lbl st m).take i)) ac ty' := by
  have hm : Machine.Op.read ac ty' ∈ rawOps π w lbl st m := List.mem_iff_getElem?.2 ⟨i, hi⟩
  cases h with
  | @kernel s s' reg ar c op h =>
    have hc : s.Live c := opStepC_live h
    have hwv := SC.wf3_view hfr hw hc
    have hRv := (reprC_view hc).1 hR
    rcases opsOf_read_cases hm with ⟨a, ls, rfl⟩ | ⟨src, dst, rfl⟩
    · obtain ⟨t', hst, -⟩ := viewStep_ok h
      have hpre := (Guarded.ok_iff.1 (show Read3Step a ls (s.view c) (.ok t') from hst)).1
      exact readOps_safe (ops := readOps m π.L π.ty ls) (rest := []) (List.append_nil _).symm
        hRv hwv hpre (fun _ _ h => nomatch h) hi hob
    · obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
      exact transfer_safe hRv hwv hpre.srcUsable hpre.srcInit hi hob
  | spawn => exact (allocOps_noRead _ _ _ _ _ _ hm).elim
  | spawnVal => exact absurd rfl (hsv _ _ _ _)
  | terminate => exact (deallocOps_noRead hm).elim
  | join => simp [rawOps] at hm
  | deriveSync => simp [rawOps] at hm
  | newMutex => simp [rawOps] at hm
  | acquire => simp [rawOps] at hm
  | unlock => simp [rawOps] at hm
  | resetLock => simp [rawOps] at hm
  | @newArena s reg ar c st₀ i' st₂ h =>
    rw [(rawOps_arena_nil π w (s, reg, ar) m c st₀ i' 0).1] at hm
    exact nomatch hm
  | @issue s reg ar c i' region dst st₂ h =>
    obtain ⟨E, s₁, hE, -⟩ := issueStepC_ok h
    rw [rawOps_issue π w (st := (s, reg, ar)) hE] at hm
    exact (writeOps_noRead hm).elim
  | @reset s reg ar c i' st₂ h =>
    rw [(rawOps_arena_nil π w (s, reg, ar) m c 0 0 i').2] at hm
    exact nomatch hm
  | @readShared s reg ar c a l v order h =>
    have hp := (Guarded.ok_iff.1 h).1
    have hc : s.Live c := SC.live_of_exercisable hp.read.exercisable
    exact readOps_safe (ops := readOps m π.L π.ty [l]) (rest := []) (List.append_nil _).symm
      ((reprC_view hc).1 hR) (SC.wf3_view hfr hw hc) hp.read (fun _ _ h => nomatch h) hi hob
  | @writeShared s s' reg ar c a region order kind h =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    have hc : s.Live c := SC.live_of_exercisable hpre.o11.exercisable
    cases kind with
    | store => exact (writeOps_noRead hm).elim
    | rmw v =>
      have hrd : Read3Pre (s.view c) a region :=
        ⟨hpre.o11.usable, hpre.rmwInit (fun e => by cases e), hpre.o11.exercisable,
          hpre.o11.effectivePresent, hpre.o11.depsValid⟩
      exact readOps_safe (ops := readOps m π.L π.ty region ++ writeOps m π.L π.ty w region) rfl
        ((reprC_view hc).1 hR) (SC.wf3_view hfr hw hc) hrd (fun _ _ h => writeOps_noRead h) hi
        hob
  | @cas s s' reg ar c a l succ fail br h =>
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · cases h
    · cases br with
      | success v =>
        obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
        have hc : s.Live c := SC.live_of_exercisable hpre.o11.exercisable
        have hrd : Read3Pre (s.view c) a [l] :=
          ⟨hpre.o11.usable, hpre.rmwInit (fun e => by cases e), hpre.o11.exercisable,
            hpre.o11.effectivePresent, hpre.o11.depsValid⟩
        exact readOps_safe (ops := readOps m π.L π.ty [l] ++ writeOps m π.L π.ty w [l]) rfl
          ((reprC_view hc).1 hR) (SC.wf3_view hfr hw hc) hrd (fun _ _ h => writeOps_noRead h)
          hi hob
      | failure v =>
        obtain ⟨hp, -⟩ := Guarded.ok_iff.1 h
        have hc : s.Live c := SC.live_of_exercisable hp.read.exercisable
        exact readOps_safe (ops := readOps m π.L π.ty [l]) (rest := []) (List.append_nil _).symm
          ((reprC_view hc).1 hR) (SC.wf3_view hfr hw hc) hp.read (fun _ _ h => nomatch h) hi
          hob

/-! ## The by-value composite -/

/-- The transfer phases of the by-value composite (C5.2; Spec 1 §63, §82.2, §82.3): from a state
whose yielded form satisfies `KBase` and is related to the memory state by `ReprC`, each raw read
of `valOps` is safe in the memory state reached by the raw operations before it, under the
obligations of the raw operations up to it. The preconditions of each phase are read in the state
where the phase starts (`ValTransfersPre`); the state of each later phase is related to its memory
state by `transfer_realized`, as in `vals_realized`. -/
theorem vals_safe {k : K} {fin : S3} {c f : Nat} {ps : List Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)) (m : Machine.State), ValTransfersPre k fin c t vs →
      KBase (yieldEff t ps f) → (∀ v ∈ vs, FrameOwned t.P v.2) →
      (∀ a ∈ ps, ∀ y, t.A[a]? = some y → ∃ g, y.holder = .frame g) →
      ReprC π.L π.rtok t m → ∀ {i : Nat} {ac : Machine.Access} {ty' : Ty},
      (valOps π c t vs m)[i]? = some (.read ac ty') →
      OblAlong ObR ObW m ((valOps π c t vs m).take (i + 1)) →
      SafeRead ObR π (run m ((valOps π c t vs m).take i)) ac ty'
  | _, [], _, _, _, _, _, _, _, _, _, hi, _ => by simp [valOps] at hi
  | t, v :: vs, m, ⟨hpre, hrest⟩, hk, hown, hp, hR, i, ac, ty', hi, hob => by
    simp only [valOps] at hi hob ⊢
    have hcl : t.Live c := SC.live_of_hasRight hpre.srcRight
    have hyw := (view_facts_base hk hcl).1
    have hcl' : (yieldEff t ps f).Live c := hcl
    have hRy : Repr π.L π.rtok ((yieldEff t ps f).view c) m :=
      repr_congr ((reprC_view hcl).1 hR) rfl rfl rfl fun _ => by
        rw [SC.mem_view_F hcl', SC.mem_view_F hcl]; exact Iff.rfl
    have hmem : ∀ g, g ∈ ((yieldEff t ps f).view c).F ↔ g ∈ (t.view c).F := fun g => by
      rw [SC.mem_view_F hcl', SC.mem_view_F hcl]; exact Iff.rfl
    have hu : ∀ q, ((yieldEff t ps f).view c).Usable q ↔ (t.view c).Usable q := fun q =>
      ⟨S3.Usable.mono (s := t.view c) (s' := (yieldEff t ps f).view c) rfl
        (fun g hg => (hmem g).1 hg) (fun _ h => h),
       S3.Usable.mono (s := (yieldEff t ps f).view c) (s' := t.view c) rfl
        (fun g hg => (hmem g).2 hg) (fun _ h => h)⟩
    by_cases hlt : i < (transferOps π.L π.ty m (t.view c) v.1 v.2).length
    · rw [List.getElem?_append_left hlt] at hi
      rw [List.take_append_of_le_length hlt] at hob
      rw [List.take_append_of_le_length (Nat.le_of_lt hlt)]
      exact transfer_safe (t := (yieldEff t ps f).view c) hRy hyw ((hu _).2 hpre.srcUsable)
        hpre.srcInit hi (obl_take_at hi hob)
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt)
      rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hi
      rw [Nat.add_assoc, take_length_add] at hob
      rw [take_length_add, run_append]
      obtain ⟨hob₁, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
      obtain ⟨-, hR₁⟩ := transfer_realized (C := fun _ _ => True) (ty := π.ty) hRy hyw
        ((hu _).2 hpre.srcUsable) ((hu _).2 hpre.dstUsable) hpre.sameShape hpre.srcInit hob₁
      have hR₁' : ReprC π.L π.rtok (transferEffC t c v.1 v.2)
          (run m (transferOps π.L π.ty m (t.view c) v.1 v.2)) :=
        (reprC_set (s := t) (t := transferEff (t.view c) v.1 v.2) fun _ => SC.mem_view_F hcl).2
          (repr_congr hR₁ rfl rfl rfl fun g => (hmem g).symm)
      have hk₁ : KBase (yieldEff (transferEffC t c v.1 v.2) ps f) :=
        transfers_base t [v] ⟨hpre, trivial⟩ hk
          (fun w hw => hown w (by rw [List.mem_singleton.1 hw]; exact List.mem_cons_self ..)) hp
      exact vals_safe (transferEffC t c v.1 v.2) vs _ hrest hk₁
        (fun w hw => transfer_frameOwned (hown w (List.mem_cons_of_mem _ hw)))
        (fun a ha y hy => by
          obtain ⟨y₀, hy₀, e⟩ := transfer_frame_held hy
          obtain ⟨g, hg⟩ := hp a ha y₀ hy₀
          exact ⟨g, by rw [e ⟨g, hg⟩, hg]⟩) hR₁' hi hob₂

/-- **Theorem 9**, safe reads of the by-value composite (C5, C5.2; Spec 1 §63, §72, §82.2–§82.4),
at the grain of abstract steps: every raw read of `rawOps` of the composite, a read of a transfer
phase, is the read of a leaf whose allocation is live and whose range is initialized, and returns
the bytes of that range, in the memory state reached by the creations and the raw operations
before it.

Hypotheses: `ReprC` at the start of the step (Spec 1 §82; C2) and the re-indexed kernel invariant
(`KInvCA`, Spec 1 §57; C20), from which the invariant of each phase is carried (`KBase`); the step,
whose transfer preconditions are read in the state where each phase starts (C5.2); the placement
and geometry of the creations (`PlacementOK`, `GeomOK`, Spec 1 §9 ¶11) and the layout of the new
locals (`NewLayout`, Spec 1 §82.1, §23), which relate the state after the creations to its memory
state (`enter_realized`); the obligations of the raw operations up to the read (Spec 1 §15, §16,
§20.3), since each earlier phase must have run for the state where the read happens to be related
to an abstract state. -/
theorem safe_read_spawnVal {ks : KShared} {ML : MutexLayout} {c : Nat} {ps : List Nat}
    {ls : LocalShape} {vs : List (Nat × Nat)} {st st' : SC × SyncReg × ArenaReg}
    {m : Machine.State} (hpl : PlacementOK π.pl) (hg : GeomOK π.geom)
    (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1)
    (h : LStep ks ML (.spawnVal c ps ls vs) st st')
    (hlay : NewLayout π.L (enterP (st.1.view c) ls) (st.1.view c).P.length m.next π.geom
      (rootIdx ls.toShape))
    {i : Nat} {ac : Machine.Access} {ty' : Ty}
    (hi : (rawOps π w (.spawnVal c ps ls vs) st m)[i]? = some (.read ac ty'))
    (hob : OblAlong ObR ObW m ((rawOps π w (.spawnVal c ps ls vs) st m).take (i + 1))) :
    SafeRead ObR π (run m ((rawOps π w (.spawnVal c ps ls vs) st m).take i)) ac ty' := by
  cases h with
  | @spawnVal s s' reg ar c ps ls vs h =>
    obtain ⟨hpre, -⟩ := Guarded.ok_iff.1 h
    simp only [rawOps] at hi hob ⊢
    have hc : s.Live c := SC.live_of_stk hpre.creatorLive
    obtain ⟨hw, -⟩ := view_facts hk hc
    by_cases hlt : i < (allocOps (Ty := Ty) π.pl π.geom π.rtok (s.view c).P.length m
      (rootIdx ls.toShape)).length
    · rw [List.getElem?_append_left hlt] at hi
      exact (allocOps_noRead _ _ _ _ _ _ (List.mem_iff_getElem?.2 ⟨_, hi⟩)).elim
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_lt hlt)
    rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left] at hi
    rw [Nat.add_assoc, take_length_add] at hob
    rw [take_length_add, run_append]
    obtain ⟨-, hob₂⟩ := (along_append (p := Obl ObR ObW)).1 hob
    obtain ⟨-, hR₁⟩ := enter_realized (C := fun _ _ => True) (ObR := ObR) (ObW := ObW) (ps := [])
      ((reprC_view hc).1 hR) hw hpre.localsOK hpl hg hlay
    have hpush := spawn_push (ps := []) (ls := ls) hk.1.1.1 hpre.creatorLive
    have hR₁' : ReprC π.L π.rtok (spawnCreate s c ls) _ := reprC_of_flat rfl (fun f => by
      show f ∈ (enterEff (s.view c) [] ls).F ↔ f ∈ (spawnEff s c [] ls).frames
      rw [hpush.mem]
      show f ∈ s.nF :: (s.view c).F ↔ _
      rw [List.mem_cons, SC.mem_view_F hc]) hR₁
    have hlt' : ∀ a ∈ ps, a < s.A.length := fun a ha => by
      have := hpre.params a ha
      unfold OptP at this; split at this
      · exact lt_of_getElem? ‹_›
      · exact this.elim
    have hframe : ∀ a ∈ ps, ∀ y, (spawnCreate s c ls).A[a]? = some y →
        ∃ g, y.holder = .frame g := by
      intro a ha y hy
      have hp := hpre.params a ha
      have hy' : (spawnCreate s c ls).A[a]? = s.A[a]? := by
        show (mapI _ 0 s.A ++ _)[a]? = _
        rw [List.getElem?_append_left (by rw [length_mapI]; exact hlt' a ha), getElem?_mapI]
        cases s.A[a]? <;> simp
      rw [hy'] at hy
      have hy₂ : (s.view c).A[a]? = some y := hy
      rw [hy₂] at hp
      exact ⟨_, hp.2.1⟩
    have hb₀ : KBase (yieldEff (spawnCreate s c ls) ps s.nF) := by
      rw [create_yield hlt']; exact spawn_base hk hpre.creatorLive hpre.params hpre.localsOK
    exact vals_safe (spawnCreate s c ls) vs _ hpre.transfers hb₀
      (fun v hv => spawn_frameOwned (hpre.freshDst v hv)) hframe hR₁' hi hob₂

/-! ## Every label, and the reached states -/

/-- **Theorem 9**, safe reads (Spec 1 §82.2, §15, §63, §66; C2, C5.2, C37–C39), at the grain of
abstract steps, for every label: every raw read of `rawOps` of a step executed by any context is
the read of a leaf whose allocation is live and whose range is initialized, and returns the bytes
of that range, in the memory state reached by the raw operations before it (`safe_read_direct`,
`safe_read_spawnVal`).

Hypotheses: `ReprC` and `KInvCA` at the start of the step (Spec 1 §57, §82; C20), the step, the
placement and geometry of the creations (Spec 1 §9 ¶11), the layout of the new locals of a
by-value composite (Spec 1 §82.1, §23), and the obligations of the raw operations up to the read
(Spec 1 §15, §16, §20.3). Only the obligation of the read itself is used for the labels other than
the by-value composite.

The statement is about the bytes the raw read returns, not about the observed value of a label
(C31–C34); for an RMW over more than one leaf (C38), the reads are an auxiliary construction of
`rawOps`, not physical events. -/
theorem safe_read {ks : KShared} {ML : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {m : Machine.State} (hpl : PlacementOK π.pl)
    (hg : GeomOK π.geom) (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1)
    (h : LStep ks ML lbl st st')
    (hlay : ∀ c ps ls vs, lbl = .spawnVal c ps ls vs →
      NewLayout π.L (enterP (st.1.view c) ls) (st.1.view c).P.length m.next π.geom
        (rootIdx ls.toShape))
    {i : Nat} {ac : Machine.Access} {ty' : Ty}
    (hi : (rawOps π w lbl st m)[i]? = some (.read ac ty'))
    (hob : OblAlong ObR ObW m ((rawOps π w lbl st m).take (i + 1))) :
    SafeRead ObR π (run m ((rawOps π w lbl st m).take i)) ac ty' := by
  by_cases hsv : ∃ c ps ls vs, lbl = .spawnVal c ps ls vs
  · obtain ⟨c, ps, ls, vs, rfl⟩ := hsv
    exact safe_read_spawnVal hpl hg hR hk h (hlay c ps ls vs rfl) hi hob
  · exact safe_read_direct hR hk.1.1.1 hk.1.1.2 h
      (fun c ps ls vs e => hsv ⟨c, ps, ls, vs, e⟩) hi (obl_take_at hi hob)

/-- **Theorem 9**, safe reads on the reached states (Spec 1 §82.2, §15, §57; C2, C20), on the model
of `Refinement.r1_read_reachable`: `safe_read` without invariant hypothesis, for a step from the
last state of a translated run (`TransRun`), under `DDSound` (Spec 1 §80), the obligations of the
parameters (`ParamsOK`), and the layout and obligations of the step as in `safe_read`. `ReprC` and
`KInvCA` hold on the states of a translated run (`refinement_run`, `TransRun.kInvCA`). -/
theorem reached_safe_read {C : Nat → Nat → Prop} {ks : KShared} {ML : MutexLayout}
    {statics : Statics} {tr : List (Label × WriteRepr)} {ops : List (Machine.Op Ty)} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} {m : Machine.State} (hdd : DDSound ks.toK)
    (hπ : ParamsOK C π) (hrun : TransRun ks ML C ObR ObW statics π tr ops st m)
    (h : LStep ks ML lbl st st')
    (hlay : ∀ c ps ls vs, lbl = .spawnVal c ps ls vs →
      NewLayout π.L (enterP (st.1.view c) ls) (st.1.view c).P.length m.next π.geom
        (rootIdx ls.toShape))
    {i : Nat} {ac : Machine.Access} {ty' : Ty}
    (hi : (rawOps π w lbl st m)[i]? = some (.read ac ty'))
    (hob : OblAlong ObR ObW m ((rawOps π w lbl st m).take (i + 1))) :
    SafeRead ObR π (run m ((rawOps π w lbl st m).take i)) ac ty' :=
  safe_read hπ.1 hπ.2.1 (refinement_run hdd hπ hrun).2.1 (TransRun.kInvCA hdd hπ hrun) h hlay hi
    hob

end SafeReads

end Ern.ConcurrencyModel
