import Ern.MM23
import Ern.MM03.Horrors

/-!
# MM23-H: adversarial corpus of the refinement (jalon 3, step 3)

The cases of the jalon-3 material (`ERN_Jalon3_materiel.md` v2), §3. Each case is an execution of
MM-03 from `S3.init statics` translated by `simulation` (`Ern.MM23`): an `SimRun` built step by step
by `srun`, which checks each labelled step (`Step3`) and its obligations (`Oblig`) by `decide`, with
parameters fixed once for the run. The layout is computed from the places of the run (`autoL`): the
`n`-th root place has the allocation `n` (MM-02 identities are created in that order, K2), its
leaves 8 bytes each in index order; the allocation of each root has 8 bytes per leaf, aligned on 8
(`autoG`); roots listed in `z` have size zero (K1 (d), D2). Tokens, placement, pointer encoding and
the obligations `dec` (accesses aligned on 4 bytes) are those of the pass-2 run `CaseSim`.

H15 and H16 rest on decisions 2 and 3 of jalon 2, not applied to the draft: they are encoded with
the verdict obtained and marked "écart connu" (material §0, rule 8). H14 and H17 are not encoded
(jalon-3 report, (a)).
-/

namespace Ern.MM23.Horrors

open Ern Ern.MM03 Ern.MM23

/-! ## Executable translated steps -/

section Exec
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- `ok` outcome of a labelled MM-03 step (`Step3`: L1 and L2 envelope included), `none`
otherwise. -/
def step3exec (s : S3) : Op3 → Option S3
  | .derive src q m => if DerivePre s src q m then some (deriveEff s src q m) else none
  | .split src rs => if SplitPre k s src rs then some (splitEff s src rs) else none
  | .release a => if ReleasePre s a then some (releaseEff s a) else none
  | .transfer src dst => if TransferPre k s src dst then some (transferEff s src dst) else none
  | .depend q x => if DependPre s q x then some (dependEff s q x) else none
  | .enter ps ls => if NoOwner ls ∧ EnterPre s ps ls then some (enterEff s ps ls) else none
  | .exit => if ExitPre k s then some (exitEff s) else none
  | .read a ls => if canRead3 s a ls then some s else none
  | .write a ls _ => if canWrite3 s a ls then some (write3Eff s ls) else none
  | .writeShared a ls _ => if WriteSharedPre k s a ls then some (write3Eff s ls) else none
  | .pin p => if PinPre s p then some (pinEff s p true) else none
  | .unpin p => if UnpinPre k s p then some (pinEff s p false) else none
  | .endUse p => if EndUsePre k s p then some (endUseEff s p) else none
  | .free p auth => if FreePre k s p auth then some (freeEff s p) else none
  | .alloc pr ow ls =>
    if (rootIdx ls).length = 1 ∧ AllocStatic k s pr ow ls ∧ k.Satisfiable pr ls s then
      some (allocEff s pr ow ls) else none
  | .newArena st i => if NewArenaPre s st i then some (newArenaEff s st i) else none
  | .issue i via region dst =>
    match s.arenas[i]? with
    | some ar =>
      if IssueStatic k s ar via region dst ∧ Avail ar region ∧ IssueRight s ar region ∧
          AnchorOrderHeld (issueEff s ar region dst).1 then
        some (arenaSet (issueEff s ar region dst).1 i (issueEff s ar region dst).2)
      else none
    | none => none
  | .reset i via => if ResetAtPre k s i via then some (resetAtEff s i) else none
  | .store a p => if StorePre s a p then some (storeEff s a p) else none

end Exec

theorem step3exec_sound {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')]
    [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
    [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
    [∀ p ls s, Decidable (k.Satisfiable p ls s)] {s s' : S3} {op : Op3}
    (h : step3exec k s op = some s') : Step3 k op s s' := by
  cases op <;> simp only [step3exec] at h
  all_goals first
    | (split at h
       · rename_i hp; simp only [Option.some.injEq] at h; subst h
         first
           | exact Guarded.ok hp
           | exact ⟨hp.1, Guarded.ok hp.2⟩
           | exact ⟨by
               obtain ⟨h1, -⟩ := hp
               match hr : rootIdx _, h1 with
               | [i], _ => exact ⟨i, rfl⟩, .ok hp.2.1 hp.2.2⟩
       · cases h)
    | (split at h
       · rename_i ar har
         split at h
         · rename_i hp; simp only [Option.some.injEq] at h; subst h
           exact .ok har (.ok hp.1 hp.2.1 hp.2.2.1 hp.2.2.2)
         · cases h
       · cases h)

instance (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)] (ptok : Nat → Nat)
    (pv : Nat → Option Nat) (p auth : Nat) : Decidable (FreeCompatInst C ptok pv p auth) :=
  match h : pv p with
  | some pr => decidable_of_iff (C auth (ptok pr)) ⟨fun hc => ⟨pr, h, hc⟩,
      fun ⟨pr', h', hc⟩ => by rw [h] at h'; cases h'; exact hc⟩
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; cases h'

instance (k : K) (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)]
    [∀ p a, Decidable (k.FreeCompat p a)] (π : Params) (op : Op3) (pv : Nat → Option Nat) :
    Decidable (FreeOblig k C π op pv) := by
  cases op <;> unfold FreeOblig <;> infer_instance

instance (k : K) (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)]
    [∀ p a, Decidable (k.FreeCompat p a)] (ObR : MM02.ReadOblSpec) (ObW : MM02.WriteOblSpec)
    [∀ s o, Decidable (Op2.Dec ObR ObW s o)] (π : Params) (op : Op3) (s3 s3' : S3)
    (pv : Nat → Option Nat) (s2 : MM02.State) : Decidable (Oblig k C ObR ObW π op s3 s3' pv s2) := by
  unfold Oblig; infer_instance

/-- A state of the translation: the MM-03 state, the ghost `provOf` (L4), the MM-02 state. -/
abbrev SSt := S3 × (Nat → Option Nat) × MM02.State

section Run
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]
  (C : Nat → Nat → Prop) [∀ a b, Decidable (C a b)] (ObR : MM02.ReadOblSpec)
  (ObW : MM02.WriteOblSpec) [∀ s o, Decidable (Op2.Dec ObR ObW s o)] (π : Params)

/-- One translated step (`SimRun.step`): the `ok` MM-03 step, its obligations, then the ghost and
the MM-02 state after the associated sequence (K4, L6). -/
def sexec (st : SSt) (op : Op3) : Option SSt :=
  match step3exec k st.1 op with
  | some s3' =>
    if Oblig k C ObR ObW π op st.1 s3' st.2.1 st.2.2 then
      some (s3', provStep op st.1 st.2.1, exec st.2.2 (assoc π op st.1 st.2.2))
    else none
  | none => none

/-- Translated run of a list of operations, in order of execution. -/
def srun (st : SSt) : List Op3 → Option SSt
  | [] => some st
  | op :: ops => (sexec k C ObR ObW π st op).bind fun st' => srun st' ops

end Run

section RunSound
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]
  {C : Nat → Nat → Prop} [∀ a b, Decidable (C a b)] {ObR : MM02.ReadOblSpec}
  {ObW : MM02.WriteOblSpec} [∀ s o, Decidable (Op2.Dec ObR ObW s o)] {π : Params}
  {statics : Statics}

/-- A successful translated run extends a `SimRun`. -/
theorem srun_sound : ∀ {ops : List Op3} {s3 : S3} {pv : Nat → Option Nat} {os : List Op2}
    {s2 : MM02.State} {ops' : List Op3} {st : SSt},
    SimRun k C ObR ObW statics π ops s3 pv os s2 → srun k C ObR ObW π (s3, pv, s2) ops' = some st →
    ∃ os', SimRun k C ObR ObW statics π (ops'.reverse ++ ops) st.1 st.2.1 os' st.2.2
  | _, _, _, os, _, [], st, h, he => by
    simp only [srun, Option.some.injEq] at he; subst he; exact ⟨os, h⟩
  | ops, s3, pv, os, s2, op :: ops', st, h, he => by
    simp only [srun] at he
    cases hx : sexec k C ObR ObW π (s3, pv, s2) op with
    | none => rw [hx] at he; cases he
    | some st₁ =>
      rw [hx] at he
      simp only [sexec] at hx
      cases hs : step3exec k s3 op with
      | none => rw [hs] at hx; cases hx
      | some s3' =>
        rw [hs] at hx
        simp only at hx
        split at hx
        · rename_i hob
          simp only [Option.some.injEq] at hx; subst hx
          obtain ⟨os', h2⟩ := srun_sound (h.step (step3exec_sound hs) hob) he
          exact ⟨os', by simpa [List.reverse_cons, List.append_assoc] using h2⟩
        · cases hx

theorem srun_append : ∀ (st : SSt) (ops ops' : List Op3),
    srun k C ObR ObW π st (ops ++ ops') =
      (srun k C ObR ObW π st ops).bind fun st' => srun k C ObR ObW π st' ops'
  | st, [], ops' => by simp [srun]
  | st, op :: ops, ops' => by
    simp only [List.cons_append, srun]
    cases sexec k C ObR ObW π st op with
    | none => rfl
    | some st₁ => simp only [Option.bind_some]; exact srun_append st₁ ops ops'

/-- A successful translated step is a labelled MM-03 step with its obligations. -/
theorem sexec_step {st st' : SSt} {op : Op3} (h : sexec k C ObR ObW π st op = some st') :
    ∃ s3', Step3 k op st.1 s3' ∧ Oblig k C ObR ObW π op st.1 s3' st.2.1 st.2.2 ∧
      st' = (s3', provStep op st.1 st.2.1, exec st.2.2 (assoc π op st.1 st.2.2)) := by
  simp only [sexec] at h
  cases hs : step3exec k st.1 op with
  | none => rw [hs] at h; cases h
  | some s3' =>
    rw [hs] at h
    simp only at h
    split at h
    · rename_i hob
      simp only [Option.some.injEq] at h
      exact ⟨s3', step3exec_sound hs, hob, h.symm⟩
    · cases h

end RunSound

/-! ## Parameters of the runs -/

/-- Root place of `q`: the last element of its chain of parents (MM-03.3.2). -/
def rootOf (P : List Place) (q : Nat) : Nat := (chain (parentOf P) q).getLastD q

/-- Number of root places below `r`: the MM-02 identity of the allocation of the root `r` when every
root is laid out in its own allocation, in index order (K2). -/
def rootRank (P : List Place) (r : Nat) : Nat :=
  ((List.range r).filter fun i => decide (i < P.length ∧ parentOf P i = none)).length

/-- Number of leaves of the root of `l` below `l`. -/
def leafRank (P : List Place) (l : Nat) : Nat :=
  ((List.range l).filter fun i => decide (i < P.length ∧ isLeaf P i ∧ rootOf P i = rootOf P l)).length

/-- Layout of the runs (K1): a place in the allocation of its root, a leaf at 8 times its rank,
8 bytes; size zero for the roots of `z`. -/
def autoL (P : List Place) (z : List Nat) : Layout := fun q =>
  if rootOf P q ∈ z then ⟨rootRank P (rootOf P q), 0, 0⟩
  else ⟨rootRank P (rootOf P q), 8 * leafRank P q, 8⟩

/-- Geometry of the allocation of the root `r` (K2): 8 bytes per leaf, aligned on 8; size zero for
the roots of `z`. -/
def autoG (P : List Place) (z : List Nat) : Nat → Geom := fun r =>
  if r ∈ z then ⟨0, 0, 8⟩ else ⟨0, 8 * (footprint P r).length, 8⟩

/-- Compatibility by equality of tokens (`TokCompat`, as in `CaseSim`). -/
abbrev Ceq : Nat → Nat → Prop := fun a d => a = d

/-- Parameters of a run whose final places are `P` (`Params`): the layout and geometry above, the
tokens, placement, pointer encoding and bytes of `CaseSim`. -/
def piOf (P : List Place) (z : List Nat) : Params :=
  ⟨autoL P z, fun f => 100 + f, fun pr => 6 + pr, topPlacement, autoG P z, CaseSim.pe, CaseSim.w⟩

theorem piOf_geom (P : List Place) (z : List Nat) (r : Nat) :
    0 < ((piOf P z).geom r).align ∧ MM02.Pow2 ((piOf P z).geom r).align := by
  simp only [piOf, autoG]
  split <;> exact ⟨Nat.succ_pos 7, ⟨3, rfl⟩⟩

/-- Initial state of a translation: `S3.init statics`, empty ghost, the MM-02 run of `repr_init`. -/
def sinit (statics : Statics) (π : Params) : SSt :=
  (S3.init statics, fun _ => none, exec MM02.State.empty (initOpsOf π statics))

/-- The MM-03 operation of a labelled one, the bytes of a write dropped. -/
def toOp : Op3 → Ern.HandlePool.Op
  | .derive src q m => .derive src q m
  | .split src rs => .split src rs
  | .release a => .release a
  | .transfer src dst => .transfer src dst
  | .depend q x => .depend q x
  | .enter ps ls => .enter ps ls
  | .exit => .exit
  | .read a ls => .read a ls
  | .write a ls _ => .write a ls
  | .writeShared a ls _ => .writeShared a ls
  | .pin p => .pin p
  | .unpin p => .unpin p
  | .endUse p => .endUse p
  | .free p auth => .free p auth
  | .alloc pr ow ls => .alloc pr ow ls
  | .newArena st i => .newArena st i
  | .issue i via region dst => .issue i via region dst
  | .reset i via => .reset i via
  | .store a p => .store a p

section Cases
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- The state reached by the translated run of `ops` (or the initial state if it fails). -/
def sst (statics : Statics) (π : Params) (ops : List Op3) : SSt :=
  (srun k Ceq CaseSim.obR CaseSim.obW π (sinit statics π) ops).getD (sinit statics π)

end Cases

section Sim
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A successful translated run from the initial state is a `SimRun`. -/
theorem simRun_of {statics : Statics} {P : List Place} {z : List Nat} {ops : List Op3}
    (hsh : ShapeOK 0 (statics.map (·.1)))
    (hlay : NewLayout (piOf P z).L (S3.init statics).P 0 0 (piOf P z).geom
      (rootIdx (statics.map (·.1))))
    (hdec : DecAlong CaseSim.obR CaseSim.obW MM02.State.empty (initOpsOf (piOf P z) statics))
    (h : (srun k Ceq CaseSim.obR CaseSim.obW (piOf P z) (sinit statics (piOf P z)) ops).isSome =
      true) :
    ∃ os, SimRun k Ceq CaseSim.obR CaseSim.obW statics (piOf P z) ops.reverse
      (sst k statics (piOf P z) ops).1 (sst k statics (piOf P z) ops).2.1 os
      (sst k statics (piOf P z) ops).2.2 := by
  obtain ⟨os, h'⟩ := srun_sound (SimRun.init (k := k) (C := Ceq) hsh hlay hdec)
    (Ern.HandlePool.some_getD (d := sinit statics (piOf P z)) h)
  rw [List.append_nil] at h'
  exact ⟨os, h'⟩

/-- `simulation` on a translated run: the MM-02 run from `State.empty` has only `ok` outcomes,
reaches the MM-02 state of the run, which is in `Repr` with the MM-03 state, reached. -/
theorem sim_of {statics : Statics} {P : List Place} {z : List Nat} {ops : List Op3}
    (hdd : DDSound k) (hsh : ShapeOK 0 (statics.map (·.1)))
    (hlay : NewLayout (piOf P z).L (S3.init statics).P 0 0 (piOf P z).geom
      (rootIdx (statics.map (·.1))))
    (hdec : DecAlong CaseSim.obR CaseSim.obW MM02.State.empty (initOpsOf (piOf P z) statics))
    (h : (srun k Ceq CaseSim.obR CaseSim.obW (piOf P z) (sinit statics (piOf P z)) ops).isSome =
      true) :
    ∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
      exec MM02.State.empty os = (sst k statics (piOf P z) ops).2.2 ∧
      Repr (piOf P z).tok (piOf P z).ptok (sst k statics (piOf P z) ops).2.1 (piOf P z).L
        (sst k statics (piOf P z) ops).1 (sst k statics (piOf P z) ops).2.2 ∧
      Reachable k statics (sst k statics (piOf P z) ops).1 := by
  obtain ⟨os, h'⟩ := simRun_of hsh hlay hdec h
  have := simulation hdd (fun _ _ => trivial) (fun _ _ _ => trivial) topPlacement_ok
    (piOf_geom P z) (fun _ => rfl) h'
  exact ⟨os, this.1, this.2.1, this.2.2.1, this.2.2.2.1⟩

/-- R6 at one step of a translated run: the MM-02 sequence associated with the step `op` after the
prefix `ops` has only `ok` outcomes in the MM-02 state of the prefix (`simulation` on the prefix and
on the prefix extended by the step). -/
theorem step_ok_of {statics : Statics} {P : List Place} {z : List Nat} {ops : List Op3}
    {op : Op3} (hdd : DDSound k) (hsh : ShapeOK 0 (statics.map (·.1)))
    (hlay : NewLayout (piOf P z).L (S3.init statics).P 0 0 (piOf P z).geom
      (rootIdx (statics.map (·.1))))
    (hdec : DecAlong CaseSim.obR CaseSim.obW MM02.State.empty (initOpsOf (piOf P z) statics))
    (h : (srun k Ceq CaseSim.obR CaseSim.obW (piOf P z) (sinit statics (piOf P z))
      (ops ++ [op])).isSome = true) :
    AllOk Ceq CaseSim.obR CaseSim.obW (sst k statics (piOf P z) ops).2.2
      (assoc (piOf P z) op (sst k statics (piOf P z) ops).1 (sst k statics (piOf P z) ops).2.2) := by
  rw [srun_append] at h
  cases hp : srun k Ceq CaseSim.obR CaseSim.obW (piOf P z) (sinit statics (piOf P z)) ops with
  | none => rw [hp] at h; cases h
  | some st₀ =>
    rw [hp] at h
    simp only [Option.bind_some, srun] at h
    cases hx : sexec k Ceq CaseSim.obR CaseSim.obW (piOf P z) st₀ op with
    | none => rw [hx] at h; cases h
    | some st₁ =>
      have hst : sst k statics (piOf P z) ops = st₀ := by simp [sst, hp]
      obtain ⟨os, ht⟩ := simRun_of (k := k) hsh hlay hdec (by rw [hp]; rfl)
      rw [hst] at ht ⊢
      obtain ⟨s3', hs, hob, -⟩ := sexec_step hx
      have h₁ := simulation hdd (fun _ _ => trivial) (fun _ _ _ => trivial) topPlacement_ok
        (piOf_geom P z) (fun _ => rfl) ht
      have h₂ := simulation hdd (fun _ _ => trivial) (fun _ _ _ => trivial) topPlacement_ok
        (piOf_geom P z) (fun _ => rfl) (ht.step hs hob)
      have := along_append.1 h₂.1
      rw [h₁.2.1] at this
      exact this.2

end Sim

/-- The value of a successful read of MM-02 exists when the provenance names an allocation and the
read conditions hold (MM-02.B). -/
theorem read_ok_of {ObR : MM02.ReadOblSpec} {ac : MM02.Access} {s : MM02.State}
    (ha : (s.allocs ac.prov).isSome = true) (h : MM02.Read s ac ∧ ObR.dec s ac ∧ ObR.stat s ac) :
    ∃ v, MM02.ReadStep ObR ac s (.ok v) := by
  cases hs : s.allocs ac.prov with
  | none => rw [hs] at ha; cases ha
  | some a => exact ⟨_, .ok hs h⟩

/-- `SameSizeAlong` read on the pairs of the transfer: decidable form. -/
theorem sameSize_of {L : Layout} {P : List Place} {src dst : Nat}
    (h : ∀ p ∈ transferPairs P src dst, (L p.1).len = (L p.2).len) : SameSizeAlong L P src dst :=
  fun l l' hm => h (l, l') hm

/-- The kind of an MM-02 operation: 0 read, 1 write, 2 deallocation, 3 allocation. -/
def opTag : Op2 → Nat
  | .read _ => 0
  | .write _ _ => 1
  | .dealloc _ _ => 2
  | .alloc .. => 3

/-- The size of an MM-02 allocation. -/
def opAllocSize : Op2 → Option Nat
  | .alloc _ _ sz _ _ => some sz
  | _ => none

/-- An abstract byte is initialised (MM-02.3). -/
def initB : MM02.AByte → Bool
  | .init _ _ => true
  | .uninit => false

/-- The allocation an MM-02 operation reads, writes or deallocates. -/
def opAlloc : Op2 → Option Nat
  | .read ac => some ac.prov
  | .write ac _ => some ac.prov
  | .dealloc i _ => some i
  | .alloc .. => none

/-- The allocation and authority of a deallocation. -/
def opDealloc : Op2 → Option (Nat × Nat)
  | .dealloc i a => some (i, a)
  | _ => none

/-- A root leaf of a shape. -/
abbrev lf : Option Nat × Option Nat × Nat := (none, none, 0)
/-- The bytes written by the runs (`CaseSim.w`). -/
abbrev w : Nat → Nat → UInt8 × Option Nat := CaseSim.w

/-! ## Run R1: owned storage, pin, transfer, leak, exit (H03, H04, H07, H08, H09) -/

/-- Contracts of R1: `ExternalDone` for the leaf 3. -/
abbrev K1 : K := KT [] [] [3] [] []

/-- R1: frame 1 with the allocator 0 and the leaves `v` (1) and `w` (2), written; the storage 3,
allocated for `v` and written; 3 pinned; `transfer v w`; 3 unpinned; `endUse w`; exit. -/
def r1 : List Op3 := [.enter [] [lf, lf, lf], .write 0 [0] w, .write 1 [1] w,
  .alloc 0 1 [lf], .write 3 [3] w, .pin 3, .transfer 1 2, .unpin 3, .endUse 2, .exit]
def P1 : List Place := (Ern.MM03.Horrors.run K1 [] (r1.map toOp)).s.P
def π1 : Params := piOf P1 []
/-- R1 before the transfer, after it, before the exit, at the end. -/
def r1a : SSt := sst K1 [] π1 (r1.take 6)
def r1b : S3 := (step3exec K1 r1a.1 (.transfer 1 2)).getD r1a.1
def r1e : SSt := sst K1 [] π1 (r1.take 9)
def r1f : SSt := sst K1 [] π1 r1

theorem R1_sim : ∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
    exec MM02.State.empty os = r1f.2.2 ∧ Repr π1.tok π1.ptok r1f.2.1 π1.L r1f.1 r1f.2.2 :=
  (sim_of (P := P1) (z := []) (KT_dd _ _ _ _ _) (by decide) (by decide) (by decide) (by decide)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

theorem R1_prefix : ∃ os, SimRun K1 Ceq CaseSim.obR CaseSim.obW [] π1 (r1.take 6).reverse r1a.1
    r1a.2.1 os r1a.2.2 :=
  simRun_of (P := P1) (z := []) (by decide) (by decide) (by decide) (by decide)

theorem R1_step6 : Step3 K1 (.transfer 1 2) r1a.1 r1b :=
  step3exec_sound (Ern.HandlePool.some_getD (by decide))

/-- **MM23-H03** (passe 2, `pinned_address_stable`). Transfer of a value whose owned storage is
pinned: the leaf 3 of the storage has a live allocation before and after the step, at the same
address (L8), and the MM-02 sequence of the transfer touches no allocation of the storage. Expected:
no MM-02 step on the storage, address unchanged; obtained: the same. -/
theorem H03 : LiveAlloc r1a.2.2 (π1.L 3).alloc ∧
    LiveAlloc (exec r1a.2.2 (assoc π1 (.transfer 1 2) r1a.1 r1a.2.2)) (π1.L 3).alloc ∧
    leafAddr (exec r1a.2.2 (assoc π1 (.transfer 1 2) r1a.1 r1a.2.2)) π1.L 3 =
      leafAddr r1a.2.2 π1.L 3 ∧
    ∀ o ∈ assoc π1 (.transfer 1 2) r1a.1 r1a.2.2, opAlloc o ≠ some (π1.L 3).alloc := by
  obtain ⟨_, ht⟩ := R1_prefix
  refine ⟨?_, ?_, ?_, by decide⟩ <;>
  first
    | exact (simulation_pinned (KT_dd _ _ _ _ _) (fun _ _ => trivial) (fun _ _ _ => trivial)
        topPlacement_ok (piOf_geom _ _) (fun _ => rfl) ht R1_step6 (by decide) (l := 3)
        (by decide) (by decide) (.inl (by decide))).1
    | exact (simulation_pinned (KT_dd _ _ _ _ _) (fun _ _ => trivial) (fun _ _ _ => trivial)
        topPlacement_ok (piOf_geom _ _) (fun _ => rfl) ht R1_step6 (by decide) (l := 3)
        (by decide) (by decide) (.inl (by decide))).2.1
    | exact (simulation_pinned (KT_dd _ _ _ _ _) (fun _ _ => trivial) (fun _ _ _ => trivial)
        topPlacement_ok (piOf_geom _ _) (fun _ => rfl) ht R1_step6 (by decide) (l := 3)
        (by decide) (by decide) (.inl (by decide))).2.2

/-- **MM23-H04** (passe 2, `transfer_copies`). Transfer of a value in place (`v` into `w`): its
MM-02 sequence is a read then a write; the range of `w` receives the bytes of `v`, provenance
included, and the bytes of `v` stay as they were, every one initialised; in MM-03 the source is
`Moved` and unreadable (I4). Expected: the same; obtained: the same. -/
theorem H04 : (assoc π1 (.transfer 1 2) r1a.1 r1a.2.2).map opTag = [0, 1] ∧
    rangeBytes (exec r1a.2.2 (assoc π1 (.transfer 1 2) r1a.1 r1a.2.2)) π1.L 2 =
      rangeBytes r1a.2.2 π1.L 1 ∧
    rangeBytes (exec r1a.2.2 (assoc π1 (.transfer 1 2) r1a.1 r1a.2.2)) π1.L 1 =
      rangeBytes r1a.2.2 π1.L 1 ∧
    (rangeBytes r1a.2.2 π1.L 1).map (·.all initB) = some true ∧
    r1b.I 1 = .moved ∧ ∀ a, ¬ CanReadLeaf r1b a 1 := by
  obtain ⟨_, ht⟩ := R1_prefix
  have hs := simulation (KT_dd _ _ _ _ _) (fun _ _ => trivial) (fun _ _ _ => trivial)
    topPlacement_ok (piOf_geom _ _) (fun _ => rfl) ht
  have hwf := (reachable_invariants (KT_dd _ _ _ _ _) hs.2.2.2.1).1
  have hc := transfer_copies hwf hs.2.2.1 R1_step6 (sameSize_of (by decide)) 1 2 (by decide)
  exact ⟨by decide, hc.1, hc.2, by decide, by decide, fun a h => by
    have h2 := h.2.1
    rw [show r1b.I 1 = .moved by decide] at h2; cases h2⟩

/-- **MM23-H07**, `ok` (passe 1). The `alloc` of R1 is one allocation of MM-02, of the size of the
geometry of the new root (8 bytes, one leaf), with the outcome `ok` (`step_ok_of`). -/
theorem H07_ok : (assoc π1 (.alloc 0 1 [lf]) (sst K1 [] π1 (r1.take 3)).1
      (sst K1 [] π1 (r1.take 3)).2.2).map opAllocSize = [some 8] ∧
    AllOk Ceq CaseSim.obR CaseSim.obW (sst K1 [] π1 (r1.take 3)).2.2
      (assoc π1 (.alloc 0 1 [lf]) (sst K1 [] π1 (r1.take 3)).1 (sst K1 [] π1 (r1.take 3)).2.2) :=
  ⟨by decide, step_ok_of (k := K1) (statics := []) (P := P1) (z := []) (ops := r1.take 3)
    (KT_dd [] [] [3] [] []) (by decide)
    (by decide) (by decide) (by decide)⟩

/-- **MM23-H08** (passe 1, `leaked`). `endUse` of `w`, whose owned storage 3 is not freed: no MM-02
step; the storage is logically dead and not freed, its allocation live (a leak). Expected: the
same; obtained: the same. -/
theorem H08 : assoc π1 (.endUse 2) (sst K1 [] π1 (r1.take 8)).1 (sst K1 [] π1 (r1.take 8)).2.2 = [] ∧
    r1e.1.dead 3 = true ∧ r1e.1.freed 3 = false ∧ LiveAlloc r1e.2.2 (π1.L 3).alloc :=
  ⟨rfl, by decide, by decide, by decide⟩

/-- **MM23-H09** (passe 1). The exit of frame 1: one deallocation per automatic allocation of the
frame (its locals 0, 1, 2, with the frame token 101), each `ok` (`step_ok_of`), none for the owned
storage 3, still live afterwards. Expected: the same; obtained: the same. -/
theorem H09 : (assoc π1 .exit r1e.1 r1e.2.2).map opDealloc =
      [some ((π1.L 0).alloc, 101), some ((π1.L 1).alloc, 101), some ((π1.L 2).alloc, 101)] ∧
    AllOk Ceq CaseSim.obR CaseSim.obW (sst K1 [] π1 (r1.take 9)).2.2
      (assoc π1 .exit (sst K1 [] π1 (r1.take 9)).1 (sst K1 [] π1 (r1.take 9)).2.2) ∧
    DeadAlloc r1f.2.2 (π1.L 0).alloc ∧ DeadAlloc r1f.2.2 (π1.L 1).alloc ∧
    DeadAlloc r1f.2.2 (π1.L 2).alloc ∧ LiveAlloc r1f.2.2 (π1.L 3).alloc :=
  ⟨by decide, step_ok_of (k := K1) (statics := []) (P := P1) (z := []) (ops := r1.take 9)
    (op := .exit) (KT_dd [] [] [3] [] [])
    (by decide) (by decide) (by decide) (by decide), by decide, by decide, by decide, by decide⟩

/-! ## Run R2: arena, block written, transferred, read, reset (H02, H06, H13) -/

/-- R2: frame 1 with the arena value 0, the allocator 1, the leaves `v` (2) and `q` (3); storage 4
with the leaves 5 and 6, owned by 0, `internal` 4; the block 5 on `[5]` issued to `v`; the leaf 5
written through the block; `transfer v q`; `read q`; `endUse q`; `reset`. -/
def r2 : List Op3 := [.enter [] [lf, lf, lf, lf], .write 1 [1] w,
  .alloc 1 0 [lf, (some 4, none, 0), (some 4, none, 0)], .write 0 [0] w, .newArena 4 4,
  .issue 0 0 [5] 2, .write 5 [5] w, .transfer 2 3, .read 3 [3], .endUse 3, .reset 0 0]
def P2 : List Place := (Ern.MM03.Horrors.run K0 [] (r2.map toOp)).s.P
def π2 : Params := piOf P2 []
def r2i : SSt := sst K0 [] π2 (r2.take 7)
def r2r : SSt := sst K0 [] π2 (r2.take 8)
def r2f : SSt := sst K0 [] π2 r2

theorem R2_sim : ∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
    exec MM02.State.empty os = r2f.2.2 ∧ Repr π2.tok π2.ptok r2f.2.1 π2.L r2f.1 r2f.2.2 :=
  (sim_of (P := P2) (z := []) (KT_dd _ _ _ _ _) (by decide) (by decide) (by decide) (by decide)).imp
    fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- After an accepted `reset`, no authority derived from `internal` is active (MM-03.3 §6, O19.2):
the old blocks cannot be used (R4 with `ResetPre`). -/
theorem reset_kills_blocks {k : K} {s s' : S3} {i via : Nat} (h : ResetAtStep k i via s (.ok s'))
    {ar : Arena} (har : s.arenas[i]? = some ar) :
    ∀ j ∈ List.range s'.A.length, ar.internal ∈ s'.ancs j → ¬ s'.Active j := by
  obtain ⟨hpre, rfl⟩ := Guarded.ok_iff.1 h
  simp only [ResetAtPre, har, OptP] at hpre
  simp only [resetAtEff, har, resetEff, arenaSet]
  exact hpre.2.2.1

/-- The old blocks stay inactive after the `reset`, whatever the later steps of `Reachable`
(MM-03.3 §3–6: no step reactivates an authority, `Steps.keeps`). -/
theorem reset_kills_blocks_after {k : K} {s s' s'' : S3} {i via : Nat}
    (h : ResetAtStep k i via s (.ok s')) {ar : Arena} (har : s.arenas[i]? = some ar)
    (hs : Ern.HandlePool.Steps k s' s'') :
    ∀ j < s'.A.length, ar.internal ∈ s'.ancs j → ¬ s''.Active j :=
  fun j hj ha hact => reset_kills_blocks h har j (List.mem_range.2 hj) ha
    ((Ern.HandlePool.Steps.keeps hs).active hj hact)

/-- **MM23-H02** (to state: R4 and `ResetPre`). After `reset`, the old block 5 is inactive and
stays so whatever the later steps (`reset_kills_blocks_after` for every old block), so no safe
program reads through it (the read through it is rejected), while MM-02 accepts a read of its range:
the allocation of the storage is live and the bytes written through the block are initialised. In
R2 the block was already released by `endUse q`, which `reset` requires (O19.2). Twin: the same read
through the block before its end is accepted. Expected: no safe program reaches it, MM-02 would
accept it; obtained: the same. -/
theorem H02 : ¬ r2f.1.Active 5 ∧ Read3Step 5 [5] r2f.1 .reject ∧ Read3Step 5 [5] r2i.1 (.ok r2i.1) ∧
    (∀ s', Ern.HandlePool.Steps K0 r2f.1 s' → ¬ s'.Active 5) ∧
    LiveAlloc r2f.2.2 (π2.L 5).alloc ∧
    ∃ v, MM02.ReadStep CaseSim.obR (leafAcc r2f.2.2 π2.L .read 5) r2f.2.2 (.ok v) :=
  ⟨by decide, .reject (by decide), .ok (by decide), fun _ hs ha =>
    absurd ((Ern.HandlePool.Steps.keeps hs).active (by decide) ha) (by decide), by decide,
    read_ok_of (by decide) ⟨by decide, by simp only [CaseSim.obR]; decide, trivial⟩⟩

/-- Contracts declaring deallocable, with the authority 7, both the storage 4 of R2 and the region
5 of its block. -/
abbrev K2f : K := KT [] [] [] [4, 5] [(4, 7), (5, 7)]

/-- R2 under `K2f` before the transfer, and after the end of the block value. -/
def r2k : SSt := sst K2f [] π2 (r2.take 7)
def r2kt : SSt := sst K2f [] π2 (r2.take 10)

/-- **MM23-H06** (passe 1). `free` of the block on `[5]` is rejected in MM-03 even when the contracts
declare it deallocable and compatible: the region is a part of the storage, not an owned root
(`OwnedRoot`, A6), and its leaf lies in the allocation of the storage. Expected: impossible, not an
allocation; obtained: the same. Every state is reached under `K2f`. Twin: in the same run, once the
block value has ended, the `free` of the allocated storage 4 is accepted. -/
theorem H06 : Reachable K2f [] r2k.1 ∧ K2f.Deallocable 5 ∧ K2f.FreeCompat 5 7 ∧
    ¬ OwnedRoot r2k.1 5 ∧ FreeStep K2f 5 7 r2k.1 .reject ∧ (π2.L 5).alloc = (π2.L 4).alloc ∧
    Reachable K2f [] r2kt.1 ∧ FreeStep K2f 4 7 r2kt.1 (.ok (freeEff r2kt.1 4)) := by
  obtain ⟨_, -, -, -, h₁⟩ := sim_of (k := K2f) (statics := []) (P := P2) (z := [])
    (ops := r2.take 7) (KT_dd [] [] [] [4, 5] [(4, 7), (5, 7)]) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨_, -, -, -, h₂⟩ := sim_of (k := K2f) (statics := []) (P := P2) (z := [])
    (ops := r2.take 10) (KT_dd [] [] [] [4, 5] [(4, 7), (5, 7)]) (by decide) (by decide)
    (by decide) (by decide)
  exact ⟨h₁, by decide, by decide, by decide, .reject (by decide), by decide, h₂, .ok (by decide)⟩

/-- **MM23-H13** (passe 2). The block value `v` holds a pointer (L6: the address of the leaf 5,
the provenance of the storage); after `transfer v q`, the range of `q` holds the same bytes, every
byte with that provenance, and the read of `q` returns them. Expected: provenance kept; obtained:
the same. -/
theorem H13 : rangeBytes r2r.2.2 π2.L 3 = rangeBytes r2i.2.2 π2.L 2 ∧
    (rangeBytes r2r.2.2 π2.L 3).map (fun bs => bs.all fun b => b == .init 0 (some (π2.L 4).alloc) ||
      match b with | .init _ p => p == some (π2.L 4).alloc | .uninit => false) = some true ∧
    ∃ v, MM02.ReadStep CaseSim.obR (leafAcc r2r.2.2 π2.L .read 3) r2r.2.2 (.ok v) :=
  ⟨by decide, by decide,
    read_ok_of (by decide) ⟨by decide, by simp only [CaseSim.obR]; decide, trivial⟩⟩

/-! ## Run R3: statics, read, `writeShared`, free, exit (H05, H10, H11, H12) -/

/-- Contracts of R3: the leaf 3 `SharedMutable`; the storage 4 deallocable with the authority 7. -/
abbrev K3 : K := KT [3] [] [] [4] [(4, 7)]
/-- One static leaf, `Init`. -/
def stZ : Statics := [((none, none, 0), true)]

/-- R3: the base frame reads the static 0; frame 1 with the allocator 1, `x` (2), written, and the
`SharedMutable` leaf 3; 4, `Observe` on 3, writes it by `writeShared`; the storage 4 allocated for
`x` by the allocator 1, then freed with the authority 7; exit. -/
def r3 : List Op3 := [.read 0 [0], .enter [] [lf, lf, lf], .write 1 [1] w, .write 2 [2] w,
  .derive 3 3 .observe, .writeShared 4 [3] w, .alloc 1 2 [lf], .free 4 7, .exit]
def P3 : List Place := (Ern.MM03.Horrors.run K3 stZ (r3.map toOp)).s.P
def π3 : Params := piOf P3 []
def r3f : SSt := sst K3 stZ π3 r3

theorem R3_sim : ∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
    exec MM02.State.empty os = r3f.2.2 ∧ Repr π3.tok π3.ptok r3f.2.1 π3.L r3f.1 r3f.2.2 :=
  (sim_of (P := P3) (z := []) (KT_dd _ _ _ _ _) (by decide) (by decide) (by decide)
    (by decide)).imp fun _ h => ⟨h.1, h.2.1, h.2.2.1⟩

/-- **MM23-H05** (passe 2, `freeSound_derived`). `free 4 7`: one `DeallocStep` of the allocation of
the root 4 with the authority 7, compatible with the token of its provider 1 (L4: `FreeCompat`
instantiated by `FreeCompatInst`), `ok` (`step_ok_of`); the allocation is dead afterwards.
Expected: the same; obtained: the same. -/
theorem H05 : (assoc π3 (.free 4 7) (sst K3 stZ π3 (r3.take 7)).1
      (sst K3 stZ π3 (r3.take 7)).2.2).map opDealloc = [some ((π3.L 4).alloc, 7)] ∧
    FreeCompatInst Ceq π3.ptok (sst K3 stZ π3 (r3.take 7)).2.1 4 7 ∧
    AllOk Ceq CaseSim.obR CaseSim.obW (sst K3 stZ π3 (r3.take 7)).2.2
      (assoc π3 (.free 4 7) (sst K3 stZ π3 (r3.take 7)).1 (sst K3 stZ π3 (r3.take 7)).2.2) ∧
    DeadAlloc r3f.2.2 (π3.L 4).alloc ∧ (r3f.2.2.allocs (π3.L 4).alloc).map (·.freeAuth) = some (some 7) :=
  ⟨by decide, by decide, step_ok_of (k := K3) (statics := stZ) (P := P3) (z := []) (ops := r3.take 7)
    (op := .free 4 7) (KT_dd [3] [] [] [4] [(4, 7)]) (by decide) (by decide) (by decide) (by decide), by decide, by decide⟩

/-- **MM23-H10** (passe 1). The allocation of the static 0 is live after every prefix of the run,
frame exit included. Expected: never deallocated; obtained: live at every step. -/
theorem H10 : ∀ n ∈ List.range (r3.length + 1),
    LiveAlloc (sst K3 stZ π3 (r3.take n)).2.2 (π3.L 0).alloc := by
  decide

/-- **MM23-H11** (passe 1, R1). The read of the `Init` static leaf by the base frame: one read of
MM-02, `ok`. Expected: `ReadStep` `ok`; obtained: the same. -/
theorem H11 : assoc π3 (.read 0 [0]) (sinit stZ π3).1 (sinit stZ π3).2.2 =
      [.read (leafAcc (sinit stZ π3).2.2 π3.L .read 0)] ∧
    ∃ v, MM02.ReadStep CaseSim.obR (leafAcc (sinit stZ π3).2.2 π3.L .read 0) (sinit stZ π3).2.2
      (.ok v) :=
  ⟨rfl, read_ok_of (by decide) ⟨by decide, by simp only [CaseSim.obR]; decide, trivial⟩⟩

/-- **MM23-H12** (passe 1, R2). The `writeShared` of the leaf 3: one ordinary write of MM-02, `ok`.
Expected: an ordinary `WriteStep`, sequential; obtained: the same. -/
theorem H12 : assoc π3 (.writeShared 4 [3] w) (sst K3 stZ π3 (r3.take 5)).1
      (sst K3 stZ π3 (r3.take 5)).2.2 =
      [.write (leafAcc (sst K3 stZ π3 (r3.take 5)).2.2 π3.L .write 3) (w 3)] ∧
    MM02.WriteStep CaseSim.obW (leafAcc (sst K3 stZ π3 (r3.take 5)).2.2 π3.L .write 3) (w 3)
      (sst K3 stZ π3 (r3.take 5)).2.2
      (.ok ((sst K3 stZ π3 (r3.take 5)).2.2.write
        (leafAcc (sst K3 stZ π3 (r3.take 5)).2.2 π3.L .write 3) (w 3))) :=
  ⟨rfl, .ok ⟨by decide, by simp only [CaseSim.obW]; decide, trivial⟩⟩

/-! ## Run R4: declared disjointness (H01) -/

/-- R4: frame 1 with the structure 0 of the parts 1 and 2. -/
def r4 : List Op3 := [.enter [] [lf, (some 0, none, 0), (some 0, none, 0)]]
def P4 : List Place := (Ern.MM03.Horrors.run K0 [] (r4.map toOp)).s.P
def π4 : Params := piOf P4 []

/-- Decision 1 of jalon 2, the source of MM23-H01: the contracts whose `DeclaredDisjoint` is the
disjointness of the leaves of the two regions, as a parameter `K` (the draft `MM23` is unchanged). -/
def KLf : K := { K0 with DeclaredDisjoint := fun r r' => ∀ l ∈ r, l ∉ r' }

instance : ∀ r r', Decidable (KLf.DeclaredDisjoint r r') := fun r r' =>
  inferInstanceAs (Decidable (∀ l ∈ r, l ∉ r'))
instance : DecidablePred KLf.SharedMutable := fun l =>
  inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : DecidablePred KLf.Pinned := fun l => inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : DecidablePred KLf.ExternalDone := fun l =>
  inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : DecidablePred KLf.Deallocable := fun l =>
  inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : ∀ p a, Decidable (KLf.FreeCompat p a) := fun p a =>
  inferInstanceAs (Decidable ((p, a) ∈ ([] : List (Nat × Nat))))
instance : ∀ p ls s, Decidable (KLf.Satisfiable p ls s) := fun _ _ _ => instDecidableTrue

/-- `DDSound` of the instantiation by leaf disjointness: immediate (MM-03.3.8). -/
theorem KLf_dd : DDSound KLf := fun _ _ h => h

def r4s : SSt := sst KLf [] π4 r4
/-- R4 after the `split` of the structure into the regions `[1]` and `[2]`. -/
def r4d : SSt := sst KLf [] π4 (r4 ++ [.split 0 [[1], [2]]])

/-- **MM23-H01** (decision 1 of jalon 2; L7, `byteDisjoint_of_leaves`). With `DeclaredDisjoint`
instantiated by the disjointness of the leaves, two regions sharing the leaf 2 are not declared
disjoint and their `split` is rejected; the regions `[1]` and `[2]` are declared disjoint and their
`split` runs in a translated execution. In its MM-02 state, every pair of declared regions of leaves
has disjoint bytes, through `LayoutWF` of `Repr`. Expected: rejected through `DDSound`
(instantiation by leaves), declared regions with disjoint bytes; obtained: the same. -/
theorem H01 : DDSound KLf ∧ ¬ KLf.DeclaredDisjoint [1, 2] [2] ∧
    SplitStep KLf 0 [[1, 2], [2]] r4s.1 .reject ∧ KLf.DeclaredDisjoint [1] [2] ∧
    SplitStep KLf 0 [[1], [2]] r4s.1 (.ok (splitEff r4s.1 0 [[1], [2]])) ∧
    (∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
      Repr π4.tok π4.ptok r4d.2.1 π4.L r4d.1 r4d.2.2) ∧
    ∀ r r', KLf.DeclaredDisjoint r r' → (∀ l ∈ r, l < r4d.1.P.length ∧ isLeaf r4d.1.P l) →
      (∀ l ∈ r', l < r4d.1.P.length ∧ isLeaf r4d.1.P l) → ByteDisjoint π4.L r r' := by
  obtain ⟨os, hok, -, hR, -⟩ := sim_of (k := KLf) (statics := []) (P := P4) (z := [])
    (ops := r4 ++ [.split 0 [[1], [2]]]) KLf_dd (by decide) (by decide) (by decide) (by decide)
  exact ⟨KLf_dd, by decide, .reject (by decide), by decide, .ok (by decide), ⟨os, hok, hR⟩,
    fun r r' hd hr hr' => byteDisjoint_of_leaves hR.lwf hr hr' hd⟩

/-! ## Run R5: pointers to empty regions (H15, écart connu) -/

/-- R5: frame 1 with the arena value 0, the allocator 1, the leaves 2, 3, 4; storage 5 with the
leaf 6, owned by 0, `internal` 5; `issue []` to 2; `split` of the root of 3 into `[[]]`, then
`store` of that empty authority 7 into 4. -/
def r5 : List Op3 := [.enter [] [lf, lf, lf, lf, lf], .write 1 [1] w,
  .alloc 1 0 [lf, (some 5, none, 0)], .write 0 [0] w, .newArena 5 5, .issue 0 0 [] 2,
  .split 3 [[]], .store 7 4]
def P5 : List Place := (Ern.MM03.Horrors.run K0 [] (r5.map toOp)).s.P
def π5 : Params := piOf P5 []
def r5f : SSt := sst K0 [] π5 r5

/-- Base address of the allocation `i` in `s2`. -/
def baseOf (s2 : MM02.State) (i : Nat) : Nat := ((s2.allocs i).map (·.base)).getD 0

/-- Address decoded from the range of the leaf `l` (L6, the encoding of the run). -/
def decodedAt (s2 : MM02.State) (L : Layout) (l : Nat) : Nat := CaseSim.pe.decode (bytesOf s2 L l)

/-- **MM23-H15**, écart connu (material §0, rule 8; decision 2 of jalon 2 not applied). Expected: the
pointer to an empty region has as address the base of the allocation of its effective anchor and
as provenance that allocation. Obtained in a translated run: `issue []` writes the address 0, with
the provenance of the storage of the arena (the allocation of the anchor `internal` 5); the `store`
of an empty region split from the root of 3 writes the address 0 without provenance. The bases of
those allocations are not 0. Not presented as passed. -/
theorem H15 : (∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
      Repr π5.tok π5.ptok r5f.2.1 π5.L r5f.1 r5f.2.2) ∧
    decodedAt r5f.2.2 π5.L 2 = 0 ∧ (bytesOf r5f.2.2 π5.L 2 0).2 = some (π5.L 5).alloc ∧
    baseOf r5f.2.2 (π5.L 5).alloc ≠ 0 ∧
    decodedAt r5f.2.2 π5.L 4 = 0 ∧ (bytesOf r5f.2.2 π5.L 4 0).2 = none ∧
    baseOf r5f.2.2 (π5.L 3).alloc ≠ 0 :=
  ⟨(sim_of (P := P5) (z := []) (KT_dd _ _ _ _ _) (by decide) (by decide) (by decide)
    (by decide)).imp fun _ h => ⟨h.1, h.2.2.1⟩, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

/-! ## Run R6: a region whose head has not the lowest offset (H16, écart connu) -/

/-- R6: frame 1 with the arena value 0, the allocator 1, the leaf 2; storage 3 with the leaves 4
(offset 0) and 5 (offset 8); `issue [5, 4]` to 2. -/
def r6 : List Op3 := [.enter [] [lf, lf, lf], .write 1 [1] w,
  .alloc 1 0 [lf, (some 3, none, 0), (some 3, none, 0)], .write 0 [0] w, .newArena 3 3,
  .issue 0 0 [5, 4] 2]
def P6 : List Place := (Ern.MM03.Horrors.run K0 [] (r6.map toOp)).s.P
def π6 : Params := piOf P6 []
def r6f : SSt := sst K0 [] π6 r6

/-- **MM23-H16**, écart connu (material §0, rule 8; decision 3 of jalon 2 not applied). Expected: the
pointer to the region `[5, 4]` has the lowest address of its non-empty leaves, that of 4. Obtained
in a translated run: the address of the head 5, 8 bytes above. Not presented as passed. -/
theorem H16 : (∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
      Repr π6.tok π6.ptok r6f.2.1 π6.L r6f.1 r6f.2.2) ∧
    (π6.L 4).off = 0 ∧ (π6.L 5).off = 8 ∧
    decodedAt r6f.2.2 π6.L 2 = baseOf r6f.2.2 (π6.L 3).alloc + 8 ∧
    decodedAt r6f.2.2 π6.L 2 ≠ baseOf r6f.2.2 (π6.L 3).alloc :=
  ⟨(sim_of (P := P6) (z := []) (KT_dd _ _ _ _ _) (by decide) (by decide) (by decide)
    (by decide)).imp fun _ h => ⟨h.1, h.2.2.1⟩, by decide, by decide, by decide, by decide⟩

/-! ## Run R7 and `fail`: `alloc` of size zero and failed (H07) -/

/-- R7: frame 1 with the allocator 0 and `x` (1), written; the storage 2 allocated for `x`, laid out
with size zero (K1 (d), D2: a shape of one leaf). -/
def r7 : List Op3 := [.enter [] [lf, lf], .write 0 [0] w, .write 1 [1] w, .alloc 0 1 [lf]]
def P7 : List Place := (Ern.MM03.Horrors.run K0 [] (r7.map toOp)).s.P
def π7 : Params := piOf P7 [2]
def r7a : SSt := sst K0 [] π7 (r7.take 3)

instance : ∀ r r', Decidable (KNS.DeclaredDisjoint r r') := fun _ _ => instDecidableFalse
instance : DecidablePred KNS.Pinned := fun l => inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : DecidablePred KNS.ExternalDone := fun l =>
  inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : DecidablePred KNS.Deallocable := fun l =>
  inferInstanceAs (Decidable (l ∈ ([] : List Nat)))
instance : ∀ p a, Decidable (KNS.FreeCompat p a) := fun p a =>
  inferInstanceAs (Decidable ((p, a) ∈ ([] : List (Nat × Nat))))

/-- The prefix of R7 reached under the contracts `KNS`, where no allocation is satisfiable. -/
def r7n : Ern.HandlePool.PS := Ern.MM03.Horrors.run KNS [] ((r7.take 3).map toOp)

/-- **MM23-H07** (passe 1). `alloc` `ok`: one allocation of MM-02, `ok` (R1, `H07_ok`); of size zero:
one allocation of size 0, `ok` (`step_ok_of`) in a translated run; `fail` (`K.Satisfiable` false,
`KNS`, on a state reached under `KNS`): the state is unchanged, and there is no labelled step
(`Step3` asks the outcome `ok`), so the translation has no step and no MM-02 operation. Expected:
`AllocStep` / no step / `AllocStep` of size 0; obtained: the same. -/
theorem H07 : (∃ os, AllOk Ceq CaseSim.obR CaseSim.obW MM02.State.empty os ∧
      exec MM02.State.empty os = (sst K0 [] π7 r7).2.2) ∧
    (assoc π7 (.alloc 0 1 [lf]) r7a.1 r7a.2.2).map opAllocSize = [some 0] ∧
    AllOk Ceq CaseSim.obR CaseSim.obW r7a.2.2 (assoc π7 (.alloc 0 1 [lf]) r7a.1 r7a.2.2) ∧
    Ern.HandlePool.PReach KNS [] r7n ∧ AllocStep KNS 0 1 [lf] r7n.s (.fail r7n.s) ∧
    ∀ s', ¬ Step3 KNS (.alloc 0 1 [lf]) r7n.s s' :=
  ⟨(sim_of (P := P7) (z := [2]) (KT_dd _ _ _ _ _) (by decide) (by decide) (by decide)
    (by decide)).imp fun _ h => ⟨h.1, h.2.1⟩, by decide,
    step_ok_of (k := K0) (statics := []) (P := P7) (z := [2]) (ops := r7.take 3)
      (op := .alloc 0 1 [lf]) (KT_dd [] [] [] [] [])
      (by decide) (by decide) (by decide) (by decide),
    Ern.MM03.Horrors.run_reach (by decide) (by decide), .fail (by decide) (fun h => h),
    fun _ hs => nomatch alloc_det hs.2 (AllocStep.fail (by decide) (fun h => h))⟩

end Ern.MM23.Horrors
