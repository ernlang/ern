import Ern.Derived.Arena
import Ern.MM23

/-!
# DataStack, a library instance over the kernel (derivability pass 0.1, question 2)

A stack administers a storage through an authority `internal` held by the stack value, as an arena
does (candidate Spec 1 §36, §46), with library metadata: the ordered leaves of the storage, the
top, the issued blocks and the live marks. Its operations are built on kernel steps and on the
derived `issue` and `reset` of question 1 (`Ern.Derived.Arena`):

* `push`: the restricted `issue` at the top, its static clauses (§77.1, §77.2) checked before the
  room, realised by `split` of `internal` on the cells then `store` of the block into the
  destination; `fail` when no room is left;
* `mark`: a mark (stack, fresh identifier, top), metadata only;
* `rewind`: the derived `reset` on the cells above the mark, `split` of `internal` on them then
  `release` of the derived authority; `fail` for a mark that is not live in the stack;
* `grow`: in place, `release` of the last block, then the derived `issue` of a region of the same
  base and of larger size into the same destination, which is `Init`; `fail` when no room is left.

Every `ok` step of the library takes kernel steps of `Reachable` only (`dexec_reach`). The theorems
of the brief are `rewind_rejects_live_above`, `mark_no_aba` (with `rewind_removes`),
`rewind_keeps_older_marks`,
`grow_same_base`, `grow_keeps_prefix_init` and `grow_keeps_prefix_bytes` (through the refinement
`Ern.MM23`, unchanged). The decisions the brief does not settle are listed in the report
(`formal/reports/Derivability_v0.1.md`, (c) and (f)).
-/

namespace Ern.Lib.DataStack

open Ern.MM03 Ern.HandlePool Ern.MM03.Horrors Ern.Derived.Arena

/-- A block issued by a stack: base and size in the cells of the stack, authority, destination. -/
structure Blk where
  base : Nat
  size : Nat
  auth : Nat
  dst : Nat
deriving DecidableEq, Repr

/-- A mark (brief: "(pile, identifiant frais, sommet)"). -/
structure Mark where
  stack : Nat
  id : Nat
  top : Nat
deriving DecidableEq, Repr

/-- A stack (brief: "stockage, `internal`, sommet, liste ordonnée des marques vivantes"); `cells`
are the ordered leaves of the storage, its footprint at creation; `blocks` the issued blocks,
oldest first. The stack value is the holder of `internal`. -/
structure Stack where
  storage : Nat
  internal : Nat
  cells : List Nat
  top : Nat
  blocks : List Blk
  marks : List Mark
deriving DecidableEq, Repr

/-- State of the library: the kernel state, the stacks (the identity of a stack is its index) and
the next fresh mark identifier. -/
structure DS where
  s : S3
  stacks : List Stack
  fresh : Nat

/-- Outcome of a library operation; `fail` leaves the state unchanged (§58). -/
inductive Out where
  | ok (d : DS)
  | fail
  | reject

/-- The `n` cells of the stack from the index `b`. -/
def cellsOf (st : Stack) (b n : Nat) : List Nat := (st.cells.drop b).take n

/-- The cells above the mark `m`, from its top to the current top: those that `rewind m` returns
to the available part (brief: "les régions au-dessus de `m`"). A region issued after `m` and still
below the top lies there, but not every such region does: a block grown after `m` from a base below
`m` starts below it, and a region issued after `m` and returned by an intermediate `rewind` lies
above the current top (`case_rewind_reading`; report, (f)). -/
def above (st : Stack) (m : Mark) : List Nat := cellsOf st m.top (st.top - m.top)

/-- The stack seen as an administration of its storage, for `MetaRightM` and `blockOf`. -/
def Stack.arena (st : Stack) : Arena := ⟨st.storage, st.internal, [], []⟩

/-- No active authority is held by the destination (O8.2, §77.2). -/
def NoHeld (s : S3) (dst : Nat) : Prop :=
  ∀ j ∈ List.range s.A.length, OptP (s.A[j]?) (fun z => z.active = true → z.holder ≠ .place dst) True

instance (s : S3) (dst : Nat) : Decidable (NoHeld s dst) := by unfold NoHeld; infer_instance

/-- Static preconditions of `push` of the cells `r`, checked before the room (§58, §77.4), those of
the restricted `issue` (`IssueStaticR`, §77.1 and §77.2): the stack is live, the current frame has
exercisable `Modify` on the stack value (`MetaRightM`), and the destination is a usable leaf under
exercisable `Modify`, not `Init`, holding no active authority and outside `r`. The inclusion of the
region in the storage is the room. -/
def PushStatic (s : S3) (st : Stack) (r : List Nat) (dst : Nat) : Prop :=
  s.Active st.internal ∧ MetaRightM s st.arena ∧ s.Usable dst ∧ isLeaf s.P dst ∧
    HasRight s .modify dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ NoHeld s dst ∧ dst ∉ r

instance (s : S3) (st : Stack) (r : List Nat) (dst : Nat) : Decidable (PushStatic s st r dst) := by
  unfold PushStatic; infer_instance

/-- The derived `issue` (question 1, `issue_as_kernel_split`): `split` of `internal` on `r`, then
`store` of the block into `dst`. -/
def IssueSeq (k : K) (s : S3) (st : Stack) (r : List Nat) (dst : Nat) : Prop :=
  SplitPre k s st.internal [r] ∧ StorePre (s.addAuth (blockOf s st.arena r)) s.A.length dst

instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (s : S3) (st : Stack)
    (r : List Nat) (dst : Nat) : Decidable (IssueSeq k s st r dst) := by
  unfold IssueSeq; infer_instance

/-- Arrival state of the derived `issue`. -/
def issueSeqEff (s : S3) (st : Stack) (r : List Nat) (dst : Nat) : S3 :=
  storeEff (s.addAuth (blockOf s st.arena r)) s.A.length dst

/-- The derived `reset` on the cells above `m` (question 1, `reset_as_kernel`): `split` of
`internal` on them, then `release` of the derived authority. -/
def RewindSeq (k : K) (s : S3) (st : Stack) (m : Mark) : Prop :=
  SplitPre k s st.internal [above st m] ∧
    ReleasePre (s.addAuth (blockOf s st.arena (above st m))) s.A.length

instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (s : S3) (st : Stack) (m : Mark) :
    Decidable (RewindSeq k s st m) := by
  unfold RewindSeq; infer_instance

/-- The guard of §56 for `internal` `i`: no live arena and no live stack already uses it. -/
def Guard56 (d : DS) (i : Nat) : Prop :=
  (∀ ar ∈ d.s.arenas, d.s.Active ar.internal → ar.internal ≠ i) ∧
    ∀ x ∈ d.stacks, d.s.Active x.internal → x.internal ≠ i

instance (d : DS) (i : Nat) : Decidable (Guard56 d i) := by unfold Guard56; infer_instance

section Ops
variable (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- Creation of a stack on `storage` administered by `internal` (as O17, §76): the preconditions of
`newArena` and the guard of §56 on both registries, arenas and stacks. -/
def newStack (d : DS) (storage i : Nat) : Out :=
  if NewArenaPreNG d.s storage i ∧ Guard56 d i then
    .ok { d with stacks := d.stacks ++ [⟨storage, i, footprint d.s.P storage, 0, [], []⟩] }
  else .reject

/-- `push size dst` on the stack `j` (brief: "émission au sommet (`issue` restreint)"): the static
clauses of the restricted `issue` (`PushStatic`), then `fail` when fewer than `size` cells are left,
then the derived `issue` of the `size` cells at the top into `dst`. By `issue_as_kernel_split`, this
realisation through kernel steps differs from the restricted `issue` only by clause 5 of `store`
(O8.5), which it inherits. `size` may be zero: the block then has an empty footprint, as the
restricted `issue` of the empty region (`ce_empty_region`), and it blocks no `rewind`. -/
def push (d : DS) (j size dst : Nat) : Out :=
  match d.stacks[j]? with
  | none => .reject
  | some st =>
    if PushStatic d.s st (cellsOf st st.top size) dst then
      if st.top + size ≤ st.cells.length then
        if IssueSeq k d.s st (cellsOf st st.top size) dst then
          .ok { d with
            s := issueSeqEff d.s st (cellsOf st st.top size) dst
            stacks := d.stacks.set j
              { st with
                top := st.top + size
                blocks := st.blocks ++ [⟨st.top, size, d.s.A.length, dst⟩] } }
        else .reject
      else .fail
    else .reject

/-- `mark` on the stack `j` (brief): `ok`, a mark (stack, fresh identifier, top) appended to the
live marks. -/
def mark (d : DS) (j : Nat) : Out :=
  match d.stacks[j]? with
  | none => .reject
  | some st => .ok { d with
      stacks := d.stacks.set j { st with marks := st.marks ++ [⟨j, d.fresh, st.top⟩] }
      fresh := d.fresh + 1 }

/-- `rewind m` on the stack `j` (brief): `fail` when `m` is not a live mark of the stack; then the
derived `reset` on the cells above `m`, `split` of `internal` on them and `release`, which rejects
when an active authority derived from `internal` covers one of them (`rewind_rejects_live_above`)
and also when the current frame cannot exercise `internal` at `Modify` (O2.1, the restricted
`MetaRight` of §78.1); `ok`: the top returns to the top of `m`, the blocks whose base is above it
are forgotten, `m` and the later marks are removed, the older marks stay (`rewind_removes`). A stack
that does not exist rejects (no stack value). -/
def rewind (d : DS) (j : Nat) (m : Mark) : Out :=
  match d.stacks[j]? with
  | none => .reject
  | some st =>
    if m ∈ st.marks then
      if RewindSeq k d.s st m then
        .ok { d with
          s := releaseEff (d.s.addAuth (blockOf d.s st.arena (above st m))) d.s.A.length
          stacks := d.stacks.set j
            { st with
              top := m.top
              blocks := st.blocks.filter (·.base < m.top)
              marks := st.marks.takeWhile (· ≠ m) } }
      else .reject
    else .fail

/-- `grow b extra` on the stack `j` (brief: in place only). Static clauses, checked before the room
(§58): `b` is the authority of the last block, at the top, `extra` is positive ("taille plus
grande"), `b` can be released, the stack is live and the current frame has exercisable `Modify` on
the stack value (`MetaRightM`). `fail` when fewer than `extra` cells follow the block; otherwise
`release` of `b`, then the derived `issue` of the region of the same base and of size `size + extra`
into the destination recorded for the block. That destination is `Init` (the first `store` wrote
it): the derived `issue` accepts it (O8.2), the restricted `issue` would not (§77.2, report (c)). -/
def grow (d : DS) (j b extra : Nat) : Out :=
  match d.stacks[j]? with
  | none => .reject
  | some st =>
    match st.blocks.getLast? with
    | none => .reject
    | some x =>
      if 0 < extra ∧ x.auth = b ∧ x.base + x.size = st.top ∧ ReleasePre d.s b ∧
          d.s.Active st.internal ∧ MetaRightM d.s st.arena then
        if x.base + x.size + extra ≤ st.cells.length then
          if IssueSeq k (releaseEff d.s b) st (cellsOf st x.base (x.size + extra)) x.dst then
            .ok { d with
              s := issueSeqEff (releaseEff d.s b) st (cellsOf st x.base (x.size + extra)) x.dst
              stacks := d.stacks.set j
                { st with
                  top := x.base + x.size + extra
                  blocks := st.blocks.dropLast ++ [⟨x.base, x.size + extra, d.s.A.length, x.dst⟩] } }
          else .reject
        else .fail
      else .reject

/-- Operations of a run of the library: a kernel or arena step, or a stack operation. -/
inductive DOp where
  | kernel (o : Op)
  | newStack (storage i : Nat)
  | push (j size dst : Nat)
  | mark (j : Nat)
  | rewind (j : Nat) (m : Mark)
  | grow (j b extra : Nat)

/-- The guard of §56 that a kernel `newArena` adds in the library: the registry of the stacks. -/
def KGuard (d : DS) : Op → Prop
  | .newArena _ i => ∀ x ∈ d.stacks, d.s.Active x.internal → x.internal ≠ i
  | _ => True

instance (d : DS) (o : Op) : Decidable (KGuard d o) := by
  cases o <;> unfold KGuard <;> infer_instance

/-- A step of the library. A kernel `newArena` also consults the registry of the stacks (§56). -/
def dexec (d : DS) : DOp → Out
  | .kernel o =>
    if KGuard d o then
      match kexec k d.s o with
      | some s' => .ok { d with s := s' }
      | none => .reject
    else .reject
  | .newStack st i => DataStack.newStack d st i
  | .push j size dst => DataStack.push k d j size dst
  | .mark j => DataStack.mark d j
  | .rewind j m => DataStack.rewind k d j m
  | .grow j b extra => DataStack.grow k d j b extra

/-- A run of the library: `some` of the final state when every step is `ok`. -/
def drun (d : DS) : List DOp → Option DS
  | [] => some d
  | o :: os =>
    match dexec k d o with
    | .ok d' => drun d' os
    | _ => none

end Ops

/-- The initial state of the library. -/
def DS.init : DS := ⟨S3.init [], [], 0⟩

/-! ## Inversion of the `ok` steps -/

section Inv
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')]

theorem newStack_ok {d d' : DS} {st i : Nat} (h : newStack d st i = .ok d') :
    NewArenaPreNG d.s st i ∧ Guard56 d i ∧
      d' = { d with stacks := d.stacks ++ [⟨st, i, footprint d.s.P st, 0, [], []⟩] } := by
  unfold newStack at h
  split at h
  · rename_i hp; cases h; exact ⟨hp.1, hp.2, rfl⟩
  · cases h

theorem push_ok {d d' : DS} {j size dst : Nat} (h : push k d j size dst = .ok d') :
    ∃ st, d.stacks[j]? = some st ∧ PushStatic d.s st (cellsOf st st.top size) dst ∧
      st.top + size ≤ st.cells.length ∧
      IssueSeq k d.s st (cellsOf st st.top size) dst ∧
      d' = { d with
        s := issueSeqEff d.s st (cellsOf st st.top size) dst
        stacks := d.stacks.set j
          { st with
            top := st.top + size
            blocks := st.blocks ++ [⟨st.top, size, d.s.A.length, dst⟩] } } := by
  unfold push at h
  split at h
  · cases h
  · rename_i st hst
    split at h
    · split at h
      · split at h
        · cases h; exact ⟨st, hst, by assumption, by assumption, by assumption, rfl⟩
        · cases h
      · cases h
    · cases h

theorem mark_ok {d d' : DS} {j : Nat} (h : mark d j = .ok d') :
    ∃ st, d.stacks[j]? = some st ∧
      d' = { d with
        stacks := d.stacks.set j { st with marks := st.marks ++ [⟨j, d.fresh, st.top⟩] }
        fresh := d.fresh + 1 } := by
  unfold mark at h
  split at h
  · cases h
  · rename_i st hst; cases h; exact ⟨st, hst, rfl⟩

theorem rewind_ok {d d' : DS} {j : Nat} {m : Mark} (h : rewind k d j m = .ok d') :
    ∃ st, d.stacks[j]? = some st ∧ m ∈ st.marks ∧ RewindSeq k d.s st m ∧
      d' = { d with
        s := releaseEff (d.s.addAuth (blockOf d.s st.arena (above st m))) d.s.A.length
        stacks := d.stacks.set j
          { st with
            top := m.top
            blocks := st.blocks.filter (·.base < m.top)
            marks := st.marks.takeWhile (· ≠ m) } } := by
  unfold rewind at h
  split at h
  · cases h
  · rename_i st hst
    split at h
    · split at h
      · cases h; exact ⟨st, hst, by assumption, by assumption, rfl⟩
      · cases h
    · cases h

theorem grow_ok {d d' : DS} {j b extra : Nat} (h : grow k d j b extra = .ok d') :
    ∃ st x, d.stacks[j]? = some st ∧ st.blocks.getLast? = some x ∧ 0 < extra ∧ x.auth = b ∧
      x.base + x.size = st.top ∧ ReleasePre d.s b ∧
      (d.s.Active st.internal ∧ MetaRightM d.s st.arena) ∧ x.base + x.size + extra ≤ st.cells.length ∧
      IssueSeq k (releaseEff d.s b) st (cellsOf st x.base (x.size + extra)) x.dst ∧
      d' = { d with
        s := issueSeqEff (releaseEff d.s b) st (cellsOf st x.base (x.size + extra)) x.dst
        stacks := d.stacks.set j
          { st with
            top := x.base + x.size + extra
            blocks := st.blocks.dropLast ++ [⟨x.base, x.size + extra, d.s.A.length, x.dst⟩] } } := by
  unfold grow at h
  split at h
  · cases h
  · rename_i st hst
    split at h
    · cases h
    · rename_i x hx
      split at h
      · rename_i hc
        split at h
        · split at h
          · cases h
            exact ⟨st, x, hst, hx, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2, by assumption,
              by assumption, rfl⟩
          · cases h
        · cases h
      · cases h

/-! ## The kernel part of the library is reached -/

theorem releaseEff_len (s : S3) (a : Nat) : (releaseEff s a).A.length = s.A.length := by
  unfold releaseEff; split <;> simp

theorem releaseEff_I (s : S3) (a : Nat) : (releaseEff s a).I = s.I := by
  unfold releaseEff; split <;> rfl

theorem releaseEff_P (s : S3) (a : Nat) : (releaseEff s a).P = s.P := by
  unfold releaseEff; split <;> rfl

omit [∀ r r', Decidable (k.DeclaredDisjoint r r')] in
/-- The derived `issue` is a `split` step then a `store` step of `Reachable` (O2, O8). -/
theorem issueSeq_reach {statics : Statics} {s : S3} {st : Stack} {r : List Nat} {dst : Nat}
    (hr : Reachable k statics s) (h : IssueSeq k s st r dst) :
    Reachable k statics (s.addAuth (blockOf s st.arena r)) ∧
      Reachable k statics (issueSeqEff s st r dst) := by
  have h1 : Reachable k statics (s.addAuth (blockOf s st.arena r)) :=
    .split hr (rs := [r]) (src := st.internal) (.ok h.1)
  exact ⟨h1, .store h1 (.ok h.2)⟩

end Inv

section InvK
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

theorem dexec_kernel {d d' : DS} {o : Op} (h : dexec k d (.kernel o) = .ok d') :
    kexec k d.s o = some d'.s ∧ d'.stacks = d.stacks ∧ d'.fresh = d.fresh := by
  simp only [dexec] at h
  split at h
  · split at h
    · rename_i hs; cases h; exact ⟨hs, rfl, rfl⟩
    · cases h
  · cases h

/-- Every `ok` step of the library takes kernel steps of `Reachable` only. -/
theorem dexec_reach {statics : Statics} {d d' : DS} {o : DOp} (hr : Reachable k statics d.s)
    (h : dexec k d o = .ok d') : Reachable k statics d'.s := by
  cases o with
  | kernel o => exact reachable_step hr (kexec_step (dexec_kernel h).1)
  | newStack st i => obtain ⟨-, -, rfl⟩ := newStack_ok h; exact hr
  | push j size dst =>
    obtain ⟨st, -, -, -, hseq, rfl⟩ := push_ok h; exact (issueSeq_reach hr hseq).2
  | mark j => obtain ⟨st, -, rfl⟩ := mark_ok h; exact hr
  | rewind j m =>
    obtain ⟨st, -, -, ⟨hsp, hrel⟩, rfl⟩ := rewind_ok h
    have h1 : Reachable k statics (d.s.addAuth (blockOf d.s st.arena (above st m))) :=
      .split hr (rs := [above st m]) (src := st.internal) (.ok hsp)
    exact .release h1 (.ok hrel)
  | grow j b extra =>
    obtain ⟨st, x, -, -, -, -, -, hrel, -, -, hseq, rfl⟩ := grow_ok h
    exact (issueSeq_reach (.release hr (.ok hrel)) hseq).2

theorem drun_reach {statics : Statics} : ∀ {d d' : DS} {os : List DOp},
    Reachable k statics d.s → drun k d os = some d' → Reachable k statics d'.s
  | d, d', [], hr, h => by simp only [drun, Option.some.injEq] at h; subst h; exact hr
  | d, d', o :: os, hr, h => by
    simp only [drun] at h
    split at h
    · rename_i d₁ h₁; exact drun_reach (dexec_reach hr h₁) h
    · cases h

end InvK

/-! ## Theorems of the brief -/

/-- An active descendant of `a` covering `l`, whatever its mode, takes the effective `Modify` of `a`
on `l` away (§43, cases 3 and 4). -/
theorem effective_ne_modify_of_active_desc {s : S3} {a j l : Nat} {y : Authority}
    (hy : s.A[j]? = some y) (ya : y.active = true) (hl : l ∈ y.footprint) (hj : a ∈ s.ancs j) :
    effective s a l ≠ some .modify := by
  intro he
  obtain ⟨x, -, -, -, hx⟩ := effective_some he
  have hmem : y.mode ∈ descModes s a l := mem_descModes.2 ⟨j, y, hy, ya, hl, hj, rfl⟩
  rcases effOf_cases hx with ⟨h0, -⟩ | ⟨-, -, h1⟩
  · rw [h0] at hmem; simp at hmem
  · cases h1

theorem getElem?_set_cases {α : Type} {l : List α} {j i : Nat} {v x : α}
    (h : (l.set j v)[i]? = some x) : (i = j ∧ x = v) ∨ (i ≠ j ∧ l[i]? = some x) := by
  rw [List.getElem?_set] at h
  by_cases hij : j = i
  · subst hij; simp only [↓reduceIte] at h; split at h
    · cases h; exact .inl ⟨rfl, rfl⟩
    · cases h
  · simp only [hij, ↓reduceIte] at h; exact .inr ⟨Ne.symm hij, h⟩

theorem getElem?_append_single {α : Type} {l : List α} {x y : α} {i : Nat}
    (h : (l ++ [x])[i]? = some y) : l[i]? = some y ∨ (i = l.length ∧ y = x) := by
  rw [List.getElem?_append] at h
  split at h
  · exact .inl h
  · rename_i hi
    have : i - l.length = 0 := by
      cases hc : i - l.length with
      | zero => rfl
      | succ n => rw [hc] at h; simp at h
    rw [this] at h; simp at h
    exact .inr ⟨by omega, h.symm⟩

theorem not_mem_takeWhile_ne {m : Mark} : ∀ l : List Mark, m ∉ l.takeWhile (· ≠ m)
  | [] => by simp
  | a :: l => by
    rw [List.takeWhile_cons]
    split
    · rename_i ha
      intro hm
      rcases List.mem_cons.1 hm with rfl | hm
      · simp at ha
      · exact not_mem_takeWhile_ne l hm
    · simp

theorem takeWhile_ne_append {m : Mark} : ∀ {pre : List Mark} (post : List Mark), m ∉ pre →
    (pre ++ m :: post).takeWhile (· ≠ m) = pre
  | [], post, _ => by simp
  | a :: pre, post, h => by
    have ha : a ≠ m := fun e => h (e ▸ List.mem_cons_self ..)
    have ih := takeWhile_ne_append (pre := pre) post (fun h' => h (List.mem_cons_of_mem _ h'))
    have ha' : decide (a ≠ m) = true := by simpa using ha
    rw [List.cons_append, List.takeWhile_cons]; simp only [ha', ↓reduceIte, ih]

theorem take_prefix_take_add {α : Type} : ∀ (l : List α) (n e : Nat), l.take n <+: l.take (n + e)
  | [], n, e => ⟨[], by rw [List.take_nil, List.take_nil]; rfl⟩
  | _ :: _, 0, _ => ⟨_, List.nil_append _⟩
  | a :: l, n + 1, e => by
    obtain ⟨t, ht⟩ := take_prefix_take_add l n e
    exact ⟨t, by rw [Nat.add_right_comm, List.take_succ_cons, List.take_succ_cons, List.cons_append, ht]⟩

theorem cellsOf_prefix (st : Stack) (b n e : Nat) : cellsOf st b n <+: cellsOf st b (n + e) :=
  take_prefix_take_add _ _ _

section Thms
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')]

/-- `rewind_rejects_live_above` (brief): `rewind m` of a live mark is rejected when an active
authority derived from `internal` covers a cell above `m` (`above`, the cells that the rewind
returns): its effective `Modify` on that cell is gone, so `split` of `internal` on the cells above
`m` is rejected (O2.1). The brief's "couvre une région émise après `m`" is read on the cells that the
rewind returns (`above`; report, (f)). -/
theorem rewind_rejects_live_above {d : DS} {j : Nat} {st : Stack} {m : Mark}
    (hst : d.stacks[j]? = some st) (hm : m ∈ st.marks) {x l : Nat} {y : Authority}
    (hy : d.s.A[x]? = some y) (ya : y.active = true) (hx : st.internal ∈ d.s.ancs x)
    (hly : l ∈ y.footprint) (hl : l ∈ above st m) : rewind k d j m = .reject := by
  have hn : ¬ RewindSeq k d.s st m := fun h =>
    effective_ne_modify_of_active_desc hy ya hly hx (h.1.2.2.1 _ (List.mem_singleton_self _) l hl)
  simp [rewind, hst, hm, hn]

/-- `rewind_rejects_live_above` read on an `ok` (its contrapositive): an `ok` of `rewind m` is the
rewind of a live mark of the stack above which no active authority derived from `internal` covers a
cell. The converse of `rewind_rejects_live_above` does not hold: `rewind` also rejects when the
current frame cannot exercise `internal` (see `rewind`). -/
theorem rewind_ok_no_live_above {d d' : DS} {j : Nat} {m : Mark} (h : rewind k d j m = .ok d') :
    ∃ st, d.stacks[j]? = some st ∧ m ∈ st.marks ∧
      ∀ (x : Nat) (y : Authority), d.s.A[x]? = some y → y.active = true →
        st.internal ∈ d.s.ancs x → ∀ l ∈ y.footprint, l ∉ above st m := by
  obtain ⟨st, hst, hm, hseq, -⟩ := rewind_ok h
  exact ⟨st, hst, hm, fun x y hy ya hx l hly hl => effective_ne_modify_of_active_desc hy ya hly hx
    (hseq.1.2.2.1 _ (List.mem_singleton_self _) l hl)⟩

/-- `rewind_keeps_older_marks` (brief): after `rewind m`, the marks of the stack are those older than
`m`, `m` and the later marks are removed, the top is the top of `m` (the cells above return to the
available part), the other stacks are unchanged and no initialisation changes. -/
theorem rewind_keeps_older_marks {d d' : DS} {j : Nat} {m : Mark} (h : rewind k d j m = .ok d')
    {st : Stack} (hst : d.stacks[j]? = some st) {pre post : List Mark}
    (hs : st.marks = pre ++ m :: post) (hpre : m ∉ pre) :
    (∃ st', d'.stacks[j]? = some st' ∧ st'.marks = pre ∧ st'.top = m.top) ∧
      (∀ i, i ≠ j → d'.stacks[i]? = d.stacks[i]?) ∧ d'.s.I = d.s.I := by
  obtain ⟨st₀, hst₀, -, -, rfl⟩ := rewind_ok h
  rw [hst] at hst₀; cases hst₀
  have hj : j < d.stacks.length := lt_of_getElem? hst
  refine ⟨⟨_, List.getElem?_set_self hj, ?_, rfl⟩, fun i hi => List.getElem?_set_ne (Ne.symm hi),
    ?_⟩
  · simp only; rw [hs]; exact takeWhile_ne_append post hpre
  · show (releaseEff _ _).I = _; rw [releaseEff_I]; rfl

/-- The blocks of the arrival state of `grow`: the authority of the new block is at the index
`d.s.A.length`, the release keeping the length of `A`. -/
theorem grow_new_auth {s : S3} {st : Stack} {r : List Nat} {b dst : Nat} :
    (issueSeqEff (releaseEff s b) st r dst).afp s.A.length = r := by
  have hy₀ := addAuth_self (releaseEff s b) (blockOf (releaseEff s b) st.arena r)
  unfold issueSeqEff
  rw [storeEff_eq hy₀, releaseEff_len]
  simp only [S3.afp]
  rw [List.getElem?_set_self (by simp [S3.addAuth, releaseEff_len])]
  rfl

/-- `grow_same_base` (brief): the `ok` of `grow b extra` releases `b`, the last block (inactive in
the arrival state), and gives the stack a last block of the same base, of size `size + extra`, with
the same recorded destination; its authority covers the cells from the same base and is held by that
destination; the old cells are a prefix of the new ones. -/
theorem grow_same_base {d d' : DS} {j b extra : Nat} (h : grow k d j b extra = .ok d') :
    ∃ st x st', d.stacks[j]? = some st ∧ st.blocks.getLast? = some x ∧ x.auth = b ∧ 0 < extra ∧
      d'.stacks[j]? = some st' ∧
      st'.blocks.getLast? = some ⟨x.base, x.size + extra, d.s.A.length, x.dst⟩ ∧
      d'.s.afp d.s.A.length = cellsOf st x.base (x.size + extra) ∧
      d'.s.A[d.s.A.length]?.map (·.holder) = some (.place x.dst) ∧
      cellsOf st x.base x.size <+: cellsOf st x.base (x.size + extra) ∧
      d'.s.A[b]?.map (·.active) = some false := by
  obtain ⟨st, x, hst, hx, hex, hb, -, hrel, -, -, -, rfl⟩ := grow_ok h
  have hj : j < d.stacks.length := lt_of_getElem? hst
  have hy₀ := addAuth_self (releaseEff d.s b)
    (blockOf (releaseEff d.s b) st.arena (cellsOf st x.base (x.size + extra)))
  refine ⟨st, x, _, hst, hx, hb, hex, List.getElem?_set_self hj, by simp, grow_new_auth, ?_,
    cellsOf_prefix st _ _ _, ?_⟩
  · show (issueSeqEff _ _ _ _).A[d.s.A.length]?.map _ = _
    unfold issueSeqEff; rw [storeEff_eq hy₀]; simp only
    rw [← releaseEff_len d.s b, List.getElem?_set_self (by simp [S3.addAuth])]; rfl
  · obtain ⟨⟨y, hy, -⟩, -⟩ := hrel
    have hbl : b < d.s.A.length := lt_of_getElem? hy
    show (issueSeqEff _ _ _ _).A[b]?.map _ = _
    unfold issueSeqEff; rw [storeEff_eq hy₀]; simp only
    rw [List.getElem?_set_ne (by rw [releaseEff_len]; omega),
      addAuth_lt (by rw [releaseEff_len]; exact hbl), releaseEff_eq hy, List.getElem?_set_self hbl]
    rfl

/-- `grow_keeps_prefix_init` (brief): `grow` changes the initialisation of no cell of the old block:
`release` and `split` change no initialisation, and `store` initialises only the destination, which
the new block does not cover (O8.3). -/
theorem grow_keeps_prefix_init {d d' : DS} {j b extra : Nat} (h : grow k d j b extra = .ok d')
    {st : Stack} {x : Blk} (hst : d.stacks[j]? = some st) (hx : st.blocks.getLast? = some x) :
    ∀ l ∈ cellsOf st x.base x.size, d'.s.I l = d.s.I l := by
  obtain ⟨st₀, x₀, hst₀, hx₀, -, -, -, -, -, -, ⟨-, hstore⟩, rfl⟩ := grow_ok h
  rw [hst] at hst₀; cases hst₀; rw [hx] at hx₀; cases hx₀
  intro l hl
  have hy₀ := addAuth_self (releaseEff d.s b)
    (blockOf (releaseEff d.s b) st.arena (cellsOf st x.base (x.size + extra)))
  obtain ⟨-, hu, -, hcov, -, hleaf, -, -, -⟩ := hstore
  have hlr : l ∈ (S3.addAuth (releaseEff d.s b)
      (blockOf (releaseEff d.s b) st.arena (cellsOf st x.base (x.size + extra)))).afp
        (releaseEff d.s b).A.length := by
    simp only [S3.afp, hy₀]; exact (cellsOf_prefix st x.base x.size extra).subset hl
  have hne : l ≠ x.dst := by
    intro he; rw [he] at hlr
    exact (hcov x.dst hlr).1 (mem_footprint.2 ⟨hu.lt, hleaf, hu.lt, .inl rfl⟩)
  show (issueSeqEff _ _ _ _).I l = _
  unfold issueSeqEff; rw [storeEff_eq hy₀]
  simp only [hne, ↓reduceIte]
  show (releaseEff d.s b).I l = _; rw [releaseEff_I]

end Thms

/-! ## Marks are never reused (`mark_no_aba`) -/

/-- The marks of the stack `i` are pairwise distinct, name the stack `i` and have identifiers below
`fresh`. -/
def MarksWF (d : DS) : Prop :=
  ∀ (i : Nat) (st : Stack), d.stacks[i]? = some st →
    st.marks.Nodup ∧ ∀ m ∈ st.marks, m.stack = i ∧ m.id < d.fresh

/-- The mark `m` is live in no stack, and its identifier was given out. -/
def Gone (d : DS) (m : Mark) : Prop :=
  m.id < d.fresh ∧ ∀ (i : Nat) (st : Stack), d.stacks[i]? = some st → m ∉ st.marks

theorem marksWF_init : MarksWF DS.init := fun i st h => by simp [DS.init] at h

section ThmsK
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')] [DecidablePred k.SharedMutable]
  [DecidablePred k.Pinned] [DecidablePred k.ExternalDone] [DecidablePred k.Deallocable]
  [∀ p a, Decidable (k.FreeCompat p a)] [∀ p ls s, Decidable (k.Satisfiable p ls s)]

/-- A step that replaces the stack `j` by a stack with the same marks, or with a part of them,
keeps a property `Q` of the marks read at each index. -/
theorem stacks_set_marks {d : DS} {j : Nat} {st st' : Stack} (hst : d.stacks[j]? = some st)
    {Q : Nat → Mark → Prop}
    (hQ : ∀ (i : Nat) (st : Stack), d.stacks[i]? = some st → ∀ m ∈ st.marks, Q i m) {i : Nat}
    {st'' : Stack} (h : (d.stacks.set j st')[i]? = some st'') (hm : ∀ m ∈ st'.marks, m ∈ st.marks) :
    ∀ m ∈ st''.marks, Q i m := by
  intro m hm'
  rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact hQ _ st hst m (hm m hm')
  · exact hQ i st'' h m hm'

theorem stacks_set_nodup {d : DS} {j : Nat} {st st' : Stack} (hst : d.stacks[j]? = some st)
    (hw : MarksWF d) {i : Nat} {st'' : Stack} (h : (d.stacks.set j st')[i]? = some st'')
    (hsub : List.Sublist st'.marks st.marks) : st''.marks.Nodup := by
  rcases getElem?_set_cases h with ⟨rfl, rfl⟩ | ⟨-, h⟩
  · exact (hw _ st hst).1.sublist hsub
  · exact (hw i st'' h).1

theorem dexec_gone {d d' : DS} {o : DOp} {m : Mark} (h : dexec k d o = .ok d') (hg : Gone d m) :
    Gone d' m := by
  obtain ⟨hid, hno⟩ := hg
  have hQ : ∀ (i : Nat) (st : Stack), d.stacks[i]? = some st → ∀ m' ∈ st.marks, m' ≠ m :=
    fun i st h m' hm' e => hno i st h (e ▸ hm')
  have fin : ∀ {l : List Stack}, (∀ (i : Nat) (st : Stack), l[i]? = some st → ∀ m' ∈ st.marks, m' ≠ m) →
      ∀ (i : Nat) (st : Stack), l[i]? = some st → m ∉ st.marks := fun hl i st h hm => hl i st h m hm rfl
  cases o with
  | kernel o =>
    obtain ⟨-, hs, hf⟩ := dexec_kernel h
    exact ⟨by rw [hf]; exact hid, fun i st h' hm => hno i st (by rw [← hs]; exact h') hm⟩
  | newStack st i =>
    obtain ⟨-, -, rfl⟩ := newStack_ok h
    refine ⟨hid, fun i' st' h' hm => ?_⟩
    rcases getElem?_append_single h' with h' | ⟨-, rfl⟩
    · exact hno i' st' h' hm
    · simp at hm
  | push j size dst =>
    obtain ⟨st, hst, -, -, -, rfl⟩ := push_ok h
    refine ⟨hid, fin ?_⟩
    intro i st'' h' m' hm'; exact stacks_set_marks hst hQ h' (fun _ h => h) m' hm'
  | mark j =>
    obtain ⟨st, hst, rfl⟩ := mark_ok h
    refine ⟨Nat.lt_succ_of_lt hid, fun i st' h' hm => ?_⟩
    rcases getElem?_set_cases h' with ⟨rfl, rfl⟩ | ⟨-, h'⟩
    · rcases List.mem_append.1 hm with hm | hm
      · exact hno _ st hst hm
      · rw [List.mem_singleton] at hm; rw [hm] at hid; exact Nat.lt_irrefl _ hid
    · exact hno i st' h' hm
  | rewind j m' =>
    obtain ⟨st, hst, -, -, rfl⟩ := rewind_ok h
    refine ⟨hid, fin ?_⟩
    intro i st'' h' m' hm'
    exact stacks_set_marks hst hQ h' (fun _ h => List.takeWhile_subset _ h) m' hm'
  | grow j b extra =>
    obtain ⟨st, x, hst, -, -, -, -, -, -, -, -, rfl⟩ := grow_ok h
    refine ⟨hid, fin ?_⟩
    intro i st'' h' m' hm'; exact stacks_set_marks hst hQ h' (fun _ h => h) m' hm'

theorem drun_gone {m : Mark} : ∀ {d d' : DS} {os : List DOp}, drun k d os = some d' → Gone d m →
    Gone d' m
  | d, d', [], h, hg => by simp only [drun, Option.some.injEq] at h; subst h; exact hg
  | d, d', o :: os, h, hg => by
    simp only [drun] at h
    split at h
    · rename_i d₁ h₁; exact drun_gone h (dexec_gone h₁ hg)
    · cases h

theorem dexec_marksWF {d d' : DS} {o : DOp} (h : dexec k d o = .ok d') (hw : MarksWF d) :
    MarksWF d' := by
  have hQ : ∀ (i : Nat) (st : Stack), d.stacks[i]? = some st → ∀ m ∈ st.marks,
      m.stack = i ∧ m.id < d.fresh := fun i st h => (hw i st h).2
  cases o with
  | kernel o =>
    obtain ⟨-, hs, hf⟩ := dexec_kernel h
    intro i st h'; rw [hs] at h'; rw [hf]; exact hw i st h'
  | newStack st i =>
    obtain ⟨-, -, rfl⟩ := newStack_ok h
    intro i' st' h'
    rcases getElem?_append_single h' with h' | ⟨-, rfl⟩
    · exact hw i' st' h'
    · exact ⟨List.nodup_nil, fun m hm => by simp at hm⟩
  | push j size dst =>
    obtain ⟨st, hst, -, -, -, rfl⟩ := push_ok h
    intro i st'' h'
    exact ⟨stacks_set_nodup hst hw h' (List.Sublist.refl _),
      stacks_set_marks hst hQ h' (fun _ h => h)⟩
  | mark j =>
    obtain ⟨st, hst, rfl⟩ := mark_ok h
    intro i st' h'
    rcases getElem?_set_cases h' with ⟨rfl, rfl⟩ | ⟨-, h'⟩
    · refine ⟨List.nodup_append.2 ⟨(hw _ st hst).1, List.nodup_cons.2 ⟨by simp, List.nodup_nil⟩,
        fun a ha b hb e => ?_⟩, fun m hm => ?_⟩
      · rw [List.mem_singleton] at hb; subst hb; subst e
        exact Nat.lt_irrefl _ ((hw _ st hst).2 _ ha).2
      · rcases List.mem_append.1 hm with hm | hm
        · exact ⟨(hw _ st hst).2 m hm |>.1, Nat.lt_succ_of_lt ((hw _ st hst).2 m hm).2⟩
        · rw [List.mem_singleton] at hm; subst hm; exact ⟨rfl, Nat.lt_succ_self _⟩
    · exact ⟨(hw i st' h').1, fun m hm =>
        ⟨((hw i st' h').2 m hm).1, Nat.lt_succ_of_lt ((hw i st' h').2 m hm).2⟩⟩
  | rewind j m' =>
    obtain ⟨st, hst, -, -, rfl⟩ := rewind_ok h
    intro i st'' h'
    exact ⟨stacks_set_nodup hst hw h' (List.takeWhile_sublist _),
      stacks_set_marks hst hQ h' (fun _ h => List.takeWhile_subset _ h)⟩
  | grow j b extra =>
    obtain ⟨st, x, hst, -, -, -, -, -, -, -, -, rfl⟩ := grow_ok h
    intro i st'' h'
    exact ⟨stacks_set_nodup hst hw h' (List.Sublist.refl _),
      stacks_set_marks hst hQ h' (fun _ h => h)⟩

theorem drun_marksWF : ∀ {d d' : DS} {os : List DOp}, drun k d os = some d' → MarksWF d →
    MarksWF d'
  | d, d', [], h, hw => by simp only [drun, Option.some.injEq] at h; subst h; exact hw
  | d, d', o :: os, h, hw => by
    simp only [drun] at h
    split at h
    · rename_i d₁ h₁; exact drun_marksWF h (dexec_marksWF h₁ hw)
    · cases h

omit [DecidablePred k.SharedMutable] [DecidablePred k.Pinned] [DecidablePred k.ExternalDone]
  [DecidablePred k.Deallocable] [∀ p a, Decidable (k.FreeCompat p a)]
  [∀ p ls s, Decidable (k.Satisfiable p ls s)] in
/-- Under `MarksWF`, `rewind m` keeps exactly the marks older than `m` and removes `m` and every later
mark of the stack (brief: "`m` et toutes les marques au-dessus sont retirées, les plus anciennes
restent vivantes"). -/
theorem rewind_removes {d d' : DS} {j : Nat} {m : Mark} (hw : MarksWF d)
    (h : rewind k d j m = .ok d') {st : Stack} (hst : d.stacks[j]? = some st)
    {pre post : List Mark} (hs : st.marks = pre ++ m :: post) :
    ∃ st', d'.stacks[j]? = some st' ∧ st'.marks = pre ∧ ∀ m' ∈ m :: post, m' ∉ st'.marks := by
  have hnd := (hw j st hst).1
  rw [hs] at hnd
  have hdisj := (List.nodup_append.1 hnd).2.2
  have hmpre : m ∉ pre := fun h => hdisj m h m (List.mem_cons_self ..) rfl
  obtain ⟨⟨st', hst', hpre, -⟩, -, -⟩ := rewind_keeps_older_marks h hst hs hmpre
  exact ⟨st', hst', hpre, fun m' hm' hin => hdisj m' (hpre ▸ hin) m' hm' rfl⟩

/-- `mark_no_aba` (brief): every mark that `rewind m` removes, `m` and the later marks of the stack,
is live in no stack in any later state, even when the top returns to the same position: identifiers
are fresh and a mark is live by membership, so `rewind` of a removed mark fails forever after. -/
theorem mark_no_aba {d d₁ d' : DS} {j : Nat} {m : Mark} {os : List DOp} (hw : MarksWF d)
    (hr : rewind k d j m = .ok d₁) (h : drun k d₁ os = some d') {st : Stack}
    (hst : d.stacks[j]? = some st) {pre post : List Mark} (hs : st.marks = pre ++ m :: post)
    {m' : Mark} (hm' : m' ∈ m :: post) :
    (∀ (i : Nat) (st' : Stack), d'.stacks[i]? = some st' → m' ∉ st'.marks) ∧
      ∀ st', d'.stacks[j]? = some st' → rewind k d' j m' = .fail := by
  obtain ⟨st₁, hst₁, hgone1, hgone⟩ :
      ∃ st₁, d₁.stacks[j]? = some st₁ ∧ st₁.marks = pre ∧ ∀ m' ∈ m :: post, m' ∉ st₁.marks :=
    rewind_removes hw hr hst hs
  obtain ⟨st₀, hst₀, -, -, rfl⟩ := rewind_ok hr
  rw [hst] at hst₀; cases hst₀
  have hm'st : m' ∈ st.marks := by rw [hs]; exact List.mem_append_right _ hm'
  obtain ⟨-, hwj⟩ := hw j st hst
  have hg : Gone { d with
      s := releaseEff (d.s.addAuth (blockOf d.s st.arena (above st m))) d.s.A.length
      stacks := d.stacks.set j
        { st with
          top := m.top
          blocks := st.blocks.filter (·.base < m.top)
          marks := st.marks.takeWhile (· ≠ m) } } m' := by
    refine ⟨(hwj m' hm'st).2, fun i st' h' hm'' => ?_⟩
    rcases getElem?_set_cases h' with ⟨rfl, rfl⟩ | ⟨hi, h'⟩
    · rw [hst₁] at h'; cases h'; exact hgone m' hm' hm''
    · exact hi (((hw i st' h').2 m' hm'').1.symm.trans (hwj m' hm'st).1)
  have hg' := drun_gone h hg
  refine ⟨hg'.2, fun st' hst' => ?_⟩
  simp [rewind, hst', hg'.2 j st' hst']

/-- Every state reached by the library from `DS.init` has well-formed marks, so `mark_no_aba`
applies to it. -/
theorem drun_init_marksWF {os : List DOp} {d : DS} (h : drun k DS.init os = some d) : MarksWF d :=
  drun_marksWF h marksWF_init

end ThmsK

section ThmsB
variable {k : K} [∀ r r', Decidable (k.DeclaredDisjoint r r')]

/-! ## Bytes of the prefix after `grow` (refinement `Ern.MM23`) -/

/-- The state after the release of `b` and the `split` of `grow`, before the `store`. -/
def growMid (s : S3) (st : Stack) (x : Blk) (b extra : Nat) : S3 :=
  (releaseEff s b).addAuth (blockOf (releaseEff s b) st.arena (cellsOf st x.base (x.size + extra)))

/-- `grow_keeps_prefix_bytes` (brief), through the refinement `Ern.MM23` unchanged: in a reached
state, the `ok` of `grow` is a `release` and a `split`, steps without an MM-02 step (`NoStep`, K4,
whose arrival states stay in `Repr` with the same MM-02 state, `r6_noStep`), then a `store`, whose
MM-02 counterpart is one write of the range of the destination (`storeOps`, L6, `r6_store`); for
every layout well-formed in the state (`LayoutWF`), that write leaves the bytes of every cell of the
old block, values and provenances (`rangeBytes`), unchanged. Under `DDSound k`. -/
theorem grow_keeps_prefix_bytes (hdd : DDSound k) {statics : Statics} {d d' : DS} {j b extra : Nat}
    (hr : Reachable k statics d.s) (h : grow k d j b extra = .ok d') {st : Stack} {x : Blk}
    (hst : d.stacks[j]? = some st) (hx : st.blocks.getLast? = some x) {L : MM23.Layout}
    {s2 : MM02.State} (hlw : MM23.LayoutWF L d.s s2) (pe : MM23.PtrEnc) :
    MM23.NoStep k d.s (releaseEff d.s b) ∧
      MM23.NoStep k (releaseEff d.s b) (growMid d.s st x b extra) ∧
      StoreStep (releaseEff d.s b).A.length x.dst (growMid d.s st x b extra) (.ok d'.s) ∧
      ∀ l ∈ cellsOf st x.base x.size,
        MM23.rangeBytes (MM23.exec s2 (MM23.storeOps pe s2 L (growMid d.s st x b extra)
          (releaseEff d.s b).A.length x.dst)) L l = MM23.rangeBytes s2 L l := by
  obtain ⟨st₀, x₀, hst₀, hx₀, -, -, -, hrel, -, -, ⟨hsp, hstore⟩, rfl⟩ := grow_ok h
  rw [hst] at hst₀; cases hst₀; rw [hx] at hx₀; cases hx₀
  have hr₁ : Reachable k statics (releaseEff d.s b) := .release hr (.ok hrel)
  have hr₂ : Reachable k statics (growMid d.s st x b extra) :=
    .split hr₁ (rs := [cellsOf st x.base (x.size + extra)]) (src := st.internal) (.ok hsp)
  refine ⟨.release (.ok hrel), .split (rs := [cellsOf st x.base (x.size + extra)])
    (src := st.internal) (.ok hsp), .ok hstore, fun l hl => ?_⟩
  have hy₀ := addAuth_self (releaseEff d.s b)
    (blockOf (releaseEff d.s b) st.arena (cellsOf st x.base (x.size + extra)))
  have hP : (growMid d.s st x b extra).P = d.s.P := releaseEff_P d.s b
  obtain ⟨-, hu, -, hcov, -, hleaf, -, -, -⟩ := hstore
  have hlr' : l ∈ cellsOf st x.base (x.size + extra) := (cellsOf_prefix st x.base x.size extra).subset hl
  have hlr : l ∈ (growMid d.s st x b extra).afp (releaseEff d.s b).A.length := by
    simp only [growMid, S3.afp, hy₀]; exact hlr'
  have hne : l ≠ x.dst := by
    intro he; rw [he] at hlr
    exact (hcov x.dst hlr).1 (mem_footprint.2 ⟨hu.lt, hleaf, hu.lt, .inl rfl⟩)
  have hfp := (MM23.reachable_fpLeaves_frameOwnedLive hdd hr₂).1
  have hwf₂ := (reachable_invariants hdd hr₂).1
  have hll : isLeaf d.s.P l := by rw [← hP]; exact hfp _ _ hy₀ l hlr'
  have hlt : l < d.s.P.length := by rw [← hP]; exact hwf₂.2.1 _ _ hy₀ l hlr'
  have hdl : x.dst < d.s.P.length := by rw [← hP]; exact hu.lt
  have hdleaf : isLeaf d.s.P x.dst := by rw [← hP]; exact hleaf
  have halloc : MM23.AllocP s2 (L x.dst).alloc fun _ => True :=
    (hlw.within x.dst hdl hdleaf).mono fun _ _ => trivial
  have hdis : (L l).alloc ≠ (L x.dst).alloc ∨
      MM02.RangeDisjoint (L l).off (L l).len (L x.dst).off (L x.dst).len := by
    by_cases ha : (L l).alloc = (L x.dst).alloc
    · exact .inr (hlw.disjoint l hlt x.dst hdl hll hdleaf hne ha)
    · exact .inl ha
  exact MM23.rangeBytes_write_other (MM23.Dom.refl s2) halloc hdis

end ThmsB

/-! ## Cases (brief, question 2)

Runs from `DS.init` under the test contracts `K0`; each statement includes that the run is `ok`
(`isSome`), so that `final` is its state; every verdict by `decide`. -/

def Out.isOk : Out → Bool
  | .ok _ => true
  | _ => false

def Out.isFail : Out → Bool
  | .fail => true
  | _ => false

def Out.isReject : Out → Bool
  | .reject => true
  | _ => false

/-- The state of a run from `DS.init` (`DS.init` when a step is not `ok`). -/
def final (os : List DOp) : DS := (drun K0 DS.init os).getD DS.init

/-- The kernel state of an `ok` run of the library is reached. -/
theorem final_reach {os : List DOp} (h : (drun K0 DS.init os).isSome = true) :
    Reachable K0 [] (final os).s := by
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.1 h
  have := drun_reach (statics := []) (show Reachable K0 [] DS.init.s from .init (by decide)) hd
  simp only [final, hd, Option.getD_some]; exact this

/-- A cell of the storage `p`. -/
abbrev cellOf (p : Nat) : Option Nat × Option Nat × Nat := (some p, none, 0)

/-- One stack: frame 1 with the leaves 0 (stack value), 2, 3, 4 (cells of the storage 1), 5, 6, 7
(destinations), of root authorities 0 (on 0), 1 (on 1), 2, 3, 4 (on 5, 6, 7); `internal` 5 derived
from 1 and stored into 0; the stack 0 created on 1 with `internal` 5. -/
def setup1 : List DOp :=
  [.kernel (.enter [] [lf, lf, cellOf 1, cellOf 1, cellOf 1, lf, lf, lf]),
    .kernel (.derive 1 1 .modify), .kernel (.store 5 0), .newStack 1 5]

/-- Mark `⟨0, 0, 0⟩`, `push 2` into 5 (block 6 on `[2, 3]`), mark `⟨0, 1, 2⟩`, `push 1` into 6
(block 7 on `[4]`). -/
def opsR : List DOp := setup1 ++ [.mark 0, .push 0 2 5, .mark 0, .push 0 1 6]

/-- **`rewind` refused then accepted**: `rewind ⟨0, 1, 2⟩` is rejected while the block 7, derived
from `internal`, covers the cell 4 above the mark (`rewind_rejects_live_above`); after the release
of 7 it is accepted: the top returns to 2, the mark `⟨0, 0, 0⟩` stays, the block 6 stays. -/
theorem case_rewind :
    (drun K0 DS.init opsR).isSome = true ∧
    (dexec K0 (final opsR) (.rewind 0 ⟨0, 1, 2⟩)).isReject = true ∧
    (drun K0 DS.init (opsR ++ [.kernel (.release 7), .rewind 0 ⟨0, 1, 2⟩])).isSome = true ∧
    (final (opsR ++ [.kernel (.release 7), .rewind 0 ⟨0, 1, 2⟩])).stacks.map
      (fun st => (st.top, st.blocks, st.marks)) = [(2, [⟨0, 2, 6, 5⟩], [⟨0, 0, 0⟩])] := by
  decide

/-- The run of `case_rewind`, then a new mark: it has the top 2 of the removed mark `⟨0, 1, 2⟩` and
the fresh identifier 2. -/
def opsA : List DOp := opsR ++ [.kernel (.release 7), .rewind 0 ⟨0, 1, 2⟩, .mark 0]

/-- **ABA** (`mark_no_aba`): the top is back at 2, the position of the removed mark `⟨0, 1, 2⟩`,
and a mark `⟨0, 2, 2⟩` is live there; `rewind ⟨0, 1, 2⟩` fails, `rewind ⟨0, 2, 2⟩` is accepted. -/
theorem case_aba :
    (drun K0 DS.init opsA).isSome = true ∧
    (final opsA).stacks.map (fun st => (st.top, st.marks)) = [(2, [⟨0, 0, 0⟩, ⟨0, 2, 2⟩])] ∧
    (dexec K0 (final opsA) (.rewind 0 ⟨0, 1, 2⟩)).isFail = true ∧
    (dexec K0 (final opsA) (.rewind 0 ⟨0, 2, 2⟩)).isOk = true := by
  decide

/-- The run of `case_aba`, then `grow` of the last block 6 by one cell. -/
def opsG : List DOp := opsA ++ [.grow 0 6 1]

/-- **`grow`**: `grow 6 1` is accepted in place: the last block becomes `⟨0, 3, 9, 5⟩`, of the same
base and destination, and its authority 9 covers `[2, 3, 4]`; `grow 9 1` then fails, no cell
following; `grow 6 1` is rejected, 6 being no longer the last block. -/
theorem case_grow :
    (drun K0 DS.init opsG).isSome = true ∧
    (final opsG).stacks.map (fun st => (st.top, st.blocks)) = [(3, [⟨0, 3, 9, 5⟩])] ∧
    (final opsG).s.afp 9 = [2, 3, 4] ∧
    (dexec K0 (final opsG) (.grow 0 9 1)).isFail = true ∧
    (dexec K0 (final opsG) (.grow 0 6 1)).isReject = true := by
  decide

/-- Two stacks: frame 1 with the leaves 0 and 8 (stack values), the storages 1 (cells 2, 3, 4)
and 9 (cells 10, 11), the destinations 5, 6, 7, 12, of root authorities 0 to 7; `internal` 8 on 1
stored into 0, stack 0; `internal` 9 on 9 stored into 8, stack 1. -/
def setup2 : List DOp :=
  [.kernel (.enter [] [lf, lf, cellOf 1, cellOf 1, cellOf 1, lf, lf, lf, lf, lf, cellOf 9, cellOf 9, lf]),
    .kernel (.derive 1 1 .modify), .kernel (.store 8 0), .newStack 1 8,
    .kernel (.derive 6 9 .modify), .kernel (.store 9 8), .newStack 9 9]

def opsS : List DOp := setup2 ++ [.mark 0, .push 0 1 5, .push 1 1 12, .mark 1]

/-- **Several stacks**: the guard of §56 rejects a second stack with `internal` 8, and a kernel
`newArena` with `internal` 8, which the kernel alone accepts; each stack has its top, blocks and
marks; `rewind` of stack 0 to its mark is rejected while its block 10 lives, a mark of stack 1 is not
a live mark of stack 0 (`fail`), stack 1 rewinds to its mark and pushes again. -/
theorem case_stacks :
    (drun K0 DS.init setup2).isSome = true ∧
    (dexec K0 (final setup2) (.newStack 1 8)).isReject = true ∧
    (kexec K0 (final setup2).s (.newArena 1 8)).isSome = true ∧
    (dexec K0 (final setup2) (.kernel (.newArena 1 8))).isReject = true ∧
    (drun K0 DS.init opsS).isSome = true ∧
    (final opsS).stacks.map (fun st => (st.internal, st.top, st.blocks, st.marks)) =
      [(8, 1, [⟨0, 1, 10, 5⟩], [⟨0, 0, 0⟩]), (9, 1, [⟨0, 1, 11, 12⟩], [⟨1, 1, 1⟩])] ∧
    (dexec K0 (final opsS) (.rewind 0 ⟨0, 0, 0⟩)).isReject = true ∧
    (dexec K0 (final opsS) (.rewind 0 ⟨1, 1, 1⟩)).isFail = true ∧
    (drun K0 DS.init (opsS ++ [.rewind 1 ⟨1, 1, 1⟩, .push 1 1 6])).isSome = true := by
  decide

/-- Frame use: the caller derives 6 from the root of the stack value at `Modify` and passes it to a
callee with one local 8; the callee marks the stack at entry and pushes 2 cells into its local
(block 8). At exit, `rewind` is rejected while the block lives; after `endUse` of the local, which
releases the block, `rewind` to the entry mark and `exitFrame` are accepted, and the stack is empty
again. -/
def opsF : List DOp :=
  setup1 ++ [.kernel (.derive 0 0 .modify), .kernel (.enter [6] [lf]), .mark 0, .push 0 2 8]

theorem case_frame :
    (drun K0 DS.init opsF).isSome = true ∧
    (dexec K0 (final opsF) (.rewind 0 ⟨0, 0, 0⟩)).isReject = true ∧
    (drun K0 DS.init (opsF ++ [.kernel (.endUse 8), .rewind 0 ⟨0, 0, 0⟩, .kernel .exit])).isSome = true ∧
    (final (opsF ++ [.kernel (.endUse 8), .rewind 0 ⟨0, 0, 0⟩, .kernel .exit])).stacks.map
      (fun st => (st.top, st.blocks, st.marks)) = [(0, [], [])] := by
  decide

/-- Block 6 pushed on `[2, 3]`, mark `⟨0, 0, 2⟩`, block grown to `[2, 3, 4]` (authority 7), released;
then 8 derived from `internal` 5 on the cell 2, below the mark. -/
def opsE4 : List DOp :=
  setup1 ++ [.push 0 2 5, .mark 0, .grow 0 6 1, .kernel (.release 7), .kernel (.derive 5 2 .modify)]

/-- Marks `⟨0, 0, 0⟩` and `⟨0, 1, 1⟩` around block 6 on `[2]`; block 7 on `[3]` pushed after both
marks, released, and returned by `rewind ⟨0, 1, 1⟩`; block 6 released; then 9 derived from
`internal` 5 on the cell 3, above the current top. -/
def opsE8 : List DOp :=
  setup1 ++ [.mark 0, .push 0 1 5, .mark 0, .push 0 1 6, .kernel (.release 7),
    .rewind 0 ⟨0, 1, 1⟩, .kernel (.release 6), .kernel (.derive 5 3 .modify)]

/-- Mark `⟨0, 0, 0⟩`, then a `push` of size 0: block 6, active, of empty footprint. -/
def opsE3 : List DOp := setup1 ++ [.mark 0, .push 0 0 5]

/-- **Reading of "couvre une région émise après `m`"** (review, DS-2 and DS-3): `rewind` looks at
the cells it returns (`above`). In `opsE4` the authority 8, active and derived from `internal`,
covers the cell 2 of the region `[2, 3, 4]` issued (by `grow`) after the mark `⟨0, 0, 2⟩`, below
the mark, and `rewind` is accepted (the cell 2 is not returned). In `opsE8` the authority 9 covers
the cell 3 of a region issued after `⟨0, 0, 0⟩`, now above the top, and `rewind` is accepted (the
cell 3 is already available). In `opsE3` the empty block 6, issued after the mark and active, does
not block `rewind`, and stays active once the metadata forget it. -/
theorem case_rewind_reading :
    (drun K0 DS.init opsE4).isSome = true ∧
    (final opsE4).s.A[8]?.map (fun y => (y.active, y.origin, y.footprint)) = some (true, some 5, [2]) ∧
    (dexec K0 (final opsE4) (.rewind 0 ⟨0, 0, 2⟩)).isOk = true ∧
    (drun K0 DS.init opsE8).isSome = true ∧
    (final opsE8).s.A[9]?.map (fun y => (y.active, y.origin, y.footprint)) = some (true, some 5, [3]) ∧
    (dexec K0 (final opsE8) (.rewind 0 ⟨0, 0, 0⟩)).isOk = true ∧
    (drun K0 DS.init (opsE3 ++ [.rewind 0 ⟨0, 0, 0⟩])).isSome = true ∧
    (final (opsE3 ++ [.rewind 0 ⟨0, 0, 0⟩])).s.A[6]?.map (fun y => (y.active, y.origin, y.footprint)) =
      some (true, some 5, []) := by
  decide

/-- Block 6 pushed into 5, then a callee entered with only 7, a `Modify` derived from the root of 5:
it has no right on the stack value 0. -/
def opsZ : List DOp := setup1 ++ [.push 0 1 5, .kernel (.derive 2 5 .modify), .kernel (.enter [7] [])]

/-- **Static clauses before `fail`** (§58, §77.4; review, DS-5 and Q2-GROW-ORDER): without a right on
the stack value, `grow` is rejected with or without room; `push` into an `Init` destination is
rejected; `push` into a destination inside the requested cells is rejected even without room, while
the same `push` into an outside destination fails. -/
theorem case_static_before_fail :
    (drun K0 DS.init opsZ).isSome = true ∧
    (dexec K0 (final opsZ) (.grow 0 6 5)).isReject = true ∧
    (dexec K0 (final opsZ) (.grow 0 6 1)).isReject = true ∧
    (drun K0 DS.init (setup1 ++ [.kernel (.write 2 [5])])).isSome = true ∧
    (dexec K0 (final (setup1 ++ [.kernel (.write 2 [5])])) (.push 0 1 5)).isReject = true ∧
    (drun K0 DS.init setup1).isSome = true ∧
    (dexec K0 (final setup1) (.push 0 4 2)).isReject = true ∧
    (dexec K0 (final setup1) (.push 0 4 5)).isFail = true := by
  decide

/-- The kernel states of the cases are reached. -/
theorem cases_reachable :
    Reachable K0 [] (final opsR).s ∧ Reachable K0 [] (final opsA).s ∧
    Reachable K0 [] (final opsG).s ∧ Reachable K0 [] (final opsS).s ∧
    Reachable K0 [] (final (opsF ++ [.kernel (.endUse 8), .rewind 0 ⟨0, 0, 0⟩, .kernel .exit])).s :=
  ⟨final_reach (by decide), final_reach (by decide), final_reach (by decide),
    final_reach (by decide), final_reach (by decide)⟩

end Ern.Lib.DataStack
