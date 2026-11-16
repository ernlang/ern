import Ern.ConcurrencyModel.State

/-!
# Concurrent authority machine: inherited operations and frame transitions

* the kernel operations O1–O16 of the Memory Model Specification v0.1 (§60–§75) executed by a
  live context `c` (C2): every operation reads the view of `c` (current frame =
  top of its stack, liveness = globally live frames); the clauses that read `ancestor` (§63.6,
  §63.7, §64.3, §65.4, §65.5, §72.4, §73.5) read `ancestorC` instead; O6 pushes the new frame on
  the stack of `c`; O7 is `exitFrameC` (C6: O7 and the reparenting of the context-initial
  frames whose parent is the exiting frame);
* `spawn` (C4, modeled on Spec 1 §72), `terminate` (C7, Spec 1 §73 on the initial frame
  of a non-initial context), `join` (C8);
* `CStep`, the union of their `ok` transitions.

Waiting (`join` on a live context) has no outcome: the transition is not enabled (C8).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel.Access

/-! ## Outcomes (Spec 1 §58) -/

/-- Image of an outcome (Spec 1 §58). -/
def omap {σ τ : Type} (f : σ → τ) : Outcome3 σ → Outcome3 τ
  | .ok s => .ok (f s)
  | .reject => .reject
  | .fail => .fail

/-! ## Operations that do not read `ancestor` (Spec 1 §60–§62, §66–§71, §74, §75; C2) -/

/-- An operation of Spec 1 that reads neither `ancestor` nor the stack beyond its top and its
membership, run by context `c` on its view and written back (C2). The context must be live;
otherwise the operation has no outcome. -/
def ViewStep (R : S3 → Outcome3 S3 → Prop) (c : Nat) (s : SC) (o : Outcome3 SC) : Prop :=
  s.Live c ∧ ∃ o₃, R (s.view c) o₃ ∧ o = omap s.set o₃

/-! ## O4 `transfer` re-indexed (Spec 1 §63) -/

/-- Effect of `transfer` executed by `c` (Spec 1 §63 effect, C2). -/
def transferEffC (s : SC) (c src dst : Nat) : SC := s.set (transferEff (s.view c) src dst)

/-- Preconditions of `transfer` executed by `c` (Spec 1 §63 re-indexed, C2): the clauses of
`TransferPre` on the view of `c`, with §63.6 and §63.7 read on `ancestorC`. -/
structure TransferPreC (k : K) (s : SC) (c src dst : Nat) : Prop where
  /-- Spec 1 §63.1: `source` is usable. -/
  srcUsable : (s.view c).Usable src
  /-- Spec 1 §63.1: `destination` is usable. -/
  dstUsable : (s.view c).Usable dst
  /-- Spec 1 §63.1: exercisable `Modify` over the source. -/
  srcRight : HasRight (s.view c) .modify src
  /-- Spec 1 §63.1: exercisable `Modify` over the destination. -/
  dstRight : HasRight (s.view c) .modify dst
  /-- Spec 1 §63.2: same shape of ordered subtrees. -/
  sameShape : SameShape (s.view c).P src dst
  /-- Spec 1 §63.3: all source leaves are `Init`. -/
  srcInit : ∀ l ∈ footprint (s.view c).P src, (s.view c).I l = .init
  /-- Spec 1 §63.3: no destination leaf is `Init`. -/
  dstNotInit : ∀ l ∈ footprint (s.view c).P dst, (s.view c).I l ≠ .init
  /-- Spec 1 §63.3: source and destination footprints are disjoint. -/
  disjoint : ¬ overlap (s.view c).P src dst
  /-- Spec 1 §63.4: no active derived authority covers a source leaf from outside the source,
  except some authority grounding the `Modify` right over the source and its origin chain. -/
  noOutsideDerived : ∃ g ∈ List.range (s.view c).A.length, Grounds (s.view c) .modify src g ∧
    ∀ j ∈ List.range (s.view c).A.length, ActiveDerivedOutside (s.view c) src j →
      RightChain (s.view c) g j
  /-- Spec 1 §63.5: no in-place source leaf is pinned, statically or dynamically. -/
  notPinned : ∀ l ∈ footprint (s.view c).P src, ¬ k.Pinned l ∧ (s.view c).pin l = false
  /-- Spec 1 §63.6: dependencies of the usable places following the value are valid. -/
  depsValid : ∀ x ∈ movedDeps (s.view c) src, (s.view c).Active x
  /-- Spec 1 §63.6 re-indexed: `AnchorOrder` (on `ancestorC`) in the resulting state. -/
  anchorOrder : AnchorOrderC (transferEffC s c src dst)
  /-- Spec 1 §63.7 re-indexed: every moved held authority satisfies `AnchorOrderHeld` (on
  `ancestorC`) in the resulting state. -/
  anchorOrderHeld : ∀ x ∈ List.range (s.view c).A.length, AnchorMoves (s.view c) src x →
    ∀ q ∈ List.range (s.view c).P.length, (transferEff (s.view c) src dst).Usable q →
      OptP ((transferEff (s.view c) src dst).A[x]?) (fun y => y.active = true →
        y.holder = .place q →
          EffAnchorOKC (transferEffC s c src dst) x
            ((transferEff (s.view c) src dst).pframe q)) True
  /-- Spec 1 §63.8: local self-blocking prevention. -/
  noSelfLock : NoLocalSelfLock (s.view c) src dst
  /-- Spec 1 §63.9: `destination` is usable in the resulting state. -/
  dstUsableAfter : (transferEff (s.view c) src dst).Usable dst

/-- Decidability of the preconditions of `transfer` executed by `c` (Spec 1 §63). -/
instance (k : K) [DecidablePred k.Pinned] (s : SC) (c src dst : Nat) :
    Decidable (TransferPreC k s c src dst) :=
  decidable_of_iff ((s.view c).Usable src ∧ (s.view c).Usable dst ∧
    HasRight (s.view c) .modify src ∧ HasRight (s.view c) .modify dst ∧
    SameShape (s.view c).P src dst ∧ (∀ l ∈ footprint (s.view c).P src, (s.view c).I l = .init) ∧
    (∀ l ∈ footprint (s.view c).P dst, (s.view c).I l ≠ .init) ∧ ¬ overlap (s.view c).P src dst ∧
    (∃ g ∈ List.range (s.view c).A.length, Grounds (s.view c) .modify src g ∧
      ∀ j ∈ List.range (s.view c).A.length, ActiveDerivedOutside (s.view c) src j →
        RightChain (s.view c) g j) ∧
    (∀ l ∈ footprint (s.view c).P src, ¬ k.Pinned l ∧ (s.view c).pin l = false) ∧
    (∀ x ∈ movedDeps (s.view c) src, (s.view c).Active x) ∧
    AnchorOrderC (transferEffC s c src dst) ∧
    (∀ x ∈ List.range (s.view c).A.length, AnchorMoves (s.view c) src x →
      ∀ q ∈ List.range (s.view c).P.length, (transferEff (s.view c) src dst).Usable q →
        OptP ((transferEff (s.view c) src dst).A[x]?) (fun y => y.active = true →
          y.holder = .place q →
            EffAnchorOKC (transferEffC s c src dst) x
              ((transferEff (s.view c) src dst).pframe q)) True) ∧
    NoLocalSelfLock (s.view c) src dst ∧ (transferEff (s.view c) src dst).Usable dst)
    ⟨fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩,
     fun ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩ =>
      ⟨a, b, c, d, e, f, g, h, i, j, l, m, n, o, p⟩⟩

/-! ## O5 `depend` re-indexed (Spec 1 §64) -/

/-- Effect of `depend` executed by `c` (Spec 1 §64 effect, C2). -/
def dependEffC (s : SC) (c q x : Nat) : SC := s.set (dependEff (s.view c) q x)

/-- Preconditions of `depend` executed by `c` (Spec 1 §64 re-indexed, C2). -/
structure DependPreC (s : SC) (c q x : Nat) : Prop where
  /-- Spec 1 §64.1: `result` is usable. -/
  usable : (s.view c).Usable q
  /-- Spec 1 §64.1: exercisable `Modify` over `result`. -/
  right : HasRight (s.view c) .modify q
  /-- Spec 1 §64.2: `anchor` is active. -/
  anchorActive : (s.view c).Active x
  /-- Spec 1 §64.3 re-indexed: the effective anchor's frame is the frame of `result` or an
  `ancestorC` of it. -/
  anchorOrder : EffAnchorOKC s x ((s.view c).pframe q)

/-- Decidability of the preconditions of `depend` executed by `c` (Spec 1 §64). -/
instance (s : SC) (c q x : Nat) : Decidable (DependPreC s c q x) :=
  decidable_of_iff ((s.view c).Usable q ∧ HasRight (s.view c) .modify q ∧ (s.view c).Active x ∧
    EffAnchorOKC s x ((s.view c).pframe q))
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩⟩

/-! ## O8 `store` re-indexed (Spec 1 §65) -/

/-- Effect of `store` executed by `c` (Spec 1 §65 effect, C2). -/
def storeEffC (s : SC) (c a p : Nat) : SC := s.set (storeEff (s.view c) a p)

/-- Preconditions of `store` executed by `c` (Spec 1 §65 re-indexed, C2). -/
structure StorePreC (s : SC) (c a p : Nat) : Prop where
  /-- Spec 1 §65.1: the authority is active, derived, and held by the current frame. -/
  derivedHeld : OptP ((s.view c).A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧
    y.holder = .frame (s.view c).top) False
  /-- Spec 1 §65.2: `target` is usable. -/
  usable : (s.view c).Usable p
  /-- Spec 1 §65.2: `target` is a leaf. -/
  leaf : isLeaf (s.view c).P p
  /-- Spec 1 §65.2: exercisable `Modify` over `target`. -/
  right : HasRight (s.view c) .modify p
  /-- Spec 1 §65.2: `target` holds no active authority. -/
  free : ∀ j ∈ List.range (s.view c).A.length,
    OptP ((s.view c).A[j]?) (fun z => z.active = true → z.holder ≠ .place p) True
  /-- Spec 1 §65.3: the authority covers no leaf of `target` nor of storage it owns. -/
  noCover : ∀ l ∈ (s.view c).afp a, l ∉ footprint (s.view c).P p ∧
    ∀ q ∈ List.range (s.view c).P.length, OwnedIn (s.view c).P p q →
      l ∉ footprint (s.view c).P q
  /-- Spec 1 §65.4 re-indexed: the effective anchor respects `AnchorOrder` (on `ancestorC`)
  relative to the frame of `target`. -/
  anchorOrder : EffAnchorOKC s a ((s.view c).pframe p)
  /-- Spec 1 §65.5: in the resulting state, `target` is under exercisable `Modify`. -/
  keepsTarget : HasRight (storeEff (s.view c) a p) .modify p
  /-- Spec 1 §65.5 re-indexed: `AnchorOrderHeld` (on `ancestorC`) in the resulting state. -/
  anchorOrderHeld : AnchorOrderHeldC (storeEffC s c a p)

/-- Decidability of the preconditions of `store` executed by `c` (Spec 1 §65). -/
instance (s : SC) (c a p : Nat) : Decidable (StorePreC s c a p) :=
  decidable_of_iff (OptP ((s.view c).A[a]?) (fun y => y.active = true ∧ y.origin ≠ none ∧
      y.holder = .frame (s.view c).top) False ∧ (s.view c).Usable p ∧ isLeaf (s.view c).P p ∧
    HasRight (s.view c) .modify p ∧
    (∀ j ∈ List.range (s.view c).A.length,
      OptP ((s.view c).A[j]?) (fun z => z.active = true → z.holder ≠ .place p) True) ∧
    (∀ l ∈ (s.view c).afp a, l ∉ footprint (s.view c).P p ∧
      ∀ q ∈ List.range (s.view c).P.length, OwnedIn (s.view c).P p q →
        l ∉ footprint (s.view c).P q) ∧
    EffAnchorOKC s a ((s.view c).pframe p) ∧ HasRight (storeEff (s.view c) a p) .modify p ∧
    AnchorOrderHeldC (storeEffC s c a p))
    ⟨fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩,
     fun ⟨a, b, c, d, e, f, g, h, i⟩ => ⟨a, b, c, d, e, f, g, h, i⟩⟩

/-! ## O6 `enterFrame` re-indexed (Spec 1 §72) -/

/-- Effect of `enterFrame` executed by `c` (Spec 1 §72 effect, C2): the effect of Spec 1 on
the view of `c`; the new frame `nF` is pushed on the stack of `c`. -/
def enterEffC (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) : SC :=
  { s.set (enterEff (s.view c) ps ls) with
    C := s.C.modify c fun x => { x with stack := s.nF :: x.stack } }

/-- Preconditions of `enterFrame` executed by `c` (Spec 1 §72 re-indexed, C2). -/
structure EnterPreC (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) : Prop where
  /-- Spec 1 §72.1 re-indexed: the calling frame, the current frame of `c`, is live. -/
  callerLive : s.stk c ≠ []
  /-- Spec 1 §72.1: each parameter is an active derived authority held by the caller. -/
  params : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
    y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False
  /-- Spec 1 §72.2: the locals form a well-formed shape. -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- Spec 1 §72.3 re-indexed: origin protection on entry, in the resulting state, for the
  executing context. -/
  originHidden : ∀ p ∈ ps, ParamOriginHidden ((enterEffC s c ps ls).view c) p
  /-- Spec 1 §72.4 re-indexed: `AnchorOrderHeld` (on `ancestorC`) over the resulting state. -/
  anchorOrderHeld : AnchorOrderHeldC (enterEffC s c ps ls)

/-- Decidability of the preconditions of `enterFrame` executed by `c` (Spec 1 §72). -/
instance (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) :
    Decidable (EnterPreC s c ps ls) :=
  decidable_of_iff (s.stk c ≠ [] ∧ (∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y =>
      y.active = true ∧ y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False) ∧
    ShapeOK s.P.length ls.toShape ∧
    (∀ p ∈ ps, ParamOriginHidden ((enterEffC s c ps ls).view c) p) ∧
    AnchorOrderHeldC (enterEffC s c ps ls))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-! ## O7 re-indexed: `exitFrameC` (Spec 1 §73; C6) -/

/-- Reparenting (C6 effect): every live context whose initial frame has parent `f` gets the
parent `p`. -/
def reparent (C : List Ctx) (f p : Nat) : List Ctx :=
  C.map fun x => if x.life = .live ∧ x.parent = some f then { x with parent := some p } else x

/-- Effect of `exitFrameC` executed by `c` (Spec 1 §73 effect; C6 effect): the effect of Spec 1 on
the view of `c`, whose surviving frames are the other live frames; the top `f` of the stack of `c`
is popped, its caller `p` becomes current again, and the context-initial frames whose parent is
`f` are reparented to `p`; the other ancestry links are unchanged (C6 effect). -/
def exitEffC (s : SC) (c : Nat) : SC :=
  { s.set (exitEff (s.view c)) with
    C := reparent (s.C.modify c fun x => { x with stack := x.stack.tail })
      ((s.stk c).headD 0) ((s.stk c).tail.headD 0) }

/-- Preconditions of `exitFrameC` executed by `c` (Spec 1 §73 re-indexed; C6, C6.1: O7.1
transposed, O7.2–O7.5 on the global state). The surviving frames are the other globally live
frames. -/
structure ExitPreC (k : K) (s : SC) (c : Nat) : Prop where
  /-- Spec 1 §73.1 re-indexed (C6, first paragraph): the current frame of `c` is not the
  initial frame of its context and has a surviving caller in its stack. -/
  hasCaller : (s.stk c).tail ≠ []
  /-- Spec 1 §73.2, §73.4, §73.5: every anchor of a place usable after the exit has a surviving
  authority among itself and its origins. -/
  anchors : ∀ q ∈ List.range s.P.length, ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
    ∀ x ∈ s.D q, firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x) ≠ none
  /-- Spec 1 §73.4: every surviving derived authority has a surviving active origin. -/
  origins : ∀ a ∈ List.range s.A.length, Survives (s.view c) (s.view c).F.tail a →
    (s.view c).org a ≠ none → firstSurv (s.view c) (s.view c).F.tail ((s.view c).ancs a) ≠ none
  /-- Spec 1 §73.3: no leaf of a place that dies with the frame is pinned. -/
  notPinned : ∀ q ∈ List.range s.P.length, (s.view c).Usable q →
    ¬ ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
    ∀ l ∈ footprint s.P q, (s.view c).pin l = false ∧ ¬ k.Pinned l
  /-- Spec 1 §73.5 re-indexed: `AnchorOrderHeld` (on `ancestorC`) in the resulting state. -/
  anchorOrderHeld : AnchorOrderHeldC (exitEffC s c)

/-- Decidability of the preconditions of `exitFrameC` (Spec 1 §73). -/
instance (k : K) [DecidablePred k.Pinned] (s : SC) (c : Nat) : Decidable (ExitPreC k s c) :=
  decidable_of_iff ((s.stk c).tail ≠ [] ∧
    (∀ q ∈ List.range s.P.length, ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x) ≠ none) ∧
    (∀ a ∈ List.range s.A.length, Survives (s.view c) (s.view c).F.tail a →
      (s.view c).org a ≠ none → firstSurv (s.view c) (s.view c).F.tail ((s.view c).ancs a) ≠ none) ∧
    (∀ q ∈ List.range s.P.length, (s.view c).Usable q →
      ¬ ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
      ∀ l ∈ footprint s.P q, (s.view c).pin l = false ∧ ¬ k.Pinned l) ∧
    AnchorOrderHeldC (exitEffC s c))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-! ## The inherited operations O1–O16 executed by a context (C2) -/

/-- Outcome relation of a kernel operation O1–O16 executed by context `c` (Spec 1 §60–§75
re-indexed, C2). Operations reading `ancestor` or changing the stack have their re-indexed
preconditions and effects; the others run on the view of `c`. A context that is not live executes
nothing. -/
def opStepC (k : K) : KernelOp → Nat → SC → Outcome3 SC → Prop
  | .transfer src dst, c, s, o =>
    s.Live c ∧ Guarded (TransferPreC k s c src dst) (transferEffC s c src dst) o
  | .depend q x, c, s, o => s.Live c ∧ Guarded (DependPreC s c q x) (dependEffC s c q x) o
  | .store a p, c, s, o => s.Live c ∧ Guarded (StorePreC s c a p) (storeEffC s c a p) o
  | .enter ps ls, c, s, o =>
    s.Live c ∧ Guarded (EnterPreC s c ps ls) (enterEffC s c ps ls) o
  | .exit, c, s, o => s.Live c ∧ Guarded (ExitPreC k s c) (exitEffC s c) o
  | op, c, s, o => ViewStep (op.Step k) c s o

/-- C2: the `K.Satisfiable` obligation of `alloc` (Spec 1 §71) executed by `c`
is evaluated on the view of `c`: an `ok` outcome entails it. -/
theorem alloc_ok_satisfiable {k : K} {c pr ow : Nat} {ls : LocalShape} {s s' : SC}
    (h : opStepC k (.alloc pr ow ls) c s (.ok s')) : k.Satisfiable pr ls (s.view c) := by
  obtain ⟨-, o₃, hR, ho⟩ := h
  change AllocStep k pr ow ls (s.view c) o₃ at hR
  cases hR with
  | ok _ hsat => exact hsat
  | fail => cases ho
  | reject => cases ho

/-- C2: a `fail` outcome of `alloc` (Spec 1 §71) executed by `c` entails that
`K.Satisfiable` fails on the view of `c`. -/
theorem alloc_fail_unsatisfiable {k : K} {c pr ow : Nat} {ls : LocalShape} {s : SC}
    (h : opStepC k (.alloc pr ow ls) c s .fail) : ¬ k.Satisfiable pr ls (s.view c) := by
  obtain ⟨-, o₃, hR, ho⟩ := h
  change AllocStep k pr ow ls (s.view c) o₃ at hR
  cases hR with
  | ok => cases ho
  | fail _ hsat => exact hsat
  | reject => cases ho

/-! ## `spawn` (C4, on Spec 1 §72) -/

/-- Effect of `spawn` executed by `c` (C4 effect): a new live context of identity `|C|` whose
stack is the fresh frame `nF`, parented to the creating frame; the locals of the new frame and
their root authorities, and the yielding of the parameters, are the effects of Spec 1 §72 on the
view of `c`. -/
def spawnEff (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) : SC :=
  { s.set (enterEff (s.view c) ps ls) with
    C := s.C ++ [⟨[s.nF], .live, (s.stk c).head?⟩] }

/-- Preconditions of `spawn` without transmitted value (C4.1–C4.5): the clauses of `EnterPre`
(Spec 1 §72, `Ern.MemoryModel.Access.Ops`) re-indexed as in `EnterPreC`, with O6.3 read from the
current frame of the new context. C4.2 (fresh identities) and C4.4 (yield without duplication)
hold by construction of `spawnEff`; C4.6 concerns `spawn` with a value
(`Ern.ConcurrencyModel.SpawnValue`); the preservation obligations of C4 are theorems, not
preconditions. -/
structure SpawnPre (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) : Prop where
  /-- C4.1 (Spec 1 §72.1 re-indexed): the creating context and its current frame are live. -/
  creatorLive : s.stk c ≠ []
  /-- C4.3 (Spec 1 §72.1): every transmitted parameter is an active derived authority held by
  the creating frame. -/
  params : ∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y => y.active = true ∧
    y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False
  /-- C4.5 (Spec 1 §72.2): the locals of the new frame form a well-formed shape. -/
  localsOK : ShapeOK s.P.length ls.toShape
  /-- C4.5 (Spec 1 §72.3): origin protection in the final state, from the current frame of the
  new context. -/
  originHidden : ∀ p ∈ ps, ParamOriginHidden ((spawnEff s c ps ls).view s.C.length) p
  /-- C4.5 (Spec 1 §72.4): `AnchorOrderHeld` (on `ancestorC`) in the final state. -/
  anchorOrderHeld : AnchorOrderHeldC (spawnEff s c ps ls)

/-- Decidability of the preconditions of `spawn` (C4). -/
instance (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) :
    Decidable (SpawnPre s c ps ls) :=
  decidable_of_iff (s.stk c ≠ [] ∧ (∀ a ∈ ps, OptP ((s.view c).A[a]?) (fun y =>
      y.active = true ∧ y.holder = .frame (s.view c).top ∧ y.origin ≠ none) False) ∧
    ShapeOK s.P.length ls.toShape ∧
    (∀ p ∈ ps, ParamOriginHidden ((spawnEff s c ps ls).view s.C.length) p) ∧
    AnchorOrderHeldC (spawnEff s c ps ls))
    ⟨fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩, fun ⟨a, b, c, d, e⟩ => ⟨a, b, c, d, e⟩⟩

/-- `spawn` executed by `c` (C4): `ok` or `reject`; no outcome if `c` is not live. -/
def SpawnStep (s : SC) (c : Nat) (ps : List Nat) (ls : LocalShape) (o : Outcome3 SC) : Prop :=
  s.Live c ∧ Guarded (SpawnPre s c ps ls) (spawnEff s c ps ls) o

/-! ## `terminate` (C7, on Spec 1 §73) -/

/-- Effect of `terminate` executed by `c` (C7): the effect of Spec 1 §73 on the view of `c`
for its initial frame `f`, whose surviving frames are the other live frames; `c` leaves the
live-context set with the completed lifecycle state; the context-initial frames whose parent is
`f` are reparented to the parent of `f` (C7, C6 effect). -/
def termEffC (s : SC) (c : Nat) : SC :=
  { s.set (exitEff (s.view c)) with
    C := reparent (s.C.modify c fun x => { x with stack := [], life := .done })
      ((s.stk c).headD 0) ((s.ctxParent c).getD 0) }

/-- Preconditions of `terminate` executed by `c` (C7: the O7 validity requirements applied to
the initial frame of a terminating non-initial context, after its nested call frames have
ended). -/
structure TermPre (k : K) (s : SC) (c : Nat) : Prop where
  /-- C7: a non-initial context (C3: the base frame never exits). -/
  nonInitial : c ≠ 0
  /-- C7: the nested call frames have ended; only the initial frame remains. -/
  initialOnly : (s.stk c).length = 1
  /-- Spec 1 §73.1 re-indexed: the initial frame has a surviving parent. -/
  hasParent : OptP (s.ctxParent c) (fun p => p ∈ s.frames ∧ p ∉ s.stk c) False
  /-- Spec 1 §73.2, §73.4, §73.5: every anchor of a place usable after the exit has a surviving
  authority among itself and its origins. -/
  anchors : ∀ q ∈ List.range s.P.length, ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
    ∀ x ∈ s.D q, firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x) ≠ none
  /-- Spec 1 §73.4: every surviving derived authority has a surviving active origin. -/
  origins : ∀ a ∈ List.range s.A.length, Survives (s.view c) (s.view c).F.tail a →
    (s.view c).org a ≠ none → firstSurv (s.view c) (s.view c).F.tail ((s.view c).ancs a) ≠ none
  /-- Spec 1 §73.3: no leaf of a place that dies with the frame is pinned. -/
  notPinned : ∀ q ∈ List.range s.P.length, (s.view c).Usable q →
    ¬ ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
    ∀ l ∈ footprint s.P q, (s.view c).pin l = false ∧ ¬ k.Pinned l
  /-- Spec 1 §73.5 re-indexed: `AnchorOrderHeld` (on `ancestorC`) in the resulting state. -/
  anchorOrderHeld : AnchorOrderHeldC (termEffC s c)

/-- Decidability of the preconditions of `terminate` (C7). -/
instance (k : K) [DecidablePred k.Pinned] (s : SC) (c : Nat) : Decidable (TermPre k s c) :=
  decidable_of_iff (c ≠ 0 ∧ (s.stk c).length = 1 ∧
    OptP (s.ctxParent c) (fun p => p ∈ s.frames ∧ p ∉ s.stk c) False ∧
    (∀ q ∈ List.range s.P.length, ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
      ∀ x ∈ s.D q, firstSurv (s.view c) (s.view c).F.tail (x :: (s.view c).ancs x) ≠ none) ∧
    (∀ a ∈ List.range s.A.length, Survives (s.view c) (s.view c).F.tail a →
      (s.view c).org a ≠ none → firstSurv (s.view c) (s.view c).F.tail ((s.view c).ancs a) ≠ none) ∧
    (∀ q ∈ List.range s.P.length, (s.view c).Usable q →
      ¬ ({ s.view c with F := (s.view c).F.tail } : S3).Usable q →
      ∀ l ∈ footprint s.P q, (s.view c).pin l = false ∧ ¬ k.Pinned l) ∧
    AnchorOrderHeldC (termEffC s c))
    ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩,
     fun ⟨a, b, c, d, e, f, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

/-- `terminate` executed by `c` (C7): `ok` or `reject`; no outcome if `c` is not live. -/
def TermStep (k : K) (s : SC) (c : Nat) (o : Outcome3 SC) : Prop :=
  s.Live c ∧ Guarded (TermPre k s c) (termEffC s c) o

/-! ## `join` (C8) -/

/-- `join d` executed by `c` (C8): `reject` when `d` is unknown to the execution (no context
has identity `d`, identities being the indices of `C`); `ok` with the state unchanged when `d` has
the completed lifecycle state; no outcome while `d` is live (C8: awaiting completion is not an
`Outcome3` result). -/
inductive JoinStep (s : SC) (c d : Nat) : Outcome3 SC → Prop where
  | ok : s.Live c → OptP (s.C[d]?) (fun x => x.life = .done) False → JoinStep s c d (.ok s)
  | reject : s.Live c → s.C[d]? = none → JoinStep s c d .reject

/-! ## Concurrent kernel steps -/

/-- One `ok` transition of the concurrent kernel without synchronization (C2, C4, C6–C8):
an inherited operation O1–O16 executed by a context, `spawn`, `terminate` or `join`. -/
inductive CStep (k : K) : SC → SC → Prop where
  | kernel {s s' : SC} {c : Nat} {op : KernelOp} : opStepC k op c s (.ok s') → CStep k s s'
  | spawn {s s' : SC} {c : Nat} {ps : List Nat} {ls : LocalShape} :
      SpawnStep s c ps ls (.ok s') → CStep k s s'
  | terminate {s s' : SC} {c : Nat} : TermStep k s c (.ok s') → CStep k s s'
  | join {s s' : SC} {c d : Nat} : JoinStep s c d (.ok s') → CStep k s s'

end Ern.ConcurrencyModel
