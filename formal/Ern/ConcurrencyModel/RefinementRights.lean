import Ern.ConcurrencyModel.Inventory
import Ern.ConcurrencyModel.RefinementAuthority

/-!
# Theorem 9e, the rights read existentially (Spec 1 §43; C22.6, theorem 6)

`usesOf` lists the authorities that a step uses as means of access or as sources of new means of
access (`RefinementArena.usedAuth`). The rights that a step reads existentially are not in it: the
rights over a place (Spec 1 §43 `HasRight`), the holder rights (§62.2), the administration right
(§36 `MetaRight`), the controller-access rights (C13.11, C14.3, C17.4, C18.4), and the holder chain
of every exercise (§43). This module states that every authority on which such a right rests is
active in the state where the right is read, for every right of the inventory of theorem 6
(`RightsRead`, C22.6).

What rests on what (Spec 1 §43; C22.6 "the entire authority-holder chain"):

* the exercise of `a` at `m` (`ExercisableAt`) rests on `a` and, along its holder chain, on every
  authority exercisable at `m` with sufficient effective mode over the place holding it
  (`RestsOn`, `ExerciseBasis`);
* `HasRight(m, q)` rests on every authority that grounds it (`Grounds`, Spec 1 §63.4: "the
  exercisable authority on which that right rests") and on the holder chain of its exercise
  (`RightBasis`);
* the holder right on a place (Spec 1 §62.2) and `MetaRight` (§36) are rights over a place
  (`HolderBasis`, `MetaBasis`);
* the controller-access right of C14.3 rests on every authority exercisable at `Observe` by the
  requesting frame with a present effective mode on the controller, and on its holder chain
  (`CtrlBasis`).

The origin chain is not counted: a right does not rest on the origins of its grounding authority,
which may be inactive (C16.2: "an inactive recorded grant with surviving derived authorities").

* `rights_founded_active`: for every `ok` labelled step, every founding authority of a right it
  reads is active in the state where the right is read;
* `exerciseBasis_self`, `rightBasis_of`, `holderBasis_of`, `metaBasis_of`, `ctrlBasis_of`: every
  such right, when it holds, has a founding authority (the holder right on a frame excepted).
-/

namespace Ern.ConcurrencyModel

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## What a right rests on (Spec 1 §43; C22.6) -/

/-- The exercise of `a` at mode `m` in `t` rests on the authority `j` (Spec 1 §43: "The latter
clause is recursive along the holder chain"; C22.6: the authority-holder chain of an exercisability
judgment): `j` is `a`, or `a` is held by a place `p` and the exercise rests on `j` through an
authority `b` exercisable at `m` whose effective mode permits `m` on every leaf of `p`. -/
inductive RestsOn (t : S3) (m : Mode) : Nat → Nat → Prop where
  | self (a : Nat) : RestsOn t m a a
  | held {a p b j : Nat} {y : Authority} : t.A[a]? = some y → y.holder = .place p →
      t.ExercisableAt b m → (∀ l ∈ footprint t.P p, Allows (effective t b l) m) →
      RestsOn t m b j → RestsOn t m a j

/-- The exercise `ExercisableAt(t, a, m)` (Spec 1 §43) holds and rests on `j`. -/
def ExerciseBasis (t : S3) (a : Nat) (m : Mode) (j : Nat) : Prop :=
  t.ExercisableAt a m ∧ RestsOn t m a j

/-- `j` founds the right `HasRight(t, m, q)` (Spec 1 §43, §63.4): some authority grounding the
right (`Grounds`) has an exercise at `m` that rests on `j`. -/
def RightBasis (t : S3) (m : Mode) (q j : Nat) : Prop :=
  ∃ g, Grounds t m q g ∧ RestsOn t m g j

/-- `j` founds the holder right of the current frame of `t` on the holder `h` (Spec 1 §62.2): for a
place, a founding authority of `HasRight(t, Modify, p)`; a frame holder rests on no authority. -/
def HolderBasis (t : S3) : Holder → Nat → Prop
  | .frame _, _ => False
  | .place p, j => RightBasis t .modify p j

/-- `j` founds `MetaRight(t, E)` (Spec 1 §36, §77.1, §78.1): a founding authority of the right over
the arena value. -/
def MetaBasis (t : S3) (E : Arena.ArenaEntry) (j : Nat) : Prop :=
  OptP (Arena.arenaValue t E) (fun v => RightBasis t .modify v j) False

/-- `j` founds the controller-access right of the frame `f` for the entry `e` in `s` (C14.3,
`CtrlRight`, under Spec 1 §68.2): some authority exercisable at `Observe` by `f`, with a present
effective mode on the controller, has an exercise that rests on `j`, in the state `s.viewAt f`
where `CtrlRight` reads it. -/
def CtrlBasis (L : MutexLayout) (s : SC) (e : SyncEntry) (f j : Nat) : Prop :=
  OptP (ControlOf L s e) (fun ctl => ∃ a ∈ List.range s.A.length,
    (s.viewAt f).ExercisableAt a .observe ∧ effective s.flat a ctl ≠ none ∧
      RestsOn (s.viewAt f) .observe a j) False

/-- The founding authorities of the rights of the transfer phases of the by-value composite (C5.2,
`ValRights`): for each phase, in the state where it starts, the founding authorities of the source
right (the grounding authority of §63.4 is one of them). -/
def ValBasis (c : Nat) : SC → List (Nat × Nat) → S3 → Nat → Prop
  | _, [], _, _ => False
  | u, v :: vs, t, j => (t = u.view c ∧ RightBasis t .modify v.1 j) ∨
      ValBasis c (transferEffC u c v.1 v.2) vs t j

/-- The authorities that found the rights of the inventory of theorem 6 read by the step `lbl` from
`st` (C22.6, `RightsRead`), each with the state `t` where the step reads the right: `Founds ks L st
lbl t j` says that `j` founds, in `t`, a right of `RightsRead ks L st lbl`. It mirrors `RightsRead`
case by case, the intermediate and resulting states included (`storeEff` for `store`;
`prospectiveUnlock` for `unlock`; `issueMid` and the `storeEff` after it for `issue`; `resetMid` for
`reset`; each transfer phase for the by-value composite). In `transfer`, `endUse` and `free`, the
authority grounding the access clause (Spec 1 §63.4, §69.2, §70.3) grounds the place right, so it
is among the founding authorities of that right. The labels that read no right
(`enterFrame`, `exitFrame`, `spawn`, `terminate`, `join`) have none, and a holder right on a frame
(Spec 1 §62.2) rests on no authority. -/
def Founds (ks : KShared) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) :
    Label → S3 → Nat → Prop
  | .kernel c (.derive a _ m), t, j => t = st.1.view c ∧ ExerciseBasis t a m j
  | .kernel c (.split a _), t, j => t = st.1.view c ∧ ExerciseBasis t a .modify j
  | .kernel c (.release a), t, j =>
      t = st.1.view c ∧ OptP (st.1.A[a]?) (fun y => HolderBasis t y.holder j) False
  | .kernel c (.transfer src dst), t, j =>
      t = st.1.view c ∧ (RightBasis t .modify src j ∨ RightBasis t .modify dst j)
  | .kernel c (.depend q _), t, j => t = st.1.view c ∧ RightBasis t .modify q j
  | .kernel _ (.enter _ _), _, _ => False
  | .kernel _ .exit, _, _ => False
  | .kernel c (.read a _), t, j => t = st.1.view c ∧ ExerciseBasis t a .observe j
  | .kernel c (.write a _), t, j => t = st.1.view c ∧ ExerciseBasis t a .modify j
  | .kernel c (.writeShared a _), t, j => t = st.1.view c ∧ ExerciseBasis t a .observe j
  | .kernel c (.pin p), t, j => t = st.1.view c ∧ RightBasis t .modify p j
  | .kernel c (.unpin o), t, j =>
      t = st.1.view c ∧ OptP (st.1.pins[o]?) (fun ob => RightBasis t .modify ob.place j) False
  | .kernel c (.endUse p), t, j => t = st.1.view c ∧ RightBasis t .modify p j
  | .kernel c (.free p _), t, j => t = st.1.view c ∧ RightBasis t .modify p j
  | .kernel c (.alloc pr ow _), t, j => t = st.1.view c ∧ (RightBasis t .modify pr j ∨
      (∃ via ∈ List.range t.A.length, WriteSharedPre ks.toK t via (footprint t.P pr) ∧
        RestsOn t .observe via j) ∨ RightBasis t .modify ow j)
  | .kernel c (.store a p), t, j =>
      (t = st.1.view c ∨ t = storeEff (st.1.view c) a p) ∧ RightBasis t .modify p j
  | .spawn _ _ _, _, _ => False
  | .terminate _, _, _ => False
  | .join _ _, _, _ => False
  | .deriveSync c g, t, j => t = st.1.viewAt (st.1.view c).top ∧
      ∃ e ∈ st.2.1, e.guarded = g ∧ CtrlBasis L st.1 e (st.1.view c).top j
  | .newMutex c g, t, j => t = st.1.view c ∧ (ExerciseBasis t g .modify j ∨
      OptP (ControlOf L st.1 ⟨g, none⟩) (fun ctl => ∃ a ∈ List.range st.1.A.length,
        t.ExercisableAt a .modify ∧ effective t a ctl = some .modify ∧
          (∀ b ∈ List.range st.1.A.length, b ≠ a → effective t b ctl = none) ∧
          RestsOn t .modify a j) False)
  | .acquire c i, t, j => t = st.1.viewAt (st.1.view c).top ∧
      OptP (st.2.1[i]?) (fun e => CtrlBasis L st.1 e (st.1.view c).top j ∨
        ∃ e' ∈ st.2.1, e'.guarded = e.guarded ∧ CtrlBasis L st.1 e' (st.1.view c).top j) False
  | .unlock c i, t, j => OptP (st.2.1[i]?) (fun e => OptP e.grant (fun g =>
      (t = st.1.view c ∧ OptP (st.1.A[g]?) (fun y => HolderBasis t y.holder j) False) ∨
      (t = st.1.viewAt (st.1.view c).top ∧ CtrlBasis L st.1 e (st.1.view c).top j) ∨
      (t = (prospectiveUnlock st.1 c g).viewAt (st.1.view c).top ∧
        CtrlBasis L (prospectiveUnlock st.1 c g) e (st.1.view c).top j)) False) False
  | .resetLock c i, t, j => OptP (st.2.1[i]?) (fun e =>
      (t = st.1.view c ∧ ExerciseBasis t e.guarded .modify j) ∨
      (t = st.1.viewAt (st.1.view c).top ∧ CtrlBasis L st.1 e (st.1.view c).top j)) False
  | .spawnVal c _ ls vs, t, j => ValBasis c (spawnCreate st.1 c ls) vs t j
  | .newArena c storage internal, t, j => t = st.1.view c ∧
      (RightBasis t .modify storage j ∨ ExerciseBasis t internal .modify j)
  | .issue c i region dst, t, j => OptP (st.2.2[i]?) (fun E =>
      (t = st.1.view c ∧ (MetaBasis t E j ∨ RightBasis t .modify dst j ∨
        ExerciseBasis t E.internal .modify j)) ∨
      (t = (issueMid st.1 c E region).view c ∧ RightBasis t .modify dst j) ∨
      (t = storeEff ((issueMid st.1 c E region).view c) st.1.A.length dst ∧
        RightBasis t .modify dst j)) False
  | .reset c i, t, j => OptP (st.2.2[i]?) (fun E =>
      (t = st.1.view c ∧ ExerciseBasis t E.internal .modify j) ∨
      (t = (resetMid st.1 c E).view c ∧
        OptP ((resetMid st.1 c E).A[st.1.A.length]?) (fun y => HolderBasis t y.holder j)
          False)) False
  | .readShared c a _ _ _, t, j => t = st.1.view c ∧ ExerciseBasis t a .observe j
  | .writeShared c a _ _ _, t, j => t = st.1.view c ∧ ExerciseBasis t a .observe j
  | .cas c a _ _ _ _, t, j => t = st.1.view c ∧ ExerciseBasis t a .observe j

/-! ## Every founding authority is active (Spec 1 §43) -/

/-- Every authority on which an exercise rests is active (Spec 1 §43: an exercisable authority is
active, and so is every authority of its holder chain). -/
theorem restsOn_active {t : S3} {m : Mode} {a j : Nat} (hr : RestsOn t m a j)
    (ha : t.ExercisableAt a m) : t.Active j := by
  induction hr with
  | self => exact RefinementArena.active_of_exercisable ha
  | held _ _ hb _ _ ih => exact ih hb

/-- The founding authorities of an exercise are active (Spec 1 §43). -/
theorem exerciseBasis_active {t : S3} {a : Nat} {m : Mode} {j : Nat}
    (h : ExerciseBasis t a m j) : t.Active j :=
  restsOn_active h.2 h.1

/-- The founding authorities of a right over a place are active (Spec 1 §43). -/
theorem rightBasis_active {t : S3} {m : Mode} {q j : Nat} (h : RightBasis t m q j) :
    t.Active j :=
  let ⟨_, hg, hr⟩ := h; restsOn_active hr hg.2.1

/-- The founding authorities of a holder right are active (Spec 1 §62.2, §43). -/
theorem holderBasis_active {t : S3} {h : Holder} {j : Nat} (hb : HolderBasis t h j) :
    t.Active j := by
  cases h with
  | frame => exact hb.elim
  | place p => exact rightBasis_active hb

/-- The founding authorities of `MetaRight` are active (Spec 1 §36, §43). -/
theorem metaBasis_active {t : S3} {E : Arena.ArenaEntry} {j : Nat} (h : MetaBasis t E j) :
    t.Active j := by
  unfold MetaBasis OptP at h
  split at h
  · exact rightBasis_active h
  · exact h.elim

/-- The founding authorities of a controller-access right are active in the state where it is
read (C14.3, Spec 1 §43). -/
theorem ctrlBasis_active {L : MutexLayout} {s : SC} {e : SyncEntry} {f j : Nat}
    (h : CtrlBasis L s e f j) : (s.viewAt f).Active j := by
  unfold CtrlBasis OptP at h
  split at h
  · obtain ⟨a, -, ha, -, hr⟩ := h
    exact restsOn_active hr ha
  · exact h.elim

/-- The founding authorities of the rights of the transfer phases are active in the state where
each phase starts (C5.2, Spec 1 §43). -/
theorem valBasis_active {c : Nat} :
    ∀ (u : SC) (vs : List (Nat × Nat)) {t : S3} {j : Nat}, ValBasis c u vs t j → t.Active j
  | _, [], _, _, h => h.elim
  | u, v :: vs, _, _, h => by
    rcases h with ⟨-, hb⟩ | h
    · exact rightBasis_active hb
    · exact valBasis_active _ vs h

/-- A property of an optional value read at `some` (Spec 1 §38). -/
private theorem optP_some {α : Type} {o : Option α} {P : α → Prop} (h : OptP o P False) :
    ∃ y, o = some y ∧ P y := by
  unfold OptP at h
  split at h
  · exact ⟨_, rfl, h⟩
  · exact h.elim

/-- **Theorem 9e**, the rights read existentially (Spec 1 §43; C13.11, C14.3, C17.4, C18.4, C22.6;
theorem 6): for every `ok` labelled step, the rights of the inventory of theorem 6 hold
(`rights_inventory`), and every authority that founds one of them (`Founds`: the authority it is
grounded on and, along the holder chain of its exercise, every authority that exercise rests on) is
active in the state where the step reads that right, the intermediate and resulting states
included. Together with `usesOf_active`, every authority that an `ok` step relies on, as a means of
access or through a right it reads, is active where it is relied on. Fragment: every labelled step,
every state.

The activity comes from Spec 1 §43 (an exercisable authority is active, along its holder chain);
the step gives that the rights hold. The origin chain of a grounding authority is not counted
(C16.2). The physical accesses that these rights justify are not modelled (`OB-C05`, `OB-C20`). -/
theorem rights_founded_active {ks : KShared} {L : MutexLayout} {lbl : Label}
    {st st' : SC × SyncReg × ArenaReg} (h : LStep ks L lbl st st') :
    RightsRead ks L st lbl ∧ ∀ t j, Founds ks L st lbl t j → t.Active j := by
  refine ⟨rights_inventory.1 _ _ _ h, fun t j hf => ?_⟩
  cases lbl with
  | kernel c op =>
    cases op with
    | derive => exact exerciseBasis_active hf.2
    | split => exact exerciseBasis_active hf.2
    | release a =>
      obtain ⟨y, -, hb⟩ := optP_some hf.2
      exact holderBasis_active hb
    | transfer => exact hf.2.elim rightBasis_active rightBasis_active
    | depend => exact rightBasis_active hf.2
    | enter => exact hf.elim
    | exit => exact hf.elim
    | read => exact exerciseBasis_active hf.2
    | write => exact exerciseBasis_active hf.2
    | writeShared => exact exerciseBasis_active hf.2
    | pin => exact rightBasis_active hf.2
    | unpin =>
      obtain ⟨ob, -, hb⟩ := optP_some hf.2
      exact rightBasis_active hb
    | endUse => exact rightBasis_active hf.2
    | free => exact rightBasis_active hf.2
    | alloc =>
      rcases hf.2 with hb | ⟨via, -, hw, hr⟩ | hb
      · exact rightBasis_active hb
      · exact restsOn_active hr hw.exercisable
      · exact rightBasis_active hb
    | store => exact rightBasis_active hf.2
  | spawn => exact hf.elim
  | terminate => exact hf.elim
  | join => exact hf.elim
  | deriveSync =>
    obtain ⟨rfl, e, -, -, hb⟩ := hf
    exact ctrlBasis_active hb
  | newMutex =>
    obtain ⟨rfl, hb | hb⟩ := hf
    · exact exerciseBasis_active hb
    · obtain ⟨ctl, -, a, -, ha, -, -, hr⟩ := optP_some hb
      exact restsOn_active hr ha
  | acquire =>
    obtain ⟨rfl, hb⟩ := hf
    obtain ⟨e, -, hb | ⟨e', -, -, hb⟩⟩ := optP_some hb
    · exact ctrlBasis_active hb
    · exact ctrlBasis_active hb
  | unlock =>
    obtain ⟨e, -, hb⟩ := optP_some hf
    obtain ⟨g, -, ⟨-, hh⟩ | ⟨ht, hc⟩ | ⟨ht, hc⟩⟩ := optP_some hb
    · obtain ⟨y, -, hy⟩ := optP_some hh
      exact holderBasis_active hy
    · rw [ht]; exact ctrlBasis_active hc
    · rw [ht]; exact ctrlBasis_active hc
  | resetLock =>
    obtain ⟨e, -, ⟨-, hx⟩ | ⟨ht, hc⟩⟩ := optP_some hf
    · exact exerciseBasis_active hx
    · rw [ht]; exact ctrlBasis_active hc
  | spawnVal => exact valBasis_active _ _ hf
  | newArena => exact hf.2.elim rightBasis_active exerciseBasis_active
  | issue =>
    obtain ⟨E, -, ⟨-, hb | hb | hb⟩ | ⟨-, hb⟩ | ⟨-, hb⟩⟩ := optP_some hf
    · exact metaBasis_active hb
    · exact rightBasis_active hb
    · exact exerciseBasis_active hb
    · exact rightBasis_active hb
    · exact rightBasis_active hb
  | reset =>
    obtain ⟨E, -, ⟨-, hb⟩ | ⟨-, hb⟩⟩ := optP_some hf
    · exact exerciseBasis_active hb
    · obtain ⟨y, -, hb⟩ := optP_some hb
      exact holderBasis_active hb
  | readShared => exact exerciseBasis_active hf.2
  | writeShared => exact exerciseBasis_active hf.2
  | cas => exact exerciseBasis_active hf.2

/-! ## The founding authorities exist (non-vacuity)

Every right of the inventory, when it holds, has a founding authority, except the holder right on
a frame, which is the current frame itself (Spec 1 §62.2) and rests on no authority. So
`rights_founded_active` does not hold through an empty set of founding authorities. -/

/-- An exercise rests on its own authority (Spec 1 §43). -/
theorem exerciseBasis_self {t : S3} {a : Nat} {m : Mode} (h : t.ExercisableAt a m) :
    ExerciseBasis t a m a :=
  ⟨h, .self a⟩

/-- A right over a place has a founding authority: the authority grounding it (Spec 1 §43,
§63.4). -/
theorem rightBasis_of {t : S3} {m : Mode} {q : Nat} (h : HasRight t m q) :
    ∃ j, RightBasis t m q j :=
  let ⟨g, hg, hx, hall⟩ := h; ⟨g, g, ⟨hg, hx, hall⟩, .self g⟩

/-- A controller-access right has a founding authority (C14.3). -/
theorem ctrlBasis_of {L : MutexLayout} {s : SC} {e : SyncEntry} {f : Nat}
    (h : CtrlRight L s e f) : ∃ j, CtrlBasis L s e f j := by
  unfold CtrlRight OptP at h
  unfold CtrlBasis OptP
  split at h
  · obtain ⟨a, ha, hx, he⟩ := h
    exact ⟨a, a, ha, hx, he, .self a⟩
  · exact h.elim

/-- A holder right on a place has a founding authority (Spec 1 §62.2, §43). A holder right on a
frame (the current frame itself) rests on no authority. -/
theorem holderBasis_of {t : S3} {p : Nat} (h : HolderRight t (.place p)) :
    ∃ j, HolderBasis t (.place p) j :=
  rightBasis_of h

/-- `MetaRight` has a founding authority (Spec 1 §36, §43). -/
theorem metaBasis_of {t : S3} {E : Arena.ArenaEntry} (h : Arena.MetaRight t E) :
    ∃ j, MetaBasis t E j := by
  unfold Arena.MetaRight OptP at h
  unfold MetaBasis OptP
  split at h
  · exact rightBasis_of h
  · exact h.elim

end Ern.ConcurrencyModel
