import Ern.Concurrency.Encap5C

/-!
# Exclusion extended to the rights over places

Brief of milestone 4, "étendre l'exclusion aux droits sur les places". `ChainExcl`
(`Ern.Concurrency.Encap5C`) reads the authority argument of `derive`, `split`, `read`, `write` and
`writeShared`; it does not read the right over a place (`HasRight`, Spec 1 §43) of the other
operations, and W-GS (`corpus-spec2-m3.md` v6 §2 sexies) writes the protected data without the lock
through such a right. `PlaceExcl` requires the right premises of the preconditions to hold without
a live `guarded` on the holder chain (`HasRight5`). It is a proposition of the brief, tested here
and not decided; the existing definitions, `ChainExcl` and `Encap5C` included, are unchanged.
-/

namespace Ern.Concurrency

open Ern.MemoryModel Ern.MemoryModel.Access

/-! ## Rights over places without a live `guarded` -/

/-- `HasRight(s, m, q)` (Spec 1 §43) read from the current frame of `c`, with `Exer5` in place of
`ExercisableAt` (brief of milestone 4, task 2): some authority exercisable by a holder chain without
a live `guarded` has, over every leaf of `q`'s footprint, an effective mode permitting `m`. -/
def HasRight5 (st : SC × SyncReg) (c : Nat) (m : Mode) (q : Nat) : Prop :=
  ∃ a ∈ List.range st.1.A.length, Exer5 st.1 st.2 c a m ∧
    ∀ l ∈ footprint st.1.P q, Allows (effective st.1.flat a l) m

/-- Decidability of `HasRight5`. -/
instance (st : SC × SyncReg) (c : Nat) (m : Mode) (q : Nat) : Decidable (HasRight5 st c m q) := by
  unfold HasRight5; infer_instance

/-- `HolderRight` (Spec 1 §62.2) with `HasRight5` in its place case. -/
def HolderRight5 (st : SC × SyncReg) (c : Nat) : Holder → Prop
  | .frame _ => True
  | .place p => HasRight5 st c .modify p

/-- Decidability of `HolderRight5`. -/
instance (st : SC × SyncReg) (c : Nat) (h : Holder) : Decidable (HolderRight5 st c h) := by
  cases h <;> unfold HolderRight5 <;> infer_instance

/-- `CtrlRight` (WC5 C14.3, read with the access condition of Spec 1 §68.2) from the current frame
of `c`, with `Exer5` in place of `ExercisableAt`. -/
def CtrlRight5 (L : MutexLayout) (st : SC × SyncReg) (e : SyncEntry) (c : Nat) : Prop :=
  OptP (ControlOf L st.1 e) (fun ctl => ∃ a ∈ List.range st.1.A.length,
    Exer5 st.1 st.2 c a .observe ∧ effective st.1.flat a ctl ≠ none) False

/-- Decidability of `CtrlRight5`. -/
instance (L : MutexLayout) (st : SC × SyncReg) (e : SyncEntry) (c : Nat) :
    Decidable (CtrlRight5 L st e c) := by
  unfold CtrlRight5; infer_instance

/-- `MetaRight` (Spec 1 §36, §77.1, §78.1) with `HasRight5` over the arena value, when the arena
value exists. -/
def MetaRight5 (st : SC × SyncReg) (c : Nat) (E : Arena.ArenaEntry) : Prop :=
  OptP (Arena.arenaValue st.1.flat E) (fun v => HasRight5 st c .modify v) True

/-- Decidability of `MetaRight5`. -/
instance (st : SC × SyncReg) (c : Nat) (E : Arena.ArenaEntry) : Decidable (MetaRight5 st c E) := by
  unfold MetaRight5; infer_instance

/-- The right premise of each transfer phase of the by-value composite (WC5 C5.2, C5 item 1, Spec 1
§63.1: `ValTransferPre.srcRight`) as `HasRight5`, each on the state produced by the earlier
transfers, in the declared order. -/
def ValRights5 (reg : SyncReg) (c : Nat) : SC → List (Nat × Nat) → Prop
  | _, [] => True
  | t, v :: vs => HasRight5 (t, reg) c .modify v.1 ∧ ValRights5 reg c (transferEffC t c v.1 v.2) vs

/-- Decidability of `ValRights5`. -/
instance instDecidableValRights5 (reg : SyncReg) (c : Nat) :
    (t : SC) → (vs : List (Nat × Nat)) → Decidable (ValRights5 reg c t vs)
  | _, [] => isTrue trivial
  | t, v :: vs =>
    haveI := instDecidableValRights5 reg c (transferEffC t c v.1 v.2) vs
    inferInstanceAs (Decidable (HasRight5 (t, reg) c .modify v.1 ∧ _))

/-! ## The extended exclusion -/

/-- `PlaceExcl` (brief of milestone 4, task 2): each right premise over a place of the precondition
holds as `HasRight5` on the same place, in the state where the premise is read:
`release` (Spec 1 §62.2, place-held case), `transfer` (§63.1, source and destination), `depend`
(§64), `store` (§65.2 before, §65.5 in the resulting state), `endUse` (§69), `free` (§70), `alloc`
(§71.2 provider, with the `writeShared` branch of §68 exercised by `Exer5`; §71.3 owner), `pin`
(§74), `unpin` (§75); `issue` and `reset`, `MetaRight` over the arena value (§36, §77.1, §78.1);
`spawnVal`, the source right of each transfer phase (WC5 C5.2); `acquire`, the controller access of
WC5 C14.3 (`CtrlRight5`). The other labels are unconstrained. -/
def PlaceExcl (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) : Label → Prop
  | .kernel c (.release a) => OptP (st.1.A[a]?) (fun y => HolderRight5 (st.1, st.2.1) c y.holder) True
  | .kernel c (.transfer src dst) =>
      HasRight5 (st.1, st.2.1) c .modify src ∧ HasRight5 (st.1, st.2.1) c .modify dst
  | .kernel c (.depend q _) => HasRight5 (st.1, st.2.1) c .modify q
  | .kernel c (.store a p) =>
      HasRight5 (st.1, st.2.1) c .modify p ∧ HasRight5 (storeEffC st.1 c a p, st.2.1) c .modify p
  | .kernel c (.endUse p) => HasRight5 (st.1, st.2.1) c .modify p
  | .kernel c (.free p _) => HasRight5 (st.1, st.2.1) c .modify p
  | .kernel c (.alloc pr ow _) =>
      (HasRight5 (st.1, st.2.1) c .modify pr ∨ ∃ via ∈ List.range st.1.A.length,
        WriteSharedPre k (st.1.view c) via (footprint st.1.P pr) ∧ Exer5 st.1 st.2.1 c via .observe) ∧
      HasRight5 (st.1, st.2.1) c .modify ow
  | .kernel c (.pin p) => HasRight5 (st.1, st.2.1) c .modify p
  | .kernel c (.unpin o) =>
      OptP (st.1.pins[o]?) (fun ob => HasRight5 (st.1, st.2.1) c .modify ob.place) True
  | .spawnVal c _ ls vs => ValRights5 st.2.1 c (spawnCreate st.1 c ls) vs
  | .acquire c i => OptP (st.2.1[i]?) (fun e => CtrlRight5 L (st.1, st.2.1) e c) True
  | .issue c i _ _ => OptP (st.2.2[i]?) (fun E => MetaRight5 (st.1, st.2.1) c E) True
  | .reset c i => OptP (st.2.2[i]?) (fun E => MetaRight5 (st.1, st.2.1) c E) True
  | _ => True

/-- Decidability of `PlaceExcl`. -/
instance (k : K) [DecidablePred k.SharedMutable] (L : MutexLayout) (st : SC × SyncReg × ArenaReg)
    (lbl : Label) : Decidable (PlaceExcl k L st lbl) := by
  unfold PlaceExcl; split <;> infer_instance

/-- `Encap5R` (brief of milestone 4, task 2): `Encap5C` and `PlaceExcl`. -/
def Encap5R (k : K) (L : MutexLayout) (st : SC × SyncReg × ArenaReg) (lbl : Label) : Prop :=
  Encap5C L (st.1, st.2.1) lbl ∧ PlaceExcl k L st lbl

/-- `EncapsulatedTrace5R`: a run every step of which satisfies `Encap5R` in the state where it is
taken. -/
inductive EncapsulatedTrace5R (k : K) (L : MutexLayout) :
    SC × SyncReg × ArenaReg → List Label → SC × SyncReg × ArenaReg → Prop where
  | nil {st : SC × SyncReg × ArenaReg} : EncapsulatedTrace5R k L st [] st
  | cons {st st₁ st₂ : SC × SyncReg × ArenaReg} {lbl : Label} {lbls : List Label} :
      Encap5R k L st lbl → LStep k L lbl st st₁ →
      EncapsulatedTrace5R k L st₁ lbls st₂ → EncapsulatedTrace5R k L st (lbl :: lbls) st₂

/-- Every `EncapsulatedTrace5R` is an `EncapsulatedTrace5C`: `cap5_compat`, `cap5_drop_own` (through
`encapsulatedTrace5C_imp`), `cap5_sound_C` and `handoff_loss_exists_C` (through `run5C_of_trace`)
apply to it. -/
theorem encapsulatedTrace5R_imp {k : K} {L : MutexLayout} {st st' : SC × SyncReg × ArenaReg}
    {lbls : List Label} (h : EncapsulatedTrace5R k L st lbls st') :
    EncapsulatedTrace5C k L st lbls st' := by
  induction h with
  | nil => exact .nil
  | cons he hs _ ih => exact .cons he.1 hs ih

/-- An `EncapsulatedTrace5R` extended by one step satisfying `Encap5R`. -/
theorem EncapsulatedTrace5R.snoc {k : K} {L : MutexLayout}
    {st st' st'' : SC × SyncReg × ArenaReg} {lbls : List Label} {lbl : Label}
    (h : EncapsulatedTrace5R k L st lbls st') (he : Encap5R k L st' lbl)
    (hs : LStep k L lbl st' st'') : EncapsulatedTrace5R k L st (lbls ++ [lbl]) st'' := by
  induction h with
  | nil => exact .cons he hs .nil
  | cons he' hs' _ ih => exact .cons he' hs' (ih he hs)

/-! ## Without a live entry -/

/-- Without a live entry, `HasRight` (Spec 1 §43) from the view of `c` is `HasRight5`. -/
theorem hasRight5_of_noLive {s : SC} {reg : SyncReg} {c q : Nat} {m : Mode}
    (hng : ∀ e ∈ reg, ¬ e.Live s) (h : HasRight (s.view c) m q) : HasRight5 (s, reg) c m q := by
  obtain ⟨a, ha, hx, hall⟩ := h
  exact ⟨a, ha, exer5_of_exercisable hng hx, hall⟩

/-- No entry becomes live in a state with the same authorities up to their holders (Spec 1 §42). -/
theorem noLive_skel {s s' : SC} {reg : SyncReg} (hs : SameSkel s.flat s'.flat)
    (hng : ∀ e ∈ reg, ¬ e.Live s) : ∀ e ∈ reg, ¬ e.Live s' :=
  fun e he hl => hng e he (hs.active.1 hl)

/-- No entry is live in the state after the creation phase of `spawn` (WC5 C4, C5 phase 1), when
every registered `guarded` identity exists (WC5 C21.6, `RegBound`): the creation keeps the former
authorities and appends the roots of the new locals. -/
theorem noLive_create {s : SC} {reg : SyncReg} {c : Nat} {ls : LocalShape}
    (hb : ∀ e ∈ reg, e.guarded < s.A.length) (hng : ∀ e ∈ reg, ¬ e.Live s) :
    ∀ e ∈ reg, ¬ e.Live (spawnCreate s c ls) := by
  intro e he ⟨y, hy, ha⟩
  have h : (spawnCreate s c ls).A[e.guarded]? = s.A[e.guarded]? := by
    have h0 : (s.view c).A[e.guarded]? = s.A[e.guarded]? := rfl
    show (enterEff (s.view c) [] ls).A[e.guarded]? = s.A[e.guarded]?
    rw [Ern.MemoryModel.Access.Frames.enter_lt (hb e he), h0]
    cases s.A[e.guarded]? <;> simp
  exact hng e he ⟨y, h ▸ hy, ha⟩

/-- Without a live entry, the source rights of the transfer phases (WC5 C5.2) hold as
`ValRights5`. -/
theorem valRights5_of_noLive {k : K} {fin : S3} {reg : SyncReg} {c : Nat} :
    ∀ (t : SC) (vs : List (Nat × Nat)), (∀ e ∈ reg, ¬ e.Live t) →
      ValTransfersPre k fin c t vs → ValRights5 reg c t vs
  | _, [], _, _ => trivial
  | t, v :: vs, hng, ⟨hp, hr⟩ =>
    ⟨hasRight5_of_noLive hng hp.srcRight, valRights5_of_noLive _ vs
      (noLive_skel (transfer_skel (t.view c) v.1 v.2) hng) hr⟩

/-- Without a live entry, `MetaRight` (Spec 1 §36) from the view of `c` gives `MetaRight5`. -/
theorem metaRight5_of_noLive {s : SC} {reg : SyncReg} {c : Nat} {E : Arena.ArenaEntry}
    (hng : ∀ e ∈ reg, ¬ e.Live s) (h : Arena.MetaRight (s.view c) E) : MetaRight5 (s, reg) c E := by
  have h0 : Arena.arenaValue (s.view c) E = Arena.arenaValue s.flat E := rfl
  unfold Arena.MetaRight at h; unfold MetaRight5
  rw [h0] at h
  revert h
  cases Arena.arenaValue s.flat E with
  | none => intro; trivial
  | some v => exact hasRight5_of_noLive hng

/-- Without a live entry, the exercise of `internal` at `Modify` from the view of `c` (Spec 1 §43,
§60.1 for the `derive` of `reset`, Spec 1 §78) gives `MetaRight5`: when `internal` is held by a
place, an authority exercisable at `Modify` has effective `Modify` over that place. -/
theorem metaRight5_of_exercisable {s : SC} {reg : SyncReg} {c : Nat} {E : Arena.ArenaEntry}
    (hng : ∀ e ∈ reg, ¬ e.Live s) (hx : (s.view c).ExercisableAt E.internal .modify) :
    MetaRight5 (s, reg) c E := by
  unfold MetaRight5 Arena.arenaValue
  cases hy : s.flat.A[E.internal]? with
  | none => trivial
  | some y =>
    dsimp only
    cases hh : y.holder with
    | frame f => trivial
    | place v =>
      cases hx with
      | base hy' _ _ hf =>
        have h1 : s.flat.A[E.internal]? = some _ := hy'
        rw [hy] at h1; cases h1; rw [hh] at hf; cases hf
      | held hy' _ _ hv hb hall =>
        have h1 : s.flat.A[E.internal]? = some _ := hy'
        rw [hy] at h1; cases h1; rw [hh] at hv; cases hv
        exact hasRight5_of_noLive hng ⟨_, List.mem_range.2 (Arena.exercisable_lt hb), hb, hall⟩

/-- Without a live entry in the synchronization registry, every registered `guarded` identity
existing (WC5 C21.6, `RegBound`), every `ok` step satisfies `PlaceExcl`: the extension leaves the
traces without a live mutex unchanged. `RegBound` keeps the creation phase of the by-value
composite from making an entry live (WC5 C21.6). -/
theorem placeExcl_of_noLive {k : K} {L : MutexLayout} {lbl : Label} {s : SC} {reg : SyncReg}
    {ar : ArenaReg} {st' : SC × SyncReg × ArenaReg} (hb : ∀ e ∈ reg, e.guarded < s.A.length)
    (hng : ∀ e ∈ reg, ¬ e.Live s) (h : LStep k L lbl (s, reg, ar) st') :
    PlaceExcl k L (s, reg, ar) lbl := by
  cases h with
  | @kernel _ s' _ _ c op hk =>
    cases op with
    | release a =>
      obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok hp =>
        have hr : OptP (s.A[a]?) (fun y => HolderRight (s.view c) y.holder) False :=
          hp.holderRight
        show OptP (s.A[a]?) _ True
        revert hr
        cases s.A[a]? with
        | none => intro hr; exact False.elim hr
        | some y =>
          intro hr
          change HolderRight (s.view c) y.holder at hr
          show HolderRight5 _ c y.holder
          revert hr
          cases y.holder with
          | frame f => intro; trivial
          | place p =>
            exact (hasRight5_of_noLive hng : HasRight (s.view c) .modify p → HasRight5 (s, reg) c .modify p)
      | reject => cases ho
    | transfer src dst =>
      obtain ⟨-, hg⟩ := hk
      cases hg with
      | ok hp => exact ⟨hasRight5_of_noLive hng hp.srcRight, hasRight5_of_noLive hng hp.dstRight⟩
    | depend q x =>
      obtain ⟨-, hg⟩ := hk
      cases hg with
      | ok hp => exact hasRight5_of_noLive hng hp.right
    | store a p =>
      obtain ⟨-, hg⟩ := hk
      cases hg with
      | ok hp =>
        refine ⟨hasRight5_of_noLive hng hp.right, ?_⟩
        have hv : (storeEffC s c a p).view c = storeEff (s.view c) a p :=
          SC.view_set (by unfold storeEff; split <;> rfl)
        have hk := hp.keepsTarget
        rw [← hv] at hk
        exact hasRight5_of_noLive (noLive_skel (store_skel (s.view c) a p) hng) hk
    | endUse p =>
      obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hasRight5_of_noLive hng hp.right
      | reject => cases ho
    | free p au =>
      obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hasRight5_of_noLive hng hp.right
      | reject => cases ho
    | alloc pr ow ls =>
      obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok hst =>
        refine ⟨?_, hasRight5_of_noLive hng hst.ownerRight⟩
        rcases hst.providerRight with hr | ⟨via, hv, hws⟩
        · exact .inl (hasRight5_of_noLive hng hr)
        · exact .inr ⟨via, hv, hws, exer5_of_exercisable hng hws.exercisable⟩
      | fail => cases ho
      | reject => cases ho
    | pin p =>
      obtain ⟨-, o, hR, ho⟩ := hk
      cases hR with
      | ok hp => exact hasRight5_of_noLive hng hp.right
      | reject => cases ho
    | unpin o =>
      obtain ⟨-, o₃, hR, ho⟩ := hk
      cases hR with
      | ok hp =>
        have hr : OptP (s.pins[o]?) (fun ob => HasRight (s.view c) .modify ob.place) False :=
          hp.right
        show OptP (s.pins[o]?) _ True
        revert hr
        cases s.pins[o]? with
        | none => intro hr; exact False.elim hr
        | some ob => exact hasRight5_of_noLive hng
      | reject => cases ho
    | _ => trivial
  | spawnVal hs =>
    obtain ⟨-, hg⟩ := hs
    cases hg with
    | ok hp => exact valRights5_of_noLive _ _ (noLive_create hb hng) hp.transfers
  | @acquire _ _ _ c i _ ha =>
    obtain ⟨-, e, hi, hauth, -⟩ := ha
    exact absurd hauth.1 (hng e (List.mem_of_getElem? hi))
  | issue hs =>
    cases hs with
    | ok hE hst =>
      show OptP (ar[_]?) _ True
      rw [hE]
      exact metaRight5_of_noLive hng hst.metaRight
  | reset hs =>
    obtain ⟨-, o₃, hR, ho⟩ := hs
    cases hR with
    | ok hE hd =>
      show OptP (ar[_]?) _ True
      rw [hE]
      cases hd with
      | ok hp => exact metaRight5_of_exercisable hng hp.exercisable
    | noEntry => cases ho
    | derive => cases ho
    | release => cases ho
    | contract => cases ho
  | _ => trivial

end Ern.Concurrency
