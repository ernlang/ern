/-!
# ERN — Memory Model v0.2, MM-02 (machine abstraite minimale)

Modèle exploratoire de MM-02. Chaque définition et chaque théorème cite la
règle MM-02.x qu'il modélise ; le texte des règles reste dans la spécification.
Conditions abstraites (par omission) : MM-02.B.4, B.6, B.7 ; MM-02.C.4, C.5, C.6 ;
MM-02.D troisième condition (autres invariants).
Non couverts : MM-02.1 (aucune règle opératoire, hors du périmètre de la tâche),
MM-02.F, MM-02.G.
-/

namespace Ern.MM02

/-- MM-02.5 : autorité d'accès. -/
inductive Auth where
  | read
  | write

/-- MM-02.5 : ordre des autorités, `read ≤ write` (réflexif). -/
instance : LE Auth := ⟨fun a b => a = .read ∨ b = .write⟩

/-- MM-02.3 : octet abstrait, non initialisé ou initialisé avec une valeur
d'octet (`val`) et une provenance optionnelle (`prov`, identité d'allocation). -/
inductive AByte where
  | uninit
  | init (val : Nat) (prov : Option Nat)

/-- MM-02.2 : allocation abstraite. Son identité est sa clé dans `State.allocs`.
`base` adresse de base, `size` étendue, `align` alignement, `live` état
d'existence, `bytes` stockage indexé par décalage depuis `base`,
`freeAuth` autorité de désallocation de référence : une autorité `auth` peut
désallouer ssi `Compatible auth d` (MM-02.D), `none` si la désallocation n'est
pas applicable. -/
structure Alloc where
  base : Nat
  size : Nat
  align : Nat
  live : Bool
  bytes : Nat → AByte
  freeAuth : Option Nat

/-- MM-02.4 : emplacement, allocation (`alloc`, identité) et portion de son
stockage (`off` décalage, `len` longueur). Interprétation typée et conditions
d'accès non modélisées. -/
structure Place where
  alloc : Nat
  off : Nat
  len : Nat

/-- MM-02.5 : moyen d'accès. `addr` adresse, `prov` provenance (identité
d'allocation, sans étiquette : lecture fixée par la tâche), `len` plage,
`auth` autorité. -/
structure Access where
  addr : Nat
  prov : Nat
  len : Nat
  auth : Auth

/-- État de la machine abstraite : allocations par identité (MM-02.2) et
prochaine identité fraîche `next` (MM-02.A). -/
structure State where
  allocs : Nat → Option Alloc
  next : Nat

/-- MM-02.A : invariant de fraîcheur, toute identité utilisée est `< next`. -/
def WF (s : State) : Prop := ∀ i, s.next ≤ i → s.allocs i = none

/-- MM-02.B.2 et MM-02.C.2 : validité spatiale, la plage de l'accès est incluse
dans l'étendue de l'allocation. -/
def Spatial (a : Alloc) (ac : Access) : Prop :=
  a.base ≤ ac.addr ∧ ac.addr + ac.len ≤ a.base + a.size

/-- MM-02.B.3 : les `len` octets à partir du décalage `off` sont initialisés. -/
def Alloc.InitRange (a : Alloc) (off len : Nat) : Prop :=
  ∀ i, i < len → a.bytes (off + i) ≠ .uninit

/-- MM-02.B : lecture typée permise. Conditions 1 (stockage vivant),
2 (spatial), 3 (initialisation), 5 (autorité de lecture). -/
def Read (s : State) (ac : Access) : Prop :=
  ∃ a, s.allocs ac.prov = some a ∧ a.live = true ∧ Spatial a ac ∧
    a.InitRange (ac.addr - a.base) ac.len ∧ Auth.read ≤ ac.auth

/-- MM-02.C : écriture typée permise. Conditions 1 (stockage vivant),
2 (spatial), 3 (autorité d'écriture). -/
def CanWrite (s : State) (ac : Access) : Prop :=
  ∃ a, s.allocs ac.prov = some a ∧ a.live = true ∧ Spatial a ac ∧ Auth.write ≤ ac.auth

/-- MM-02.C : effet d'une écriture sur le stockage. Les `len` octets à partir
du décalage `off` deviennent `init`, avec `w i = (valeur, provenance)` du
i-ème octet écrit ; les autres octets sont inchangés. -/
def Alloc.write (a : Alloc) (off len : Nat) (w : Nat → Nat × Option Nat) : Alloc :=
  { a with bytes := fun j =>
      if off ≤ j ∧ j < off + len then .init (w (j - off)).1 (w (j - off)).2 else a.bytes j }

/-- MM-02.C : effet d'une écriture par le moyen d'accès `ac` sur l'état. -/
def write (s : State) (ac : Access) (w : Nat → Nat × Option Nat) : State :=
  { s with allocs := fun i =>
      if i = ac.prov then (s.allocs i).map (fun a => a.write (ac.addr - a.base) ac.len w)
      else s.allocs i }

/-- MM-02.D : désallocation permise de l'allocation `id` avec l'autorité `auth` :
allocation vivante et désallouable (`freeAuth = some d`), autorité compatible
selon la relation paramétrique `Compatible`. -/
def CanDealloc (Compatible : Nat → Nat → Prop) (s : State) (id auth : Nat) : Prop :=
  ∃ a, s.allocs id = some a ∧ a.live = true ∧ ∃ d, a.freeAuth = some d ∧ Compatible auth d

/-- MM-02.D : effet d'une désallocation, l'allocation `id` cesse d'exister
(état mort) ; son identité reste consommée (MM-02.A). -/
def dealloc (s : State) (id : Nat) : State :=
  { s with allocs := fun i =>
      if i = id then (s.allocs i).map (fun a => { a with live := false }) else s.allocs i }

/-- MM-02.2 et MM-02.A : nouvelle allocation sous l'identité fraîche `s.next`,
vivante, entièrement non initialisée (MM-02.3). -/
def alloc (s : State) (base size align : Nat) (freeAuth : Option Nat) : State :=
  { allocs := fun i =>
      if i = s.next then
        some { base, size, align, live := true, bytes := fun _ => .uninit, freeAuth }
      else s.allocs i
    next := s.next + 1 }

/-- MM-02.E : `ac'` est dérivé de `ac` : sous-plage, même provenance,
autorité au plus celle de l'origine. -/
def Derive (ac ac' : Access) : Prop :=
  ac.addr ≤ ac'.addr ∧ ac'.addr + ac'.len ≤ ac.addr + ac.len ∧
    ac'.prov = ac.prov ∧ ac'.auth ≤ ac.auth

/-- P1, MM-02.B.1 : toute lecture permise porte sur une allocation vivante. -/
theorem read_requires_live {s : State} {ac : Access} (h : Read s ac) :
    ∃ a, s.allocs ac.prov = some a ∧ a.live = true :=
  let ⟨a, ha, hl, _⟩ := h
  ⟨a, ha, hl⟩

/-- MM-02.D : après `dealloc s id`, l'allocation enregistrée sous `id`, si elle
existe, est morte. -/
theorem dealloc_dead {s : State} {id : Nat} {a : Alloc}
    (ha : (dealloc s id).allocs id = some a) : a.live = false := by
  simp [dealloc] at ha
  obtain ⟨b, -, rfl⟩ := ha
  rfl

/-- P2a, MM-02.D : après désallocation de l'allocation visée par `ac`, aucun
accès par `ac`, lecture ou écriture, n'est permis. -/
theorem dealloc_invalidates (s : State) (ac : Access) :
    ¬ Read (dealloc s ac.prov) ac ∧ ¬ CanWrite (dealloc s ac.prov) ac :=
  ⟨fun ⟨_, ha, hl, _⟩ => by simp [dealloc_dead ha] at hl,
   fun ⟨_, ha, hl, _⟩ => by simp [dealloc_dead ha] at hl⟩

/-- P2c, MM-02.D : après désallocation de `id`, aucune désallocation de `id`
n'est permise. -/
theorem no_double_free (Compatible : Nat → Nat → Prop) (s : State) (id auth : Nat) :
    ¬ CanDealloc Compatible (dealloc s id) id auth :=
  fun ⟨_, ha, hl, _⟩ => by simp [dealloc_dead ha] at hl

/-- P3, MM-02.C : une écriture permise met à jour les octets de sa plage, qui
deviennent initialisés avec les valeurs et provenances écrites. -/
theorem write_initializes {s : State} {ac : Access} (hw : CanWrite s ac)
    (w : Nat → Nat × Option Nat) :
    ∃ a', (write s ac w).allocs ac.prov = some a' ∧
      ∀ i, i < ac.len → a'.bytes (ac.addr - a'.base + i) = .init (w i).1 (w i).2 := by
  obtain ⟨a, ha, -, -, -⟩ := hw
  refine ⟨a.write (ac.addr - a.base) ac.len w, by simp [write, ha], fun i hi => ?_⟩
  simp only [Alloc.write]
  rw [ite_eq_left ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hi _⟩, Nat.add_sub_cancel_left]

/-- P4, MM-02.E : un accès dérivé d'un accès spatialement valide est
spatialement valide. -/
theorem derive_spatial {ac ac' : Access} (hd : Derive ac ac') {a : Alloc}
    (hs : Spatial a ac) : Spatial a ac' := by
  obtain ⟨h1, h2, -, -⟩ := hd
  obtain ⟨h3, h4⟩ := hs
  exact ⟨by omega, by omega⟩

/-- P4, MM-02.E : la dérivation préserve la provenance. -/
theorem derive_prov {ac ac' : Access} (hd : Derive ac ac') : ac'.prov = ac.prov :=
  hd.2.2.1

/-- P4, MM-02.E : un accès dérivé n'acquiert pas plus d'autorité que son origine. -/
theorem derive_auth_le {ac ac' : Access} (hd : Derive ac ac') : ac'.auth ≤ ac.auth :=
  hd.2.2.2

/-- MM-02.A : l'identité `s.next` qu'attribue `alloc` est distincte de toute
identité déjà utilisée, et `alloc` laisse intacte toute allocation existante. -/
theorem alloc_fresh {s : State} (hwf : WF s) (base size align : Nat) (freeAuth : Option Nat)
    {i : Nat} {a : Alloc} (ha : s.allocs i = some a) :
    i ≠ s.next ∧ (alloc s base size align freeAuth).allocs i = some a :=
  have hne : i ≠ s.next := fun e => by simp [e, hwf _ (Nat.le_refl _)] at ha
  ⟨hne, by simp [alloc, hne, ha]⟩

/-- MM-02.A : `alloc` préserve l'invariant de fraîcheur. -/
theorem alloc_wf {s : State} (hwf : WF s) (base size align : Nat) (freeAuth : Option Nat) :
    WF (alloc s base size align freeAuth) := by
  intro i hi
  simp only [alloc] at hi ⊢
  have : i ≠ s.next := by omega
  simp [this, hwf i (by omega)]

/-- MM-02.A : `dealloc` préserve l'invariant de fraîcheur. -/
theorem dealloc_wf {s : State} (hwf : WF s) (id : Nat) : WF (dealloc s id) := by
  intro i hi
  simp [dealloc, hwf i hi]

/-- P2b, MM-02.A : si l'allocation visée par `ac` existait, alors après sa
désallocation puis une nouvelle allocation de base `base` quelconque (y compris
la base de l'ancienne), aucun accès par `ac`, lecture ou écriture, n'est permis. -/
theorem reuse_does_not_restore {s : State} (hwf : WF s) {ac : Access} {a : Alloc}
    (ha : s.allocs ac.prov = some a) (base size align : Nat) (freeAuth : Option Nat) :
    ¬ Read (alloc (dealloc s ac.prov) base size align freeAuth) ac ∧
      ¬ CanWrite (alloc (dealloc s ac.prov) base size align freeAuth) ac := by
  have hd : (dealloc s ac.prov).allocs ac.prov = some { a with live := false } := by
    simp [dealloc, ha]
  have hk := (alloc_fresh (dealloc_wf hwf ac.prov) base size align freeAuth hd).2
  exact ⟨fun ⟨_, hb, hl, _⟩ => by rw [hk] at hb; cases hb; simp at hl,
         fun ⟨_, hb, hl, _⟩ => by rw [hk] at hb; cases hb; simp at hl⟩

/-- MM-02.A : `write` préserve l'invariant de fraîcheur. -/
theorem write_wf {s : State} (hwf : WF s) (ac : Access) (w : Nat → Nat × Option Nat) :
    WF (write s ac w) := by
  intro i hi
  simp [write, hwf i hi]

end Ern.MM02
