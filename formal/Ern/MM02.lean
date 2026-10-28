/-!
# ERN — Memory Model v0.3, MM-02 (machine abstraite minimale)

Modèle exploratoire de MM-02. Chaque définition et chaque théorème cite la
règle MM-02.x qu'il modélise ; le texte des règles reste dans la spécification.
`State.write`, `State.dealloc`, `State.alloc` : effet d'une opération valide.
`read`, `write`, `dealloc`, `alloc` : opérations brutes, issue `ok` ou `ub`
(MM-02.H) ; `checkedWrite`, `checkedDealloc` : variantes vérifiées.
Obligations non décidées par le noyau, paramètres explicites des opérations
brutes : `ObR` (MM-02.B.4, B.6, B.7), `ObW` (MM-02.C.4, C.5, C.6).
Non couverts : MM-02.1, MM-02.F, MM-02.G, MM-03.
-/

namespace Ern.MM02

/-- MM-02.5 : autorité d'accès. -/
inductive Auth where
  | read
  | write

/-- MM-02.5 : ordre des autorités, `read ≤ write` (réflexif). -/
instance : LE Auth := ⟨fun a b => a = .read ∨ b = .write⟩

/-- MM-02.3 : octet abstrait, non initialisé ou initialisé avec une valeur
d'octet sur 8 bits (`val`) et une provenance optionnelle (`prov`, identité
d'allocation). -/
inductive AByte where
  | uninit
  | init (val : UInt8) (prov : Option Nat)

/-- MM-02.2 : allocation abstraite. Son identité est sa clé dans `State.allocs`.
`space` espace d'adressage, `base` adresse de base, `size` étendue, `align` alignement, `live` état
d'existence, `bytes` stockage indexé par décalage depuis `base`,
`freeAuth` jeton de désallocation : si `freeAuth = some d`, les autorités
capables de la désallouer (MM-02.2) sont les `auth` telles que
`Compatible auth d` (MM-02.D) ; `none` si la désallocation n'est pas applicable. -/
structure Alloc where
  space : Nat
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

/-- MM-02.B : la validité spatiale est décidable. -/
instance (a : Alloc) (ac : Access) : Decidable (Spatial a ac) :=
  inferInstanceAs (Decidable (a.base ≤ ac.addr ∧ ac.addr + ac.len ≤ a.base + a.size))

/-- MM-02.4 : résolution partielle d'un moyen d'accès vers un emplacement :
`some` exactement quand la provenance désigne une allocation existante et que la
plage de l'accès y est spatialement contenue (MM-02.B). -/
def Access.toPlace (s : State) (ac : Access) : Option Place :=
  match s.allocs ac.prov with
  | some a => if Spatial a ac then some ⟨ac.prov, ac.addr - a.base, ac.len⟩ else none
  | none => none

/-- MM-02.B et MM-02.4 : lecture permise formulée sur l'emplacement résolu.
Condition 2 portée par la résolution ; conditions 1, 3, 5 vérifiées séparément. -/
def ReadPlace (s : State) (ac : Access) : Prop :=
  ∃ p, ac.toPlace s = some p ∧ ∃ a, s.allocs p.alloc = some a ∧ a.live = true ∧
    a.InitRange p.off p.len ∧ Auth.read ≤ ac.auth

/-- MM-02.C et MM-02.4 : écriture permise formulée sur l'emplacement résolu.
Condition 2 portée par la résolution ; conditions 1, 3 vérifiées séparément. -/
def CanWritePlace (s : State) (ac : Access) : Prop :=
  ∃ p, ac.toPlace s = some p ∧ ∃ a, s.allocs p.alloc = some a ∧ a.live = true ∧
    Auth.write ≤ ac.auth

/-- MM-02.C : effet d'une écriture sur le stockage. Les `len` octets à partir
du décalage `off` deviennent `init`, avec `w i = (valeur, provenance)` du
i-ème octet écrit ; les autres octets sont inchangés. -/
def Alloc.write (a : Alloc) (off len : Nat) (w : Nat → UInt8 × Option Nat) : Alloc :=
  { a with bytes := fun j =>
      if off ≤ j ∧ j < off + len then .init (w (j - off)).1 (w (j - off)).2 else a.bytes j }

/-- MM-02.C : effet d'une écriture par le moyen d'accès `ac` sur l'état. -/
def State.write (s : State) (ac : Access) (w : Nat → UInt8 × Option Nat) : State :=
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
def State.dealloc (s : State) (id : Nat) : State :=
  { s with allocs := fun i =>
      if i = id then (s.allocs i).map (fun a => { a with live := false }) else s.allocs i }

/-- MM-02.2 et MM-02.A : nouvelle allocation sous l'identité fraîche `s.next`,
vivante ; MM-02.3 : allocation brute nouvellement créée, octets tous `uninit`. -/
def State.alloc (s : State) (space base size align : Nat) (freeAuth : Option Nat) : State :=
  { allocs := fun i =>
      if i = s.next then
        some { space, base, size, align, live := true, bytes := fun _ => .uninit, freeAuth }
      else s.allocs i
    next := s.next + 1 }

/-- MM-02.2 (LiveDisjoint) : les plages semi-ouvertes `[b1, b1 + n1)` et
`[b2, b2 + n2)` ont une intersection vide. -/
def RangeDisjoint (b1 n1 b2 n2 : Nat) : Prop :=
  ∀ x, b1 ≤ x → x < b1 + n1 → b2 ≤ x → x < b2 + n2 → False

/-- MM-02.2 (LiveDisjoint) : deux allocations vivantes distinctes du même espace
d'adressage occupent des plages disjointes. -/
def LiveDisjoint (s : State) : Prop :=
  ∀ i j a b, i ≠ j → s.allocs i = some a → s.allocs j = some b →
    a.live = true → b.live = true → a.space = b.space →
    RangeDisjoint a.base a.size b.base b.size

/-- MM-02.2 : `n` est une puissance de deux. -/
def Pow2 (n : Nat) : Prop := ∃ k, n = 2 ^ k

/-- MM-02.2 (création brute) : précondition de création d'une allocation vivante
dans l'espace `space` : identité `s.next` fraîche, alignement strictement positif
et puissance de deux, base alignée, plage disjointe de celle de toute allocation
vivante du même espace (`LiveDisjoint`). -/
def AllocPre (s : State) (space base size align : Nat) : Prop :=
  s.allocs s.next = none ∧ 0 < align ∧ Pow2 align ∧ base % align = 0 ∧
    ∀ i a, s.allocs i = some a → a.live = true → a.space = space →
      RangeDisjoint a.base a.size base size

/-- MM-02.E : `ac'` est dérivé de `ac` : sous-plage, même provenance,
autorité au plus celle de l'origine. -/
def Derive (ac ac' : Access) : Prop :=
  ac.addr ≤ ac'.addr ∧ ac'.addr + ac'.len ≤ ac.addr + ac.len ∧
    ac'.prov = ac.prov ∧ ac'.auth ≤ ac.auth

/-- MM-02.H : issue d'une opération brute : effet défini `ok` (nouvel état) ou
comportement indéfini `ub` (MM-01.5). -/
inductive Outcome where
  | ok (s : State)
  | ub

/-- MM-02.H : issue d'une variante vérifiée : celles d'une opération brute, plus
l'échec défini `fail` rendu sans entrer dans l'opération (MM-01.3). -/
inductive Outcome' where
  | ok (s : State)
  | ub
  | fail

/-- MM-02.H : une issue d'opération brute vue comme issue de variante vérifiée. -/
def Outcome.lift : Outcome → Outcome'
  | .ok s => .ok s
  | .ub => .ub

open Classical in
/-- MM-02.B et MM-02.H : lecture brute par `ac`. `ok` (état inchangé) si les
conditions 1, 2, 3, 5 (`Read`) et les obligations abstraites `ObR`
(conditions 4, 6, 7, non décidées par le noyau) sont satisfaites ; `ub` sinon. -/
noncomputable def read (ObR : State → Access → Prop) (ac : Access) (s : State) : Outcome :=
  if Read s ac ∧ ObR s ac then .ok s else .ub

open Classical in
/-- MM-02.C et MM-02.H : écriture brute de `w` par `ac`. `ok` avec l'effet
`State.write` si les conditions 1, 2, 3 (`CanWrite`) et les obligations
abstraites `ObW` (conditions 4, 5, 6) sont satisfaites ; `ub` sinon. -/
noncomputable def write (ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop)
    (ac : Access) (w : Nat → UInt8 × Option Nat) (s : State) : Outcome :=
  if CanWrite s ac ∧ ObW s ac w then .ok (s.write ac w) else .ub

open Classical in
/-- MM-02.D et MM-02.H : désallocation brute de `id` avec l'autorité `auth`.
`ok` avec l'effet `State.dealloc` si `CanDealloc` ; `ub` sinon. -/
noncomputable def dealloc (Compatible : Nat → Nat → Prop) (id auth : Nat) (s : State) :
    Outcome :=
  if CanDealloc Compatible s id auth then .ok (s.dealloc id) else .ub

open Classical in
/-- MM-02.2 (création brute) et MM-02.H : allocation brute. `ok` avec l'effet
`State.alloc` si `AllocPre` ; `ub` sinon. -/
noncomputable def alloc (space base size align : Nat) (freeAuth : Option Nat) (s : State) :
    Outcome :=
  if AllocPre s space base size align then .ok (s.alloc space base size align freeAuth)
  else .ub

open Classical in
/-- MM-01.3 et MM-02.H : écriture vérifiée : contrôle les conditions de `write`
avant d'appeler l'opération brute ; `fail` sans y entrer si le contrôle échoue. -/
noncomputable def checkedWrite (ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop)
    (ac : Access) (w : Nat → UInt8 × Option Nat) (s : State) : Outcome' :=
  if CanWrite s ac ∧ ObW s ac w then (write ObW ac w s).lift else .fail

open Classical in
/-- MM-01.3 et MM-02.H : désallocation vérifiée : contrôle `CanDealloc` avant
d'appeler l'opération brute ; `fail` sans y entrer si le contrôle échoue. -/
noncomputable def checkedDealloc (Compatible : Nat → Nat → Prop) (id auth : Nat)
    (s : State) : Outcome' :=
  if CanDealloc Compatible s id auth then (dealloc Compatible id auth s).lift else .fail

/-- P1, MM-02.B.1 : toute lecture permise porte sur une allocation vivante. -/
theorem read_requires_live {s : State} {ac : Access} (h : Read s ac) :
    ∃ a, s.allocs ac.prov = some a ∧ a.live = true :=
  let ⟨a, ha, hl, _⟩ := h
  ⟨a, ha, hl⟩

/-- MM-02.D : après `s.dealloc id`, l'allocation enregistrée sous `id`, si elle
existe, est morte. -/
theorem dealloc_dead {s : State} {id : Nat} {a : Alloc}
    (ha : (s.dealloc id).allocs id = some a) : a.live = false := by
  simp [State.dealloc] at ha
  obtain ⟨b, -, rfl⟩ := ha
  rfl

/-- MM-02.D (forme v0.2 sur les prédicats) : après désallocation de l'allocation
visée par `ac`, aucun accès par `ac`, lecture ou écriture, n'est permis. -/
theorem dealloc_invalidates_pre (s : State) (ac : Access) :
    ¬ Read (s.dealloc ac.prov) ac ∧ ¬ CanWrite (s.dealloc ac.prov) ac :=
  ⟨fun ⟨_, ha, hl, _⟩ => by simp [dealloc_dead ha] at hl,
   fun ⟨_, ha, hl, _⟩ => by simp [dealloc_dead ha] at hl⟩

/-- MM-02.D (forme v0.2 sur les prédicats) : après désallocation de `id`, aucune
désallocation de `id` n'est permise. -/
theorem no_double_free_pre (Compatible : Nat → Nat → Prop) (s : State) (id auth : Nat) :
    ¬ CanDealloc Compatible (s.dealloc id) id auth :=
  fun ⟨_, ha, hl, _⟩ => by simp [dealloc_dead ha] at hl

/-- P3, MM-02.C : une écriture permise met à jour les octets de sa plage, qui
deviennent initialisés avec les valeurs et provenances écrites. -/
theorem write_initializes {s : State} {ac : Access} (hw : CanWrite s ac)
    (w : Nat → UInt8 × Option Nat) :
    ∃ a', (s.write ac w).allocs ac.prov = some a' ∧
      ∀ i, i < ac.len → a'.bytes (ac.addr - a'.base + i) = .init (w i).1 (w i).2 := by
  obtain ⟨a, ha, -, -, -⟩ := hw
  refine ⟨a.write (ac.addr - a.base) ac.len w, by simp [State.write, ha], fun i hi => ?_⟩
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

/-- MM-02.A : l'identité `s.next` qu'attribue `State.alloc` est distincte de toute
identité déjà utilisée, et `State.alloc` laisse intacte toute allocation existante. -/
theorem alloc_fresh {s : State} (hwf : WF s) (space base size align : Nat)
    (freeAuth : Option Nat) {i : Nat} {a : Alloc} (ha : s.allocs i = some a) :
    i ≠ s.next ∧ (s.alloc space base size align freeAuth).allocs i = some a :=
  have hne : i ≠ s.next := fun e => by simp [e, hwf _ (Nat.le_refl _)] at ha
  ⟨hne, by simp [State.alloc, hne, ha]⟩

/-- MM-02.A : `State.alloc` préserve l'invariant de fraîcheur. -/
theorem alloc_wf {s : State} (hwf : WF s) (space base size align : Nat)
    (freeAuth : Option Nat) : WF (s.alloc space base size align freeAuth) := by
  intro i hi
  simp only [State.alloc] at hi ⊢
  have : i ≠ s.next := by omega
  simp [this, hwf i (by omega)]

/-- MM-02.A : `State.dealloc` préserve l'invariant de fraîcheur. -/
theorem dealloc_wf {s : State} (hwf : WF s) (id : Nat) : WF (s.dealloc id) := by
  intro i hi
  simp [State.dealloc, hwf i hi]

/-- MM-02.A (forme v0.2 sur les prédicats) : sous l'invariant de fraîcheur
`WF s`, si l'allocation visée par `ac` existait, alors après sa désallocation
puis une nouvelle allocation de base `base` quelconque (y compris la base de
l'ancienne), aucun accès par `ac`, lecture ou écriture, n'est permis. -/
theorem reuse_does_not_restore_pre {s : State} (hwf : WF s) {ac : Access} {a : Alloc}
    (ha : s.allocs ac.prov = some a) (space base size align : Nat) (freeAuth : Option Nat) :
    ¬ Read ((s.dealloc ac.prov).alloc space base size align freeAuth) ac ∧
      ¬ CanWrite ((s.dealloc ac.prov).alloc space base size align freeAuth) ac := by
  have hd : (s.dealloc ac.prov).allocs ac.prov = some { a with live := false } := by
    simp [State.dealloc, ha]
  have hk := (alloc_fresh (dealloc_wf hwf ac.prov) space base size align freeAuth hd).2
  exact ⟨fun ⟨_, hb, hl, _⟩ => by rw [hk] at hb; cases hb; simp at hl,
         fun ⟨_, hb, hl, _⟩ => by rw [hk] at hb; cases hb; simp at hl⟩

/-- MM-02.A : `State.write` préserve l'invariant de fraîcheur. -/
theorem write_wf {s : State} (hwf : WF s) (ac : Access) (w : Nat → UInt8 × Option Nat) :
    WF (s.write ac w) := by
  intro i hi
  simp [State.write, hwf i hi]

/-- MM-02.2 (LiveDisjoint) : un pas qui ne rend vivante aucune allocation et
conserve espace, base et étendue de toute allocation restée vivante préserve
`LiveDisjoint`. -/
theorem LiveDisjoint.of_fields {s s' : State} (hd : LiveDisjoint s)
    (h : ∀ i a, s'.allocs i = some a → a.live = true →
      ∃ a₀, s.allocs i = some a₀ ∧ a₀.live = true ∧ a₀.space = a.space ∧
        a₀.base = a.base ∧ a₀.size = a.size) :
    LiveDisjoint s' := by
  intro i j a b hij ha hb hla hlb hsp
  obtain ⟨a₀, ha₀, hla₀, hs₁, hb₁, hz₁⟩ := h i a ha hla
  obtain ⟨b₀, hb₀, hlb₀, hs₂, hb₂, hz₂⟩ := h j b hb hlb
  have := hd i j a₀ b₀ hij ha₀ hb₀ hla₀ hlb₀ (by rw [hs₁, hs₂, hsp])
  rw [hb₁, hz₁, hb₂, hz₂] at this
  exact this

/-- MM-02.2 (LiveDisjoint) : une écriture préserve `LiveDisjoint`. -/
theorem liveDisjoint_write {s : State} (hd : LiveDisjoint s) (ac : Access)
    (w : Nat → UInt8 × Option Nat) : LiveDisjoint (s.write ac w) :=
  hd.of_fields fun i a ha hla => by
    simp only [State.write] at ha
    split at ha
    · obtain ⟨a₀, h₀, rfl⟩ := Option.map_eq_some_iff.1 ha
      exact ⟨a₀, h₀, hla, rfl, rfl, rfl⟩
    · exact ⟨a, ha, hla, rfl, rfl, rfl⟩

/-- MM-02.2 (LiveDisjoint) : une désallocation préserve `LiveDisjoint`. -/
theorem liveDisjoint_dealloc {s : State} (hd : LiveDisjoint s) (id : Nat) :
    LiveDisjoint (s.dealloc id) :=
  hd.of_fields fun i a ha hla => by
    simp only [State.dealloc] at ha
    split at ha
    · obtain ⟨a₀, -, rfl⟩ := Option.map_eq_some_iff.1 ha
      simp at hla
    · exact ⟨a, ha, hla, rfl, rfl, rfl⟩

/-- MM-02.2 (LiveDisjoint, création brute) : une allocation dont la précondition
de création est satisfaite préserve `LiveDisjoint`. -/
theorem liveDisjoint_alloc {s : State} (hd : LiveDisjoint s) {space base size align : Nat}
    (hp : AllocPre s space base size align) (freeAuth : Option Nat) :
    LiveDisjoint (s.alloc space base size align freeAuth) := by
  obtain ⟨-, -, -, -, hdis⟩ := hp
  intro i j a b hij ha hb hla hlb hsp
  simp only [State.alloc] at ha hb
  by_cases hi : i = s.next <;> by_cases hj : j = s.next
  · exact absurd (hi.trans hj.symm) hij
  · rw [ite_eq_left hi] at ha
    rw [ite_eq_right hj] at hb
    cases ha
    exact fun x h1 h2 h3 h4 => hdis j b hb hlb hsp.symm x h3 h4 h1 h2
  · rw [ite_eq_right hi] at ha
    rw [ite_eq_left hj] at hb
    cases hb
    exact hdis i a ha hla hsp
  · rw [ite_eq_right hi] at ha
    rw [ite_eq_right hj] at hb
    exact hd i j a b hij ha hb hla hlb hsp

/-- MM-02.4 : `ac.toPlace s = some p` ssi la provenance désigne une allocation
existante `a`, l'accès est spatialement contenu dans `a`, et `p` est la portion
désignée. -/
theorem toPlace_eq_some {s : State} {ac : Access} {p : Place} :
    ac.toPlace s = some p ↔
      ∃ a, s.allocs ac.prov = some a ∧ Spatial a ac ∧
        p = ⟨ac.prov, ac.addr - a.base, ac.len⟩ := by
  unfold Access.toPlace
  split
  · next a ha =>
    by_cases hs : Spatial a ac
    · simp [hs, ha, eq_comm]
    · simp [hs, ha]
  · next ha => simp [ha]

/-- MM-02.4 et MM-02.B : la lecture formulée par résolution équivaut à `Read`. -/
theorem read_iff_place {s : State} {ac : Access} : Read s ac ↔ ReadPlace s ac := by
  constructor
  · rintro ⟨a, ha, hl, hs, hi, hr⟩
    exact ⟨_, toPlace_eq_some.2 ⟨a, ha, hs, rfl⟩, a, ha, hl, hi, hr⟩
  · rintro ⟨p, hp, b, hb, hl, hi, hr⟩
    obtain ⟨a, ha, hs, rfl⟩ := toPlace_eq_some.1 hp
    have hb : s.allocs ac.prov = some b := hb
    rw [ha] at hb
    cases hb
    exact ⟨_, ha, hl, hs, hi, hr⟩

/-- MM-02.4 et MM-02.C : l'écriture formulée par résolution équivaut à `CanWrite`. -/
theorem canWrite_iff_place {s : State} {ac : Access} : CanWrite s ac ↔ CanWritePlace s ac := by
  constructor
  · rintro ⟨a, ha, hl, hs, hr⟩
    exact ⟨_, toPlace_eq_some.2 ⟨a, ha, hs, rfl⟩, a, ha, hl, hr⟩
  · rintro ⟨p, hp, b, hb, hl, hr⟩
    obtain ⟨a, ha, hs, rfl⟩ := toPlace_eq_some.1 hp
    have hb : s.allocs ac.prov = some b := hb
    rw [ha] at hb
    cases hb
    exact ⟨_, ha, hl, hs, hr⟩

/-- MM-02.D et MM-02.H : une désallocation brute a pour issue `ok s'` ssi
`CanDealloc` est satisfait et `s'` est l'effet `State.dealloc`. -/
theorem dealloc_eq_ok {Compatible : Nat → Nat → Prop} {id auth : Nat} {s s' : State} :
    dealloc Compatible id auth s = .ok s' ↔ CanDealloc Compatible s id auth ∧ s' = s.dealloc id := by
  unfold dealloc
  split <;> simp_all [eq_comm]

/-- MM-02.2 (création brute) et MM-02.H : une allocation brute a pour issue
`ok s'` ssi `AllocPre` est satisfait et `s'` est l'effet `State.alloc`. -/
theorem alloc_eq_ok {space base size align : Nat} {freeAuth : Option Nat} {s s' : State} :
    alloc space base size align freeAuth s = .ok s' ↔
      AllocPre s space base size align ∧ s' = s.alloc space base size align freeAuth := by
  unfold alloc
  split <;> simp_all [eq_comm]

/-- MM-02.B et MM-02.H : une lecture brute a pour issue `ok s'` ssi `Read` et les
obligations `ObR` sont satisfaites et `s' = s`. -/
theorem read_eq_ok {ObR : State → Access → Prop} {ac : Access} {s s' : State} :
    read ObR ac s = .ok s' ↔ (Read s ac ∧ ObR s ac) ∧ s' = s := by
  unfold read
  split <;> simp_all [eq_comm]

/-- MM-02.B et MM-02.H : une lecture brute a pour issue `ub` ssi `Read` ou les
obligations `ObR` ne sont pas satisfaites. -/
theorem read_eq_ub {ObR : State → Access → Prop} {ac : Access} {s : State} :
    read ObR ac s = .ub ↔ ¬ (Read s ac ∧ ObR s ac) := by
  unfold read
  split <;> simp_all

/-- MM-02.C et MM-02.H : une écriture brute a pour issue `ok s'` ssi `CanWrite`
et les obligations `ObW` sont satisfaites et `s'` est l'effet `State.write`. -/
theorem write_eq_ok {ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop} {ac : Access}
    {w : Nat → UInt8 × Option Nat} {s s' : State} :
    write ObW ac w s = .ok s' ↔ (CanWrite s ac ∧ ObW s ac w) ∧ s' = s.write ac w := by
  unfold write
  split <;> simp_all [eq_comm]

/-- MM-02.C et MM-02.H : une écriture brute a pour issue `ub` ssi `CanWrite` ou
les obligations `ObW` ne sont pas satisfaites. -/
theorem write_eq_ub {ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop} {ac : Access}
    {w : Nat → UInt8 × Option Nat} {s : State} :
    write ObW ac w s = .ub ↔ ¬ (CanWrite s ac ∧ ObW s ac w) := by
  unfold write
  split <;> simp_all

/-- MM-01.3 et MM-02.H : une écriture vérifiée a pour issue `ok s'` ssi le
contrôle réussit et `s'` est l'effet `State.write`. -/
theorem checkedWrite_eq_ok {ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop}
    {ac : Access} {w : Nat → UInt8 × Option Nat} {s s' : State} :
    checkedWrite ObW ac w s = .ok s' ↔ (CanWrite s ac ∧ ObW s ac w) ∧ s' = s.write ac w := by
  unfold checkedWrite write
  split <;> simp_all [Outcome.lift, eq_comm]

/-- MM-01.3 et MM-02.H : une écriture vérifiée a pour issue `fail` ssi le
contrôle échoue. -/
theorem checkedWrite_eq_fail {ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop}
    {ac : Access} {w : Nat → UInt8 × Option Nat} {s : State} :
    checkedWrite ObW ac w s = .fail ↔ ¬ (CanWrite s ac ∧ ObW s ac w) := by
  unfold checkedWrite write
  split <;> simp_all [Outcome.lift]

/-- MM-01.3 et MM-02.H : une désallocation vérifiée a pour issue `ok s'` ssi le
contrôle réussit et `s'` est l'effet `State.dealloc`. -/
theorem checkedDealloc_eq_ok {Compatible : Nat → Nat → Prop} {id auth : Nat} {s s' : State} :
    checkedDealloc Compatible id auth s = .ok s' ↔
      CanDealloc Compatible s id auth ∧ s' = s.dealloc id := by
  unfold checkedDealloc dealloc
  split <;> simp_all [Outcome.lift, eq_comm]

/-- MM-01.3 et MM-02.H : une désallocation vérifiée a pour issue `fail` ssi le
contrôle échoue. -/
theorem checkedDealloc_eq_fail {Compatible : Nat → Nat → Prop} {id auth : Nat} {s : State} :
    checkedDealloc Compatible id auth s = .fail ↔ ¬ CanDealloc Compatible s id auth := by
  unfold checkedDealloc dealloc
  split <;> simp_all [Outcome.lift]

/-- MM-01.3 et MM-02.H : une écriture vérifiée n'a jamais pour issue `ub`. -/
theorem checkedWrite_ne_ub (ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop)
    (ac : Access) (w : Nat → UInt8 × Option Nat) (s : State) :
    checkedWrite ObW ac w s ≠ .ub := by
  unfold checkedWrite write
  split <;> simp_all [Outcome.lift]

/-- MM-01.3 et MM-02.H : une désallocation vérifiée n'a jamais pour issue `ub`. -/
theorem checkedDealloc_ne_ub (Compatible : Nat → Nat → Prop) (id auth : Nat) (s : State) :
    checkedDealloc Compatible id auth s ≠ .ub := by
  unfold checkedDealloc dealloc
  split <;> simp_all [Outcome.lift]

/-- P2a, MM-02.D et MM-02.H : après une désallocation brute réussie de
l'allocation visée par `ac`, toute lecture et toute écriture brutes par `ac` ont
pour issue `ub`. -/
theorem dealloc_invalidates {Compatible : Nat → Nat → Prop} {ObR : State → Access → Prop}
    {ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop} {ac : Access} {auth : Nat}
    {s s' : State} (h : dealloc Compatible ac.prov auth s = .ok s') :
    read ObR ac s' = .ub ∧ ∀ w, write ObW ac w s' = .ub := by
  obtain ⟨-, rfl⟩ := dealloc_eq_ok.1 h
  obtain ⟨hr, hw⟩ := dealloc_invalidates_pre s ac
  exact ⟨by simp [read, hr], fun w => by simp [write, hw]⟩

/-- P2c, MM-02.D et MM-02.H : après une désallocation brute réussie de `id`, une
nouvelle désallocation brute de `id`, avec toute autorité, a pour issue `ub`. -/
theorem no_double_free {Compatible : Nat → Nat → Prop} {id auth : Nat} {s s' : State}
    (h : dealloc Compatible id auth s = .ok s') (auth' : Nat) :
    dealloc Compatible id auth' s' = .ub := by
  obtain ⟨-, rfl⟩ := dealloc_eq_ok.1 h
  simp [dealloc, no_double_free_pre Compatible s id auth']

/-- P2b, MM-02.A et MM-02.H : après la désallocation brute réussie de
l'allocation visée par `ac`, puis une allocation brute réussie de base `base`
quelconque (y compris la base de l'ancienne), toute lecture et toute écriture
brutes par `ac` ont pour issue `ub`. -/
theorem reuse_does_not_restore {Compatible : Nat → Nat → Prop}
    {ObR : State → Access → Prop} {ObW : State → Access → (Nat → UInt8 × Option Nat) → Prop}
    {ac : Access} {auth : Nat} (space base size align : Nat) (freeAuth : Option Nat)
    {s s₁ s₂ : State} (h₁ : dealloc Compatible ac.prov auth s = .ok s₁)
    (h₂ : alloc space base size align freeAuth s₁ = .ok s₂) :
    read ObR ac s₂ = .ub ∧ ∀ w, write ObW ac w s₂ = .ub := by
  obtain ⟨⟨a, ha, -⟩, hs₁⟩ := dealloc_eq_ok.1 h₁
  obtain ⟨⟨hf, -⟩, hs₂⟩ := alloc_eq_ok.1 h₂
  have hd : s₁.allocs ac.prov = some { a with live := false } := by
    subst hs₁
    simp [State.dealloc, ha]
  have hne : ac.prov ≠ s₁.next := fun e => by
    rw [e, hf] at hd
    cases hd
  have hk : s₂.allocs ac.prov = some { a with live := false } := by
    subst hs₂
    simp [State.alloc, hne, hd]
  have hr : ¬ Read s₂ ac := fun ⟨_, hb, hl, _⟩ => by rw [hk] at hb; cases hb; simp at hl
  have hw : ¬ CanWrite s₂ ac := fun ⟨_, hb, hl, _⟩ => by rw [hk] at hb; cases hb; simp at hl
  exact ⟨by simp [read, hr], fun w => by simp [write, hw]⟩

/-- MM-02, exemple 1 (adresse réutilisée) : allocation, désallocation, puis
nouvelle allocation à la même base ; les hypothèses de `reuse_does_not_restore`
sont satisfiables avec une base identique. -/
example : ∃ s₁ s₂ s₃ : State,
    alloc 0 96 8 8 (some 0) ⟨fun _ => none, 0⟩ = .ok s₁ ∧
    dealloc (fun _ _ => True) 0 0 s₁ = .ok s₂ ∧
    alloc 0 96 8 8 none s₂ = .ok s₃ := by
  refine ⟨_, _, _, alloc_eq_ok.2 ⟨?_, rfl⟩, dealloc_eq_ok.2 ⟨?_, rfl⟩, alloc_eq_ok.2 ⟨?_, rfl⟩⟩
  · exact ⟨rfl, by decide, ⟨3, rfl⟩, rfl, fun _ _ h => by cases h⟩
  · exact ⟨{ space := 0, base := 96, size := 8, align := 8, live := true,
              bytes := fun _ => .uninit, freeAuth := some 0 },
            by simp [State.alloc], rfl, 0, rfl, trivial⟩
  · refine ⟨by simp [State.dealloc, State.alloc], by decide, ⟨3, rfl⟩, rfl, fun i a h hl _ => ?_⟩
    by_cases hi : i = 0
    · subst hi
      simp [State.dealloc, State.alloc] at h
      subst h
      simp at hl
    · simp [State.dealloc, State.alloc, hi] at h

/-- MM-02.C (écriture valide) : cadre de l'effet d'écriture. Toute allocation
autre que `ac.prov` est inchangée ; dans `ac.prov`, seuls les octets changent et
tout octet hors de `[off, off + len)`, avec `off = ac.addr - base`, est inchangé ;
`next` est inchangé. -/
theorem write_frame (s : State) (ac : Access) (w : Nat → UInt8 × Option Nat) :
    (∀ i, i ≠ ac.prov → (s.write ac w).allocs i = s.allocs i) ∧
    (∀ a, s.allocs ac.prov = some a → ∃ a', (s.write ac w).allocs ac.prov = some a' ∧
      { a' with bytes := a.bytes } = a ∧
      ∀ j, ¬ (ac.addr - a.base ≤ j ∧ j < ac.addr - a.base + ac.len) → a'.bytes j = a.bytes j) ∧
    (s.write ac w).next = s.next :=
  ⟨fun i hi => by simp [State.write, hi],
   fun a ha => ⟨a.write (ac.addr - a.base) ac.len w, by simp [State.write, ha], rfl,
     fun j hj => by simp only [Alloc.write]; exact ite_eq_right hj⟩,
   rfl⟩

/-- MM-02.D : cadre de l'effet de désallocation. Toute allocation autre que `id`
est inchangée ; `next` est inchangé. -/
theorem dealloc_frame (s : State) (id : Nat) :
    (∀ i, i ≠ id → (s.dealloc id).allocs i = s.allocs i) ∧ (s.dealloc id).next = s.next :=
  ⟨fun i hi => by simp [State.dealloc, hi], rfl⟩

/-- MM-02.A : cadre de l'effet d'allocation. Si l'identité `s.next` est fraîche
(clause de `AllocPre`), toute allocation existante est inchangée. -/
theorem alloc_frame {s : State} (hf : s.allocs s.next = none) (space base size align : Nat)
    (freeAuth : Option Nat) {i : Nat} {a : Alloc} (ha : s.allocs i = some a) :
    (s.alloc space base size align freeAuth).allocs i = some a := by
  have hne : i ≠ s.next := fun e => by
    rw [e, hf] at ha
    cases ha
  simp [State.alloc, hne, ha]

end Ern.MM02
