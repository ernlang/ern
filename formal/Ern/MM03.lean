import Ern.MM02

/-!
# MM-03.3 v0.2 : noyau de la discipline d'accès (modèle exploratoire, jalon 1)

Couche abstraite de `formal/DESIGN.md` (« Abstract model ») : la mémoire est un arbre fini
d'emplacements. Le raffinement vers MM-02 (MM-03.3 §9) est le jalon 2 et n'est pas traité ici ;
le module importe `Ern.MM02` sans l'utiliser ni le modifier.
-/

namespace Ern.MM03

/-! ## Cadres (MM-03.3.1) -/

/-- Pile de cadres `F` (MM-03.3.1) : identités de cadres, cadre courant en tête. Le parent d'un
cadre est l'élément qui le suit ; le dernier élément est le cadre initial. -/
abbrev Frames := List Nat

/-- `ancestor F f₁ f₂` (MM-03.3.1) : `f₁` est `f₂` lui-même ou l'un de ses ancêtres dans `F`,
c'est-à-dire `f₁` figure dans `F` à partir de la première occurrence de `f₂`. -/
def ancestor (F : Frames) (f₁ f₂ : Nat) : Prop := f₁ ∈ F.dropWhile (· != f₂)

instance (F : Frames) (f₁ f₂ : Nat) : Decidable (ancestor F f₁ f₂) :=
  inferInstanceAs (Decidable (_ ∈ _))

/-! ## Chaînes de parents

Les emplacements (par `parent`) et les autorités (par `origin`) forment des forêts dont les
identités sont des indices. Une chaîne ne suit qu'un lien vers un indice strictement inférieur ;
le carburant `k` ne sert qu'à la terminaison. -/

/-- Chaîne des ancêtres stricts de `i` par le lien `org`, du plus proche au plus lointain. -/
def chainF (org : Nat → Option Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | k + 1, i =>
    match org i with
    | some o => if o < i then o :: chainF org k o else []
    | none => []

/-- Ancêtres stricts de `i` par `org` (carburant `i`, suffisant puisque la chaîne décroît). -/
def chain (org : Nat → Option Nat) (i : Nat) : List Nat := chainF org i i

/-! ## Emplacements (MM-03.3.2) -/

/-- Emplacement logique (MM-03.3.2 : `Place { id, parent?, frame, kind }`). Son identité est son
indice dans `P`. `kind` n'est pas interprété : MM-03.3.2 n'en donne pas les valeurs. -/
structure Place where
  parent : Option Nat
  frame : Nat
  kind : Nat
deriving DecidableEq, Repr

/-- Lien `parent` de l'emplacement d'indice `i` (MM-03.3.2). -/
def parentOf (P : List Place) (i : Nat) : Option Nat := (P[i]?).bind (·.parent)

/-- `partOf P p q` (MM-03.3.2, composition logique) : `p` est un emplacement de `P` et `q` est
`p` lui-même ou l'un de ses ancêtres par `parent`. -/
def partOf (P : List Place) (p q : Nat) : Prop :=
  p < P.length ∧ (p = q ∨ q ∈ chain (parentOf P) p)

instance (P : List Place) (p q : Nat) : Decidable (partOf P p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Feuille de stockage (MM-03.3.2) : emplacement sans partie stricte. -/
def isLeaf (P : List Place) (l : Nat) : Prop := ∀ r < P.length, parentOf P r ≠ some l

instance (P : List Place) (l : Nat) : Decidable (isLeaf P l) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- `footprint P q` (MM-03.3.2) : les feuilles de `P` qui sont des parties de `q`. -/
def footprint (P : List Place) (q : Nat) : List Nat :=
  (List.range P.length).filter fun l => decide (isLeaf P l ∧ partOf P l q)

/-- Chevauchement de deux emplacements : leurs empreintes ont une feuille commune
(MM-03.3.2). -/
def overlap (P : List Place) (p q : Nat) : Prop := ∃ l ∈ footprint P p, l ∈ footprint P q

instance (P : List Place) (p q : Nat) : Decidable (overlap P p q) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, _))

/-- Disjonction structurelle (MM-03.3.2) : aucun des deux chemins n'est une partie de l'autre. -/
def structurallyDisjoint (P : List Place) (p q : Nat) : Prop := ¬ partOf P p q ∧ ¬ partOf P q p

instance (P : List Place) (p q : Nat) : Decidable (structurallyDisjoint P p q) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Cadre de l'emplacement `p` (MM-03.3.2, champ `frame`). -/
def placeFrame (P : List Place) (p : Nat) : Option Nat := (P[p]?).map (·.frame)

/-! ## État `S3` (MM-03.3 §1) -/

/-- État d'initialisation d'une feuille (MM-03.3.3). -/
inductive InitSt where
  | uninit
  | init
  | moved
deriving DecidableEq, Repr

/-- Mode d'une autorité (MM-03.3.4). -/
inductive Mode where
  | observe
  | modify
deriving DecidableEq, Repr

/-- Ordre des modes : `Observe` n'excède pas `Modify` (MM-03.3.4 : `Modify` autorise les
modifications et les observations). -/
def Mode.le (m m' : Mode) : Prop := m = .observe ∨ m' = .modify

instance (m m' : Mode) : Decidable (m.le m') := inferInstanceAs (Decidable (_ ∨ _))

/-- Autorité (MM-03.3.4 : `Authority { id, mode, origin?, footprint, frame, active }`). Son
identité est son indice dans `A` ; son empreinte est une liste de feuilles ; aucun statut
`Suspended` n'est stocké (arbitrage 4). -/
structure Authority where
  mode : Mode
  origin : Option Nat
  footprint : List Nat
  frame : Nat
  active : Bool
deriving DecidableEq, Repr

/-- Contrats `K` (MM-03.3.8), fixés pour l'exécution (arbitrage 5). Les types sont un choix de
représentation : régions comme listes de feuilles, feuilles, et `Invalidates r x` pour
« l'opération invalidante de la ressource `r` invalide l'ancre `x` ». Les obligations
accompagnant chaque contrat sont des hypothèses nommées des théorèmes, jamais des champs. -/
structure K where
  DeclaredDisjoint : List Nat → List Nat → Prop
  SharedMutable : Nat → Prop
  Pinned : Nat → Prop
  Invalidates : Nat → Nat → Prop

/-- Obligation de `DeclaredDisjoint` (MM-03.3.8) : une déclaration de disjonction ne couvre
jamais deux régions qui se chevauchent réellement. -/
def DDSound (k : K) : Prop := ∀ r r', k.DeclaredDisjoint r r' → ∀ l ∈ r, l ∉ r'

/-- État `S3 = (F, P, I, A, D)` (MM-03.3 §1), sans composante `M` (arbitrage 1). `nF` est la
prochaine identité de cadre, pour que l'identité d'un cadre sorti ne soit jamais réutilisée.
`I` est total sur les identités ; seules les feuilles sont lues. `D q` est la liste des ancres
de l'emplacement `q`, chaque ancre étant une identité d'autorité (arbitrage 2). -/
structure S3 where
  F : Frames
  nF : Nat
  P : List Place
  I : Nat → InitSt
  A : List Authority
  D : Nat → List Nat

/-- État initial : un cadre, aucun emplacement, aucune autorité. -/
def S3.init : S3 := ⟨[0], 1, [], fun _ => .uninit, [], fun _ => []⟩

/-- Lien `origin` de l'autorité d'indice `i` (MM-03.3.4). -/
def S3.org (s : S3) (i : Nat) : Option Nat := (s.A[i]?).bind (·.origin)

/-- Ancêtres stricts de l'autorité `i` par `origin` : `i` est descendant de chacun
(MM-03.3.5). -/
def S3.ancs (s : S3) (i : Nat) : List Nat := chain s.org i

/-- Autorité active, c'est-à-dire ancre valide (arbitrage 2). -/
def S3.Active (s : S3) (x : Nat) : Prop := ∃ y, s.A[x]? = some y ∧ y.active = true

instance (s : S3) (x : Nat) : Decidable (s.Active x) :=
  match h : s.A[x]? with
  | some y => if hy : y.active = true then isTrue ⟨y, h, hy⟩
    else isFalse fun ⟨y', h', hy'⟩ => by rw [h] at h'; cases h'; exact hy hy'
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; cases h'

/-- Emplacement encore utilisable : il existe et son cadre est sur la pile (MM-03.3.1 : un
emplacement local n'est pas utilisable après la sortie de son cadre). -/
def S3.Usable (s : S3) (q : Nat) : Prop := ∃ f, placeFrame s.P q = some f ∧ f ∈ s.F

instance (s : S3) (q : Nat) : Decidable (s.Usable q) :=
  match h : placeFrame s.P q with
  | some f => if hf : f ∈ s.F then isTrue ⟨f, h, hf⟩
    else isFalse fun ⟨f', h', hf'⟩ => by rw [h] at h'; cases h'; exact hf hf'
  | none => isFalse fun ⟨_, h', _⟩ => by rw [h] at h'; cases h'

/-! ## Autorité effective (MM-03.3.5) -/

/-- Modes des descendants actifs de `a` dont l'empreinte couvre la feuille `p` (MM-03.3.5). -/
def descModes (s : S3) (a p : Nat) : List Mode :=
  (List.range s.A.length).filterMap fun j =>
    match s.A[j]? with
    | some y => if y.active = true ∧ p ∈ y.footprint ∧ a ∈ s.ancs j then some y.mode else none
    | none => none

/-- Cas 1 à 3 de MM-03.3.5 pour une autorité active couvrant la feuille, de mode `m`, dont
les descendants actifs couvrants ont les modes `ds`. -/
def effOf (m : Mode) (ds : List Mode) : Option Mode :=
  if ds = [] then some m else if Mode.modify ∈ ds then none else some .observe

/-- `effective(a, p)` (MM-03.3.5), calculé feuille par feuille, sans statut stocké
(arbitrage 4) : absente si `a` est inactive ou ne couvre pas `p`, sinon `effOf`. -/
def effective (s : S3) (a p : Nat) : Option Mode :=
  match s.A[a]? with
  | some x => if x.active = true ∧ p ∈ x.footprint then effOf x.mode (descModes s a p) else none
  | none => none

/-- Compatibilité des modes effectifs pour les accès ordinaires (MM-03.3 §2, I1) : seul le
couple `Observe` / `Observe` est compatible. -/
def Compat (m₁ m₂ : Mode) : Prop := m₁ = .observe ∧ m₂ = .observe

/-! ## Invariants (MM-03.3 §2) -/

/-- I1, exclusivité effective (MM-03.3 §2), sur les modes effectifs (arbitrage 4). Une autorité
de mode effectif présent est active. -/
def I1 (s : S3) : Prop :=
  ∀ a b p m₁ m₂, a ≠ b → effective s a p = some m₁ → effective s b p = some m₂ → Compat m₁ m₂

/-- I2, conservation des autorités (MM-03.3 §2) : l'origine d'une autorité dérivée existe, et
sur chaque feuille de l'empreinte dérivée, cette feuille est dans l'empreinte de l'origine et le
mode dérivé n'excède pas le sien. -/
def I2 (s : S3) : Prop :=
  ∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a →
    ∃ x : Authority, s.A[a]? = some x ∧ ∀ p ∈ y.footprint, p ∈ x.footprint ∧ y.mode.le x.mode

/-- I3, validité des dépendances (MM-03.3 §2) : toute ancre d'un emplacement encore utilisable
est valide, c'est-à-dire active (arbitrage 2). -/
def I3 (s : S3) : Prop := ∀ q, s.Usable q → ∀ x ∈ s.D q, s.Active x

/-- Dépendances encore valides des valeurs contenant la feuille `p` (MM-03.3 §5 : « les
dépendances nécessaires sont valides ») : toute ancre d'un emplacement dont `p` fait partie est
active. -/
def DepsValid (s : S3) (p : Nat) : Prop :=
  ∀ q ∈ List.range s.P.length, partOf s.P p q → ∀ x ∈ s.D q, s.Active x

instance (s : S3) (p : Nat) : Decidable (DepsValid s p) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))

/-- Condition de lecture ordinaire d'une feuille par l'autorité `a` (MM-03.3 §5, `canRead3`) :
une autorité effective permet l'observation, la feuille est initialisée, les dépendances
nécessaires sont valides. La condition de contrat de type et de stockage n'est pas
représentée (types hors périmètre). -/
def CanReadLeaf (s : S3) (a p : Nat) : Prop :=
  effective s a p ≠ none ∧ s.I p = .init ∧ DepsValid s p

instance (s : S3) (a p : Nat) : Decidable (CanReadLeaf s a p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- I4, validité des valeurs consommées (MM-03.3 §2), première phrase, comme prédicat d'état :
aucune feuille `Moved` n'est lisible. Les deux autres phrases portent sur `transfer` et sont des
théorèmes de l'étape 4. -/
def I4 (s : S3) : Prop := ∀ a p, s.I p = .moved → ¬ CanReadLeaf s a p

/-- `Inv3 = I1 ∧ I2 ∧ I3 ∧ I4` (MM-03.3 §2). -/
def Inv3 (s : S3) : Prop := I1 s ∧ I2 s ∧ I3 s ∧ I4 s

/-- I4 tient dans tout état : la condition de lecture exige `Init` (MM-03.3 §2, I4 ; §5). -/
theorem i4_always (s : S3) : I4 s := fun _ _ hm h => by rw [h.2.1] at hm; cases hm

end Ern.MM03
