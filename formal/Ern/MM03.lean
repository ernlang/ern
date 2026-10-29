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

/-! ## Issues et relations gardées (MM-03.3 §3) -/

/-- `Outcome3` (MM-03.3 §3) : `ok` avec le nouvel état, ou `reject`, refus de la discipline
statique, distinct de l'échec défini d'une abstraction et du `ub` de MM-02 (arbitrage 6). -/
inductive Outcome3 (σ : Type) where
  | ok (s : σ)
  | reject

/-- Forme commune des règles de transition de MM-03.3 §3–5 : `ok` avec l'effet si la
précondition tient, `reject` sinon. -/
inductive Guarded {σ : Type} (Pre : Prop) (eff : σ) : Outcome3 σ → Prop where
  | ok : Pre → Guarded Pre eff (.ok eff)
  | reject : ¬ Pre → Guarded Pre eff .reject

theorem Guarded.det {σ : Type} {Pre : Prop} {eff : σ} {o₁ o₂ : Outcome3 σ}
    (h₁ : Guarded Pre eff o₁) (h₂ : Guarded Pre eff o₂) : o₁ = o₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | contradiction

theorem Guarded.ok_iff {σ : Type} {Pre : Prop} {eff s' : σ} :
    Guarded Pre eff (.ok s') ↔ Pre ∧ s' = eff :=
  ⟨fun h => by cases h; exact ⟨‹_›, rfl⟩, fun ⟨h, e⟩ => e ▸ .ok h⟩

theorem Guarded.reject_iff {σ : Type} {Pre : Prop} {eff : σ} :
    Guarded Pre eff .reject ↔ ¬ Pre :=
  ⟨fun h => by cases h; assumption, fun h => .reject h⟩

/-! ## Aides décidables -/

/-- Prédicat sur une valeur optionnelle : `P y` si elle vaut `some y`, `d` sinon. -/
def OptP {α : Type} (o : Option α) (P : α → Prop) (d : Prop) : Prop :=
  match o with
  | some y => P y
  | none => d

instance {α : Type} (o : Option α) (P : α → Prop) (d : Prop) [DecidablePred P] [Decidable d] :
    Decidable (OptP o P d) :=
  match o with
  | some y => inferInstanceAs (Decidable (P y))
  | none => inferInstanceAs (Decidable d)

/-- Le mode effectif `e` permet le mode demandé `m` : présent et non excédé (MM-03.3 §3, O1.3). -/
def Allows (e : Option Mode) (m : Mode) : Prop := OptP e (fun e => m.le e) False

/-- Empreinte de l'autorité `a`, vide si elle n'existe pas. -/
def S3.afp (s : S3) (a : Nat) : List Nat := match s.A[a]? with
  | some x => x.footprint
  | none => []

/-- Cadre détenteur de l'autorité `x` (MM-03.3.4, champ `frame`). -/
def S3.frameOf (s : S3) (x : Nat) : Option Nat := (s.A[x]?).map (·.frame)

/-- Cadre courant : la tête de la pile (MM-03.3.1). -/
def S3.top (s : S3) : Nat := s.F.headD 0

/-- Ajout d'une autorité en fin de `A` : sa nouvelle identité est `s.A.length`. -/
def S3.addAuth (s : S3) (y : Authority) : S3 := { s with A := s.A ++ [y] }

/-- Restriction de non-échappement (MM-03.3.6) pour l'ancre `x` et une destination de cadre
`fd` : si `x` est une ancre locale, le cadre de `x` est `fd` ou l'un de ses ancêtres, donc
`fd` ne lui survit pas. Une ancre est dite locale quand elle n'a pas d'origine (autorité
racine d'un emplacement) ; une ancre dérivée est traitée à `exitFrame` (arbitrage 1). -/
def NoEscape (s : S3) (x : Nat) (fd : Option Nat) : Prop :=
  OptP (s.A[x]?) (fun y => OptP fd (fun f => y.origin = none → ancestor s.F y.frame f) True) True

/-- Dépendances de la valeur en `q`, héritées de ses parties (MM-03.3.6 : la valeur contenante
hérite des dépendances des valeurs contenues). -/
def depsOf (s : S3) (q : Nat) : List Nat :=
  ((List.range s.P.length).filter fun r => decide (partOf s.P r q)).flatMap s.D

/-! ## O1 `derive` (MM-03.3 §3) -/

/-- Effet de `derive(source, place, mode)` (MM-03.3 §3, O1) : nouvelle autorité active
d'origine `src`, d'empreinte `footprint place`, de mode `m`, détenue par le cadre courant. -/
def deriveEff (s : S3) (src q : Nat) (m : Mode) : S3 :=
  s.addAuth ⟨m, some src, footprint s.P q, s.top, true⟩

/-- Préconditions de `derive` (MM-03.3 §3, O1), dans l'ordre : 1 origine active ; emplacement
encore utilisable (MM-03.3.1) ; 2 empreinte demandée incluse dans celle de l'origine ; 3 mode
permis par l'autorité effective de l'origine sur chaque feuille ; 4 toute autorité existante
reste compatible avec l'autorité dérivée dans l'état résultant. O1.5 n'est pas reprise :
`derive` ne désactive aucune autorité (`derive_keeps_active`). -/
def DerivePre (s : S3) (src q : Nat) (m : Mode) : Prop :=
  s.Active src ∧ s.Usable q ∧
  (∀ p ∈ footprint s.P q, p ∈ s.afp src) ∧
  (∀ p ∈ footprint s.P q, Allows (effective s src p) m) ∧
  (∀ b ∈ List.range s.A.length, ∀ p ∈ footprint s.P q,
    OptP (effective (deriveEff s src q m) b p) (fun e => Compat e m) True)

instance (s : S3) (src q : Nat) (m : Mode) : Decidable (DerivePre s src q m) := by
  unfold DerivePre Allows Compat; infer_instance

/-- `derive` comme relation (MM-03.3 §3, O1). -/
def DeriveStep (src q : Nat) (m : Mode) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DerivePre s src q m) (deriveEff s src q m)

/-! ## O2 `split` (MM-03.3 §3) -/

/-- Effet de `split(source, regions)` (MM-03.3 §3, O2) : une autorité de modification dérivée
de `src` par région, détenue par le cadre courant ; l'origine reste une autorité logique. -/
def splitEff (s : S3) (src : Nat) (rs : List (List Nat)) : S3 :=
  { s with A := s.A ++ rs.map fun r => ⟨.modify, some src, r, s.top, true⟩ }

/-- Droit exclusif déjà distribué par `src` sur la feuille `p` : un descendant actif de `src`
en mode `Modify` couvrant `p` (MM-03.3 §3, O2.4). -/
def DistribExcl (s : S3) (src j p : Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ src ∈ s.ancs j ∧ p ∈ y.footprint ∧ y.mode = .modify)
    False

/-- Préconditions de `split` (MM-03.3 §3, O2), dans l'ordre : 1 autorité effective de
modification de l'origine sur chaque feuille des régions ; 2 régions dans l'empreinte disponible,
c'est-à-dire l'empreinte de l'origine où son autorité effective est présente ; 3 régions deux à
deux disjointes, structurellement (sans feuille commune) ou par `DeclaredDisjoint` (MM-03.3.8) ;
4 aucune région ne recouvre un droit exclusif déjà distribué. O2.5 n'est pas reprise : `split`
ne modifie ni `D` ni l'activité des autorités. -/
def SplitPre (k : K) (s : S3) (src : Nat) (rs : List (List Nat)) : Prop :=
  (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify) ∧
  (∀ r ∈ rs, ∀ p ∈ r, p ∈ s.afp src ∧ effective s src p ≠ none) ∧
  rs.Pairwise (fun r r' => (∀ l ∈ r, l ∉ r') ∨ k.DeclaredDisjoint r r') ∧
  (∀ r ∈ rs, ∀ p ∈ r, ∀ j ∈ List.range s.A.length, ¬ DistribExcl s src j p)

instance (k : K) [∀ r r', Decidable (k.DeclaredDisjoint r r')] (s : S3) (src : Nat)
    (rs : List (List Nat)) : Decidable (SplitPre k s src rs) := by
  unfold SplitPre DistribExcl; infer_instance

/-- `split` comme relation (MM-03.3 §3, O2). -/
def SplitStep (k : K) (src : Nat) (rs : List (List Nat)) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (SplitPre k s src rs) (splitEff s src rs)

/-! ## O3 `release` (MM-03.3 §3) -/

/-- Effet de `release(authority)` (MM-03.3 §3, O3) : l'autorité devient inactive ; les
autorités effectives de ses ancêtres sont recalculées par `effective`. -/
def releaseEff (s : S3) (a : Nat) : S3 := match s.A[a]? with
  | some x => { s with A := s.A.set a { x with active := false } }
  | none => s

/-- Préconditions de `release` (MM-03.3 §3, O3), dans l'ordre : 1 autorité active ; 2 aucun
descendant actif ; 3 aucun emplacement encore utilisable n'a `a` pour ancre. O3.4 (garanties
des abstractions associées) n'est pas représentée dans le noyau. -/
def ReleasePre (s : S3) (a : Nat) : Prop :=
  s.Active a ∧
  (∀ j ∈ List.range s.A.length, a ∈ s.ancs j → ¬ s.Active j) ∧
  (∀ q ∈ List.range s.P.length, s.Usable q → a ∉ s.D q)

instance (s : S3) (a : Nat) : Decidable (ReleasePre s a) := by unfold ReleasePre; infer_instance

/-- `release` comme relation (MM-03.3 §3, O3). -/
def ReleaseStep (a : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (ReleasePre s a) (releaseEff s a)

/-! ## O4 `transfer` (MM-03.3 §3) -/

/-- Effet de `transfer(source, destination)` (MM-03.3 §3, O4). Les autorités transférées `auths`
sont un argument : l'état ne dit pas quelles autorités une valeur contient. Effets : la
destination devient `Init`, la source `Moved` ; les dépendances de la source (héritées comprises)
s'ajoutent à la destination et quittent la source et ses parties ; `auths` change de cadre
détenteur sans être dupliquée. -/
def transferEff (s : S3) (src dst : Nat) (auths : List Nat) : S3 :=
  { s with
    I := fun l => if l ∈ footprint s.P dst then .init
      else if l ∈ footprint s.P src then .moved else s.I l
    D := fun q => if q = dst then s.D dst ++ depsOf s src
      else if partOf s.P q src then [] else s.D q
    A := s.A.mapIdx fun j y => if j ∈ auths then { y with frame := (placeFrame s.P dst).getD 0 }
      else y }

/-- Accès actif dérivé couvrant une feuille de `ls` (MM-03.3 §3, O4.4). -/
def ActiveDerivedOn (s : S3) (j : Nat) (ls : List Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ y.origin ≠ none ∧ ∃ l ∈ y.footprint, l ∈ ls) False

/-- Préconditions de `transfer` (MM-03.3 §3, O4), dans l'ordre : source encore utilisable
(MM-03.3.1) et 1 initialisée ; 2 destination encore utilisable, sans valeur initialisée, sans
feuille commune avec la source, et autorités transférées actives et détenues par le cadre de la
source ; 4 aucun accès actif dérivé, hors `auths`, sur la source ; 5 ancres de la valeur
valides ; 6 non-échappement (MM-03.3.6) vers le cadre de la destination ; 7 aucune feuille de la
source épinglée (`Pinned`, MM-03.3.8). O4.3 tient par construction
(`transfer_no_duplicate_authority`). -/
def TransferPre (k : K) (s : S3) (src dst : Nat) (auths : List Nat) : Prop :=
  s.Usable src ∧ (∀ l ∈ footprint s.P src, s.I l = .init) ∧
  s.Usable dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ ¬ overlap s.P src dst ∧
  (∀ b ∈ auths, s.Active b ∧ s.frameOf b = placeFrame s.P src) ∧
  (∀ j ∈ List.range s.A.length, j ∉ auths → ¬ ActiveDerivedOn s j (footprint s.P src)) ∧
  (∀ x ∈ depsOf s src, s.Active x) ∧
  (∀ x ∈ depsOf s src, NoEscape s x (placeFrame s.P dst)) ∧
  (∀ l ∈ footprint s.P src, ¬ k.Pinned l)

instance (k : K) [DecidablePred k.Pinned] (s : S3) (src dst : Nat) (auths : List Nat) :
    Decidable (TransferPre k s src dst auths) := by
  unfold TransferPre ActiveDerivedOn NoEscape; infer_instance

/-- `transfer` comme relation (MM-03.3 §3, O4). -/
def TransferStep (k : K) (src dst : Nat) (auths : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (TransferPre k s src dst auths) (transferEff s src dst auths)

/-! ## O5 `depend` (MM-03.3 §3) -/

/-- Effet de `depend(result, anchor)` (MM-03.3 §3, O5) : l'ancre s'ajoute aux dépendances de
l'emplacement résultat ; les dépendances existantes sont conservées ; la propagation aux valeurs
contenantes est calculée par `depsOf`. -/
def dependEff (s : S3) (q x : Nat) : S3 :=
  { s with D := fun r => if r = q then s.D q ++ [x] else s.D r }

/-- Préconditions de `depend` (MM-03.3 §3, O5), dans l'ordre : emplacement résultat encore
utilisable (MM-03.3.1) ; 1 ancre valide ; 5 non-échappement (MM-03.3.6). O5.2 (origine réelle
des droits ou du stockage) n'est pas représentable : l'état ne relie pas une valeur à
l'origine de son contenu. O5.3 et O5.4 tiennent par construction. -/
def DependPre (s : S3) (q x : Nat) : Prop :=
  s.Usable q ∧ s.Active x ∧ NoEscape s x (placeFrame s.P q)

instance (s : S3) (q x : Nat) : Decidable (DependPre s q x) := by
  unfold DependPre NoEscape; infer_instance

/-- `depend` comme relation (MM-03.3 §3, O5). -/
def DependStep (q x : Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (DependPre s q x) (dependEff s q x)

/-! ## O6 `enterFrame` (MM-03.3 §4) -/

/-- Effet de `enterFrame` (MM-03.3 §4, O6) avec les emplacements locaux `ls` (parent, kind) :
nouveau cadre `nF` empilé ; emplacements ajoutés dans ce cadre, non initialisés, sans
dépendance ; une autorité racine `Modify` active par emplacement racine (arbitrage 2), sur son
empreinte. Les paramètres `let`/`inout` sont des `derive` exécutés dans le nouveau cadre, les
paramètres `sink` des `transfer` (arbitrage 1). -/
def enterEff (s : S3) (ls : List (Option Nat × Nat)) : S3 :=
  let n := s.P.length
  let P' := s.P ++ ls.map fun pk => ⟨pk.1, s.nF, pk.2⟩
  { F := s.nF :: s.F, nF := s.nF + 1, P := P'
    I := fun l => if n ≤ l then .uninit else s.I l
    A := s.A ++ ((List.range ls.length).filter fun i => ((ls[i]?).bind (·.1)).isNone).map
      fun i => ⟨.modify, none, footprint P' (n + i), s.nF, true⟩
    D := fun q => if n ≤ q then [] else s.D q }

/-- Préconditions de `enterFrame` (MM-03.3 §4, O6) : le cadre appelant est actif (la pile n'est
pas vide) ; le parent d'un emplacement local est un emplacement local qui le précède. -/
def EnterPre (s : S3) (ls : List (Option Nat × Nat)) : Prop :=
  s.F ≠ [] ∧ ∀ i ∈ List.range ls.length,
    OptP ((ls[i]?).bind (·.1)) (fun r => s.P.length ≤ r ∧ r < s.P.length + i) True

instance (s : S3) (ls : List (Option Nat × Nat)) : Decidable (EnterPre s ls) := by
  unfold EnterPre; infer_instance

/-- `enterFrame` comme relation (MM-03.3 §4, O6). -/
def EnterStep (ls : List (Option Nat × Nat)) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (EnterPre s ls) (enterEff s ls)

/-! ## O7 `exitFrame` (MM-03.3 §4, arbitrage 1) -/

/-- Ré-ancrage possible de `x` (arbitrage 1) : son origine est active et détenue par un cadre
survivant de `F₀`. -/
def Reanch (s : S3) (F₀ : Frames) (x : Nat) : Prop :=
  OptP (s.org x) (fun o => s.Active o ∧ OptP (s.frameOf o) (· ∈ F₀) False) False

/-- Ancre `x` après la sortie du cadre `f` : son origine si `x` est détenue par `f`
(arbitrage 1). -/
def reanchor (s : S3) (f x : Nat) : Nat :=
  if s.frameOf x = some f then (s.org x).getD x else x

/-- Emplacement d'un cadre survivant de `F₀`. -/
def UsableIn (s : S3) (F₀ : Frames) (q : Nat) : Prop := OptP (placeFrame s.P q) (· ∈ F₀) False

/-- Préconditions de `exitFrame` (MM-03.3 §4, O7, et arbitrage 1) : le cadre sortant `f` a un
appelant ; 3 toute ancre détenue par `f` d'une valeur encore utilisable dans un cadre survivant
est ré-ancrable sur son origine ; 4 toute autorité active d'un cadre survivant dont l'origine est
détenue par `f` est rattachable à l'origine de celle-ci (MM-03.3.7). O7.1, O7.2 et O7.5 ne sont
pas reprises : les transferts sont vérifiés par `transfer`, les autorités restantes sont
restituées par l'effet, le nettoyage est hors périmètre. -/
def ExitPre (s : S3) : Prop :=
  match s.F with
  | f :: F₀ => F₀ ≠ [] ∧
      (∀ q ∈ List.range s.P.length, UsableIn s F₀ q →
        ∀ x ∈ s.D q, s.frameOf x = some f → Reanch s F₀ x) ∧
      (∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => y.active = true → y.frame ≠ f →
        OptP y.origin (fun x => s.frameOf x = some f → Reanch s F₀ x) True) True)
  | [] => False

instance (s : S3) (F₀ : Frames) (x : Nat) : Decidable (Reanch s F₀ x) := by
  unfold Reanch; infer_instance

instance (s : S3) (F₀ : Frames) (q : Nat) : Decidable (UsableIn s F₀ q) := by
  unfold UsableIn; infer_instance

instance (s : S3) : Decidable (ExitPre s) := by
  unfold ExitPre; split <;> infer_instance

/-- Effet de `exitFrame` (MM-03.3 §4, O7, arbitrage 1) : retour à l'appelant ; ancres détenues
par `f` remplacées par leur origine ; autorités détenues par `f` restituées (inactives) ;
autorités actives survivantes d'origine détenue par `f` rattachées à l'origine de celle-ci. -/
def exitEff (s : S3) : S3 :=
  match s.F with
  | f :: F₀ =>
    { s with
      F := F₀
      D := fun q => (s.D q).map (reanchor s f)
      A := s.A.map fun y => if y.frame = f then { y with active := false }
        else if y.active = true ∧ y.origin.bind s.frameOf = some f then
          { y with origin := y.origin.bind s.org } else y }
  | [] => s

/-- `exitFrame` comme relation (MM-03.3 §4, O7). -/
def ExitStep (s : S3) : Outcome3 S3 → Prop := Guarded (ExitPre s) (exitEff s)

/-! ## Lecture et écriture abstraites (MM-03.3 §5) -/

/-- `canRead3` (MM-03.3 §5) : lecture ordinaire des feuilles `ls` par l'autorité `a`. -/
def canRead3 (s : S3) (a : Nat) (ls : List Nat) : Prop := ∀ p ∈ ls, CanReadLeaf s a p

instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (canRead3 s a ls) := by
  unfold canRead3; infer_instance

/-- `read3` comme relation (MM-03.3 §5) : la lecture ne modifie pas l'état. -/
def Read3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (canRead3 s a ls) s

/-- `canWrite3` (MM-03.3 §5) : sur chaque feuille, autorité effective de modification de `a`,
aucune autre autorité de mode effectif présent (tout mode est incompatible avec `Modify`),
dépendances nécessaires valides. La condition de type et de stockage n'est pas représentée. -/
def canWrite3 (s : S3) (a : Nat) (ls : List Nat) : Prop :=
  ∀ p ∈ ls, effective s a p = some .modify ∧
    (∀ b ∈ List.range s.A.length, b ≠ a → effective s b p = none) ∧ DepsValid s p

instance (s : S3) (a : Nat) (ls : List Nat) : Decidable (canWrite3 s a ls) := by
  unfold canWrite3; infer_instance

/-- Effet d'une écriture (MM-03.3 §5) : les feuilles écrites deviennent `Init`. -/
def write3Eff (s : S3) (ls : List Nat) : S3 := { s with I := fun p => if p ∈ ls then .init else s.I p }

/-- `write3` comme relation (MM-03.3 §5). -/
def Write3Step (a : Nat) (ls : List Nat) (s : S3) : Outcome3 S3 → Prop :=
  Guarded (canWrite3 s a ls) (write3Eff s ls)

/-! ## Déterminisme et issues `ok` (MM-03.3 §3–5) -/

/-- Déterminisme de `derive` (MM-03.3, O1). -/
theorem derive_det {src q : Nat} {m : Mode} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : DeriveStep src q m s o₁) (h₂ : DeriveStep src q m s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `derive` (MM-03.3, O1). -/
theorem derive_ok_iff {src q : Nat} {m : Mode} {s s' : S3} :
    DeriveStep src q m s (.ok s') ↔ DerivePre s src q m ∧ s' = deriveEff s src q m := Guarded.ok_iff

/-- Déterminisme de `split` (MM-03.3, O2). -/
theorem split_det {k : K} {src : Nat} {rs : List (List Nat)} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : SplitStep k src rs s o₁) (h₂ : SplitStep k src rs s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `split` (MM-03.3, O2). -/
theorem split_ok_iff {k : K} {src : Nat} {rs : List (List Nat)} {s s' : S3} :
    SplitStep k src rs s (.ok s') ↔ SplitPre k s src rs ∧ s' = splitEff s src rs := Guarded.ok_iff

/-- Déterminisme de `release` (MM-03.3, O3). -/
theorem release_det {a : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ReleaseStep a s o₁) (h₂ : ReleaseStep a s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `release` (MM-03.3, O3). -/
theorem release_ok_iff {a : Nat} {s s' : S3} :
    ReleaseStep a s (.ok s') ↔ ReleasePre s a ∧ s' = releaseEff s a := Guarded.ok_iff

/-- Déterminisme de `transfer` (MM-03.3, O4). -/
theorem transfer_det {k : K} {src dst : Nat} {auths : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : TransferStep k src dst auths s o₁) (h₂ : TransferStep k src dst auths s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `transfer` (MM-03.3, O4). -/
theorem transfer_ok_iff {k : K} {src dst : Nat} {auths : List Nat} {s s' : S3} :
    TransferStep k src dst auths s (.ok s') ↔ TransferPre k s src dst auths ∧ s' = transferEff s src dst auths := Guarded.ok_iff

/-- Déterminisme de `depend` (MM-03.3, O5). -/
theorem depend_det {q x : Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : DependStep q x s o₁) (h₂ : DependStep q x s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `depend` (MM-03.3, O5). -/
theorem depend_ok_iff {q x : Nat} {s s' : S3} :
    DependStep q x s (.ok s') ↔ DependPre s q x ∧ s' = dependEff s q x := Guarded.ok_iff

/-- Déterminisme de `enter` (MM-03.3, O6). -/
theorem enter_det {ls : List (Option Nat × Nat)} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : EnterStep ls s o₁) (h₂ : EnterStep ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `enter` (MM-03.3, O6). -/
theorem enter_ok_iff {ls : List (Option Nat × Nat)} {s s' : S3} :
    EnterStep ls s (.ok s') ↔ EnterPre s ls ∧ s' = enterEff s ls := Guarded.ok_iff

/-- Déterminisme de `exit` (MM-03.3, O7). -/
theorem exit_det  {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : ExitStep s o₁) (h₂ : ExitStep s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `exit` (MM-03.3, O7). -/
theorem exit_ok_iff  {s s' : S3} :
    ExitStep s (.ok s') ↔ ExitPre s ∧ s' = exitEff s := Guarded.ok_iff

/-- Déterminisme de `read3` (MM-03.3, §5). -/
theorem read3_det {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : Read3Step a ls s o₁) (h₂ : Read3Step a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `read3` (MM-03.3, §5). -/
theorem read3_ok_iff {a : Nat} {ls : List Nat} {s s' : S3} :
    Read3Step a ls s (.ok s') ↔ canRead3 s a ls ∧ s' = s := Guarded.ok_iff

/-- Déterminisme de `write3` (MM-03.3, §5). -/
theorem write3_det {a : Nat} {ls : List Nat} {s : S3} {o₁ o₂ : Outcome3 S3}
    (h₁ : Write3Step a ls s o₁) (h₂ : Write3Step a ls s o₂) : o₁ = o₂ := Guarded.det h₁ h₂

/-- Issue `ok` de `write3` (MM-03.3, §5). -/
theorem write3_ok_iff {a : Nat} {ls : List Nat} {s s' : S3} :
    Write3Step a ls s (.ok s') ↔ canWrite3 s a ls ∧ s' = write3Eff s ls := Guarded.ok_iff

end Ern.MM03
