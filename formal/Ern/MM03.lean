import Ern.MM02

/-!
# MM-03.3 v0.2 : noyau de la discipline d'accès (modèle exploratoire, jalon 1)

Couche abstraite de `formal/DESIGN.md` (« Abstract model ») : la mémoire est un arbre fini
d'emplacements. Le raffinement vers MM-02 (MM-03.3 §9) est le jalon 2 et n'est pas traité ici ;
le module importe `Ern.MM02` sans l'utiliser ni le modifier. Fragment couvert : exécution
séquentielle des opérations du noyau (MM-03.3 §3–5) et de l'arène (§6) ; ni concurrence, ni
handles, ni nettoyage différé.

Chaque opération est une relation `… → S3 → Outcome3 S3` de forme `Guarded` : `ok` avec l'effet
si sa précondition tient, `reject` sinon (MM-03.3 §3, arbitrage 6). `Inv3` seul n'est pas
inductif (`inv3_not_inductive`) ; les préservations par `release`, `enterFrame` et `exitFrame`
sont énoncées sous l'invariant structurel
`WF3`, établi pour tout état atteint sous l'obligation `DDSound`
(`reachable_access_invariant_underDD`). Les théorèmes
conditionnés à une obligation de `K` portent le suffixe `_underDD` ou `_underInv` (arbitrage 5).
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

/-- Contrats `K` (MM-03.3.8), fixés pour l'exécution (arbitrage 5). Les types sont un choix de
représentation : régions comme listes de feuilles, feuilles, et `Invalidates s r x` pour
« dans l'état `s`, l'opération invalidante de la ressource `r` invalide l'ancre `x` » ; un
prédicat fixé peut dépendre de l'état. Les obligations accompagnant chaque contrat sont des
hypothèses nommées des théorèmes, jamais des champs. -/
structure K where
  DeclaredDisjoint : List Nat → List Nat → Prop
  SharedMutable : Nat → Prop
  Pinned : Nat → Prop
  Invalidates : S3 → Nat → Nat → Prop

/-- Obligation de `DeclaredDisjoint` (MM-03.3.8) : une déclaration de disjonction ne couvre
jamais deux régions qui se chevauchent réellement. -/
def DDSound (k : K) : Prop := ∀ r r', k.DeclaredDisjoint r r' → ∀ l ∈ r, l ∉ r'

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

/-- Préconditions de `split` (MM-03.3 §3, O2), dans l'ordre : 1 l'origine est une autorité
active qui possède une autorité effective de modification sur chaque feuille des régions ; 2 régions dans l'empreinte disponible,
c'est-à-dire l'empreinte de l'origine où son autorité effective est présente ; 3 régions deux à
deux disjointes, structurellement (sans feuille commune) ou par `DeclaredDisjoint` (MM-03.3.8) ;
4 aucune région ne recouvre un droit exclusif déjà distribué. O2.5 n'est pas reprise : `split`
ne modifie ni `D` ni l'activité des autorités. -/
def SplitPre (k : K) (s : S3) (src : Nat) (rs : List (List Nat)) : Prop :=
  s.Active src ∧ (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify) ∧
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

/-- `mapI f i l` applique `f` à chaque élément de `l` avec son indice, compté à partir de `i`. -/
def mapI {α β : Type} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | i, a :: l => f i a :: mapI f (i + 1) l

theorem length_mapI {α β : Type} (f : Nat → α → β) :
    ∀ (i : Nat) (l : List α), (mapI f i l).length = l.length
  | _, [] => rfl
  | i, _ :: l => by simp [mapI, length_mapI f (i + 1) l]

theorem getElem?_mapI {α β : Type} (f : Nat → α → β) :
    ∀ (i : Nat) (l : List α) (j : Nat), (mapI f i l)[j]? = (l[j]?).map (f (i + j))
  | _, [], _ => rfl
  | i, a :: l, 0 => by simp [mapI]
  | i, a :: l, j + 1 => by
    simp only [mapI, List.getElem?_cons_succ, getElem?_mapI f (i + 1) l j]
    congr 2; omega

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
    A := mapI (fun j y => if j ∈ auths then { y with frame := (placeFrame s.P dst).getD 0 }
      else y) 0 s.A }

/-- Accès actif dérivé couvrant une feuille de `ls` (MM-03.3 §3, O4.4). -/
def ActiveDerivedOn (s : S3) (j : Nat) (ls : List Nat) : Prop :=
  OptP (s.A[j]?) (fun y => y.active = true ∧ y.origin ≠ none ∧ ∃ l ∈ y.footprint, l ∈ ls) False

/-- Préconditions de `transfer` (MM-03.3 §3, O4), dans l'ordre : source encore utilisable
(MM-03.3.1) et 1 initialisée ; 2 destination encore utilisable, sans valeur initialisée, sans
feuille commune avec la source, et autorités transférées actives, détenues par le cadre de la
source et dérivées : une autorité racine reste attachée à son emplacement (arbitrage 2), et
« Une autorité dont l'origine est strictement locale au cadre appelé ne peut pas être rendue
persistante dans l'appelant par cette seule opération » (O4) ; 4 aucun accès actif dérivé, hors `auths`, sur la source ; 5 ancres de la valeur
valides ; 6 non-échappement (MM-03.3.6) vers le cadre de la destination ; 7 aucune feuille de la
source épinglée (`Pinned`, MM-03.3.8). O4.3 tient par construction
(`transfer_no_duplicate_authority`). -/
def TransferPre (k : K) (s : S3) (src dst : Nat) (auths : List Nat) : Prop :=
  s.Usable src ∧ (∀ l ∈ footprint s.P src, s.I l = .init) ∧
  s.Usable dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ ¬ overlap s.P src dst ∧
  (∀ b ∈ auths, s.Active b ∧ s.frameOf b = placeFrame s.P src ∧ s.org b ≠ none) ∧
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

/-- Emplacements après `enterFrame` : les locaux `ls` (parent, kind) ajoutés dans le cadre `nF`. -/
def enterP (s : S3) (ls : List (Option Nat × Nat)) : List Place :=
  s.P ++ ls.map fun pk => ⟨pk.1, s.nF, pk.2⟩

/-- Indices, relatifs à `ls`, des emplacements locaux racines (sans parent). -/
def rootIdx (ls : List (Option Nat × Nat)) : List Nat :=
  (List.range ls.length).filter fun i => ((ls[i]?).bind (·.1)).isNone

/-- Effet de `enterFrame` (MM-03.3 §4, O6) avec les emplacements locaux `ls` (parent, kind) :
nouveau cadre `nF` empilé ; emplacements ajoutés dans ce cadre, non initialisés, sans
dépendance ; une autorité racine `Modify` active par emplacement racine (arbitrage 2), sur son
empreinte. Les paramètres `let`/`inout` sont des `derive` exécutés dans le nouveau cadre, les
paramètres `sink` des `transfer` (arbitrage 1). -/
def enterEff (s : S3) (ls : List (Option Nat × Nat)) : S3 :=
  { F := s.nF :: s.F, nF := s.nF + 1, P := enterP s ls
    I := fun l => if s.P.length ≤ l then .uninit else s.I l
    A := s.A ++ (rootIdx ls).map
      fun i => ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), s.nF, true⟩
    D := fun q => if s.P.length ≤ q then [] else s.D q }

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

/-- Autorité après la sortie du cadre `f` (MM-03.3 §4, O7, arbitrage 1) : restituée si détenue
par `f` ; rattachée à l'origine de son origine si elle est active, survivante et d'origine
détenue par `f`. -/
def exitG (s : S3) (f : Nat) (y : Authority) : Authority :=
  if y.frame = f then { y with active := false }
  else if y.active = true ∧ y.origin.bind s.frameOf = some f then
    { y with origin := y.origin.bind s.org } else y

/-- Effet de `exitFrame` (MM-03.3 §4, O7, arbitrage 1) : retour à l'appelant ; ancres détenues
par `f` remplacées par leur origine ; autorités détenues par `f` restituées (inactives) ;
autorités actives survivantes d'origine détenue par `f` rattachées à l'origine de celle-ci. -/
def exitEff (s : S3) : S3 :=
  match s.F with
  | f :: F₀ =>
    { s with
      F := F₀
      D := fun q => (s.D q).map (reanchor s f)
      A := s.A.map (exitG s f) }
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

/-! ## Lemmes de chaînes -/

theorem chainF_none {org : Nat → Option Nat} {i : Nat} (h : org i = none) :
    ∀ k, chainF org k i = []
  | 0 => rfl
  | _ + 1 => by simp [chainF, h]

theorem chainF_fuel (org : Nat → Option Nat) :
    ∀ k₁ k₂ i, i ≤ k₁ → i ≤ k₂ → chainF org k₁ i = chainF org k₂ i
  | 0, 0, _, _, _ => rfl
  | 0, _ + 1, i, h, _ => by
    obtain rfl : i = 0 := by omega
    simp only [chainF]; split <;> simp
  | _ + 1, 0, i, _, h => by
    obtain rfl : i = 0 := by omega
    simp only [chainF]; split <;> simp
  | k₁ + 1, k₂ + 1, i, h₁, h₂ => by
    simp only [chainF]; split
    · split
      · rw [chainF_fuel org k₁ k₂ _ (by omega) (by omega)]
      · rfl
    · rfl

theorem chain_none {org : Nat → Option Nat} {i : Nat} (h : org i = none) : chain org i = [] :=
  chainF_none h i

theorem chain_cons {org : Nat → Option Nat} {i o : Nat} (h : org i = some o) (hlt : o < i) :
    chain org i = o :: chain org o := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  simp only [chain, chainF, h, hlt, ↓reduceIte]
  rw [chainF_fuel org k o o (by omega) (Nat.le_refl o)]

theorem chainF_lt {org : Nat → Option Nat} : ∀ k i j, j ∈ chainF org k i → j < i
  | 0, _, _, h => by simp [chainF] at h
  | k + 1, i, j, h => by
    simp only [chainF] at h; split at h
    · split at h
      · rcases List.mem_cons.1 h with rfl | h
        · assumption
        · exact Nat.lt_trans (chainF_lt k _ j h) ‹_›
      · simp at h
    · simp at h

theorem chain_lt {org : Nat → Option Nat} {i j : Nat} (h : j ∈ chain org i) : j < i :=
  chainF_lt i i j h

theorem chainF_congr {org org' : Nat → Option Nat} :
    ∀ k i, (∀ j ≤ i, org j = org' j) → chainF org k i = chainF org' k i
  | 0, _, _ => rfl
  | k + 1, i, h => by
    simp only [chainF]; rw [h i (Nat.le_refl i)]; split
    · split
      · rw [chainF_congr k _ fun j hj => h j (by omega)]
      · rfl
    · rfl

theorem chain_congr {org org' : Nat → Option Nat} {i : Nat} (h : ∀ j ≤ i, org j = org' j) :
    chain org i = chain org' i := chainF_congr i i h

/-- Deux racines (sans lien) d'une même chaîne sont égales. -/
theorem chainF_root {org : Nat → Option Nat} : ∀ k i r r', r ∈ chainF org k i → org r = none →
    r' ∈ chainF org k i → org r' = none → r = r'
  | 0, _, _, _, h, _, _, _ => by simp [chainF] at h
  | k + 1, i, r, r', h, hr, h', hr' => by
    simp only [chainF] at h h'; split at h
    · rename_i o ho; simp only [ho] at h'
      split at h
      · rename_i hlt; simp only [hlt, ↓reduceIte] at h'
        rcases List.mem_cons.1 h with rfl | h <;> rcases List.mem_cons.1 h' with rfl | h'
        · rfl
        · rw [chainF_none hr] at h'; simp at h'
        · rw [chainF_none hr'] at h; simp at h
        · exact chainF_root k _ r r' h hr h' hr'
      · simp at h
    · simp at h

/-! ## Lemmes sur l'autorité effective (MM-03.3.5) -/

theorem effOf_cases {m m' : Mode} {ds : List Mode} (h : effOf m ds = some m') :
    (ds = [] ∧ m' = m) ∨ (ds ≠ [] ∧ Mode.modify ∉ ds ∧ m' = .observe) := by
  unfold effOf at h
  by_cases h0 : ds = []
  · simp [h0] at h; exact .inl ⟨h0, h.symm⟩
  · by_cases h1 : Mode.modify ∈ ds
    · simp [h0, h1] at h
    · simp [h0, h1] at h; exact .inr ⟨h0, h1, h.symm⟩

theorem mode_eq_observe {m : Mode} (h : m ≠ .modify) : m = .observe := by cases m <;> simp_all

theorem mem_descModes {s : S3} {a p : Nat} {m : Mode} :
    m ∈ descModes s a p ↔ ∃ j y, s.A[j]? = some y ∧ y.active = true ∧ p ∈ y.footprint ∧
      a ∈ s.ancs j ∧ y.mode = m := by
  simp only [descModes, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨j, -, h⟩
    split at h
    · rename_i y hy
      split at h
      · rename_i hc; cases h; exact ⟨j, y, hy, hc.1, hc.2.1, hc.2.2, rfl⟩
      · cases h
    · cases h
  · rintro ⟨j, y, hy, h1, h2, h3, rfl⟩
    refine ⟨j, (List.getElem?_eq_some_iff.1 hy).1, ?_⟩
    simp [hy, h1, h2, h3]

theorem effective_some {s : S3} {a p : Nat} {m : Mode} (h : effective s a p = some m) :
    ∃ x, s.A[a]? = some x ∧ x.active = true ∧ p ∈ x.footprint ∧
      effOf x.mode (descModes s a p) = some m := by
  unfold effective at h
  split at h
  · rename_i x hx; split at h
    · rename_i hc; exact ⟨x, hx, hc.1, hc.2, h⟩
    · cases h
  · cases h

theorem effective_eq {s : S3} {a p : Nat} {x : Authority} (hx : s.A[a]? = some x)
    (ha : x.active = true) (hp : p ∈ x.footprint) :
    effective s a p = effOf x.mode (descModes s a p) := by
  simp [effective, hx, ha, hp]

theorem Mode.le_refl (m : Mode) : m.le m := by cases m <;> simp [Mode.le]

/-- Le mode effectif n'excède pas le mode de l'autorité (MM-03.3.5). -/
theorem effective_le {s : S3} {a p : Nat} {m : Mode} {x : Authority} (hx : s.A[a]? = some x)
    (h : effective s a p = some m) : m.le x.mode := by
  obtain ⟨x', hx', -, -, he⟩ := effective_some h
  rw [hx] at hx'; cases hx'
  rcases effOf_cases he with ⟨-, rfl⟩ | ⟨-, -, rfl⟩
  · exact Mode.le_refl _
  · simp [Mode.le]

/-! ## Invariant structurel `WF3`

I1 seul n'est pas préservé par `release` (`inv3_not_inductive`). La préservation par `release`,
`enterFrame` et `exitFrame` est établie sous l'invariant structurel `WF3`, qui tient dans tout
état atteint quand `DDSound k` tient (`reachable_access_invariant_underDD`).
Sa clause centrale `Tree` dit que deux autorités actives non apparentées couvrant une même
feuille sont en observation. -/

/-- Deux autorités actives distinctes, non apparentées par `origin`, couvrant une même feuille,
sont toutes deux en mode `Observe`. -/
def Tree (s : S3) : Prop :=
  ∀ (a b : Nat) (x y : Authority) (p : Nat), a ≠ b → s.A[a]? = some x → s.A[b]? = some y → x.active = true →
    y.active = true → p ∈ x.footprint → p ∈ y.footprint → a ∉ s.ancs b → b ∉ s.ancs a →
    x.mode = .observe ∧ y.mode = .observe

/-- Invariant structurel : origines antérieures, `Tree`, empreintes faites d'emplacements
existants, pile sans doublon et identités de cadres inférieures à `nF`. -/
def WF3 (s : S3) : Prop :=
  (∀ (b : Nat) (y : Authority) (a : Nat), s.A[b]? = some y → y.origin = some a → a < b) ∧
  Tree s ∧
  (∀ (a : Nat) (x : Authority), s.A[a]? = some x → ∀ l ∈ x.footprint, l < s.P.length) ∧
  s.F.Nodup ∧ (∀ f ∈ s.F, f < s.nF) ∧ (∀ (q : Nat) (pl : Place), s.P[q]? = some pl → pl.frame < s.nF)

/-- `Tree` implique I1 (MM-03.3 §2, I1) : c'est par cette voie que les opérations préservent
l'exclusivité effective. -/
theorem i1_of_tree {s : S3} (h : Tree s) : I1 s := by
  intro a b p m₁ m₂ hab ha hb
  obtain ⟨x, hx, xa, xp, ex⟩ := effective_some ha
  obtain ⟨y, hy, ya, yp, ey⟩ := effective_some hb
  have obs₁ : x.mode = .observe → m₁ = .observe := fun hm => by
    rcases effOf_cases ex with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [hm]
  have obs₂ : y.mode = .observe → m₂ = .observe := fun hm => by
    rcases effOf_cases ey with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ <;> simp [hm]
  by_cases hba : b ∈ s.ancs a
  · have hm : x.mode ∈ descModes s b p := mem_descModes.2 ⟨a, x, hx, xa, xp, hba, rfl⟩
    rcases effOf_cases ey with ⟨h0, -⟩ | ⟨-, hn, rfl⟩
    · simp [h0] at hm
    · have : x.mode = .observe := mode_eq_observe fun e => hn (e ▸ hm)
      exact ⟨obs₁ this, rfl⟩
  by_cases hab' : a ∈ s.ancs b
  · have hm : y.mode ∈ descModes s a p := mem_descModes.2 ⟨b, y, hy, ya, yp, hab', rfl⟩
    rcases effOf_cases ex with ⟨h0, -⟩ | ⟨-, hn, rfl⟩
    · simp [h0] at hm
    · have : y.mode = .observe := mode_eq_observe fun e => hn (e ▸ hm)
      exact ⟨rfl, obs₂ this⟩
  obtain ⟨h₁, h₂⟩ := h a b x y p hab hx hy xa ya xp yp hab' hba
  exact ⟨obs₁ h₁, obs₂ h₂⟩

/-- `effective_exclusive` (MM-03.3 §10) : sous I1, une autorité de mode effectif `Modify` sur
une feuille est la seule à y avoir un mode effectif présent. -/
theorem effective_exclusive {s : S3} (h : I1 s) {a b p : Nat} (hab : a ≠ b)
    (ha : effective s a p = some .modify) : effective s b p = none := by
  cases hb : effective s b p with
  | none => rfl
  | some m => exact absurd (h a b p _ _ hab ha hb).1 (by simp)

/-- Théorème central (MM-03.3 §5) : dans un état satisfaisant `Inv3`, une écriture ordinaire
autorisée ne coexiste avec aucune autre autorité de mode effectif présent sur les feuilles
écrites. La preuve n'utilise de `canWrite3` que le mode effectif `Modify` de l'écrivain. -/
theorem write3_exclusive {s s' : S3} {a : Nat} {ls : List Nat} (hinv : Inv3 s)
    (h : Write3Step a ls s (.ok s')) : ∀ p ∈ ls, ∀ b, b ≠ a → effective s b p = none := by
  intro p hp b hb
  exact effective_exclusive hinv.1 (Ne.symm hb) ((write3_ok_iff.1 h).1 p hp).1

/-- Sous I1, la seconde clause de `canWrite3` découle de la première (MM-03.3 §5). -/
theorem canWrite3_iff {s : S3} (h : I1 s) {a : Nat} {ls : List Nat} :
    canWrite3 s a ls ↔ ∀ p ∈ ls, effective s a p = some .modify ∧ DepsValid s p := by
  constructor
  · intro hw p hp; exact ⟨(hw p hp).1, (hw p hp).2.2⟩
  · intro hw p hp
    exact ⟨(hw p hp).1, fun b _ hb => effective_exclusive h (Ne.symm hb) (hw p hp).1, (hw p hp).2⟩

/-! ## Vérifications bornées de I1 et I2 -/

theorem nil_of_forall_not_mem {α : Type} : ∀ {l : List α}, (∀ a, a ∉ l) → l = []
  | [], _ => rfl
  | a :: _, h => absurd (List.mem_cons_self ..) (h a)

theorem pairwise_lt_range : ∀ n, (List.range n).Pairwise (· < ·)
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.pairwise_append]
    exact ⟨pairwise_lt_range n, by simp, fun a ha b hb => by
      simp at hb; subst hb; exact List.mem_range.1 ha⟩

theorem Mode.le_trans {a b c : Mode} (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  cases a <;> cases b <;> cases c <;> simp_all [Mode.le]

theorem Mode.le_observe {m : Mode} (h : m.le .observe) : m = .observe := by
  cases m <;> simp_all [Mode.le]

theorem lt_of_getElem? {α : Type} {l : List α} {i : Nat} {x : α} (h : l[i]? = some x) :
    i < l.length := (List.getElem?_eq_some_iff.1 h).1

/-- Forme bornée de I1, décidable. -/
def I1b (s : S3) : Prop :=
  ∀ a ∈ List.range s.A.length, ∀ b ∈ List.range s.A.length, a ≠ b → ∀ p ∈ s.afp a,
    OptP (effective s a p) (fun m₁ => OptP (effective s b p) (fun m₂ => Compat m₁ m₂) True) True

instance (s : S3) : Decidable (I1b s) := by unfold I1b Compat; infer_instance

theorem i1_of_i1b {s : S3} (h : I1b s) : I1 s := by
  intro a b p m₁ m₂ hab ha hb
  obtain ⟨x, hx, -, hp, -⟩ := effective_some ha
  obtain ⟨y, hy, -, -, -⟩ := effective_some hb
  have := h a (List.mem_range.2 (lt_of_getElem? hx)) b (List.mem_range.2 (lt_of_getElem? hy))
    hab p (by simp [S3.afp, hx, hp])
  simpa [OptP, ha, hb] using this

/-- Forme bornée de I2, décidable. -/
def I2b (s : S3) : Prop :=
  ∀ b ∈ List.range s.A.length, OptP (s.A[b]?) (fun y => OptP y.origin (fun a =>
    OptP (s.A[a]?) (fun x => ∀ p ∈ y.footprint, p ∈ x.footprint ∧ y.mode.le x.mode) False) True) True

instance (s : S3) : Decidable (I2b s) := by unfold I2b; infer_instance

theorem i2_of_i2b {s : S3} (h : I2b s) : I2 s := by
  intro b y a hy ha
  have := h b (List.mem_range.2 (lt_of_getElem? hy))
  simp only [OptP, hy, ha] at this
  split at this
  · exact ⟨_, ‹_›, this⟩
  · exact this.elim

/-! ## I1 seul n'est pas inductif -/

/-- État admissible pour `Inv3` où deux autorités racines `Modify` couvrent la même feuille,
chacune suspendue en observation par un descendant `Observe`. -/
def badS : S3 :=
  ⟨[0], 1, [⟨none, 0, 0⟩], fun _ => .uninit,
    [⟨.modify, none, [0], 0, true⟩, ⟨.modify, none, [0], 0, true⟩,
     ⟨.observe, some 0, [0], 0, true⟩, ⟨.observe, some 1, [0], 0, true⟩], fun _ => []⟩

/-- `Inv3` (MM-03.3 §2) n'est pas préservé par `release` (MM-03.3 §3, O3) : dans `badS`, qui
satisfait `Inv3`, la restitution du descendant de la première racine rend à celle-ci le mode
effectif `Modify` alors que la seconde garde `Observe`. -/
theorem inv3_not_inductive :
    Inv3 badS ∧ ReleaseStep 2 badS (.ok (releaseEff badS 2)) ∧ ¬ I1 (releaseEff badS 2) := by
  refine ⟨⟨i1_of_i1b (by decide), i2_of_i2b (by decide), fun _ _ x hx => by simp [badS] at hx,
    i4_always _⟩, .ok (by decide), fun h => ?_⟩
  have := h 0 1 0 .modify .observe (by decide) (by decide) (by decide)
  simp [Compat] at this

/-! ## Ajout d'une autorité -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr' fun b hb => h b (List.mem_cons_of_mem a hb)]

theorem addAuth_get {s : S3} {y₀ z : Authority} {j : Nat} (h : (s.addAuth y₀).A[j]? = some z) :
    (j < s.A.length ∧ s.A[j]? = some z) ∨ (j = s.A.length ∧ z = y₀) := by
  simp only [S3.addAuth] at h
  by_cases hj : j < s.A.length
  · exact .inl ⟨hj, by rwa [List.getElem?_append_left hj] at h⟩
  · rw [List.getElem?_append_right (by omega)] at h
    have : j - s.A.length = 0 := by
      have := lt_of_getElem? h; simp at this; omega
    rw [this] at h; simp at h
    exact .inr ⟨by have := lt_of_getElem? (l := s.A ++ [y₀]) (i := j) (x := z) (by
      rw [List.getElem?_append_right (by omega), this]; simp [h]); simp at this; omega, h.symm⟩

theorem addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).A[j]? = s.A[j]? := List.getElem?_append_left h

theorem addAuth_self (s : S3) (y₀ : Authority) : (s.addAuth y₀).A[s.A.length]? = some y₀ := by
  simp [S3.addAuth]

theorem ancs_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).ancs j = s.ancs j :=
  chain_congr fun i hi => by simp only [S3.org, addAuth_lt (Nat.lt_of_le_of_lt hi h)]

theorem ancs_addAuth_self {s : S3} {y₀ : Authority} {src : Nat} (ho : y₀.origin = some src)
    (hs : src < s.A.length) : (s.addAuth y₀).ancs s.A.length = src :: s.ancs src := by
  unfold S3.ancs
  rw [chain_cons (by simp [S3.org, addAuth_self, ho]) hs]
  exact congrArg _ (ancs_addAuth_lt hs)

theorem active_addAuth {s : S3} {y₀ : Authority} {x : Nat} (h : s.Active x) :
    (s.addAuth y₀).Active x := by
  obtain ⟨y, hy, ha⟩ := h; exact ⟨y, by rw [addAuth_lt (lt_of_getElem? hy)]; exact hy, ha⟩

theorem descModes_addAuth (s : S3) (y₀ : Authority) (a p : Nat) :
    descModes (s.addAuth y₀) a p = descModes s a p ++
      (if y₀.active = true ∧ p ∈ y₀.footprint ∧ a ∈ (s.addAuth y₀).ancs s.A.length
        then [y₀.mode] else []) := by
  have hl : (s.addAuth y₀).A.length = s.A.length + 1 := by simp [S3.addAuth]
  unfold descModes
  rw [hl, List.range_succ, List.filterMap_append]
  congr 1
  · refine filterMap_congr' fun j hj => ?_
    have hj' := List.mem_range.1 hj
    rw [addAuth_lt hj', ancs_addAuth_lt hj']
  · simp only [List.filterMap_cons, List.filterMap_nil, addAuth_self]
    split <;> simp_all

/-- Le mode permis par un mode effectif présent n'excède pas celui-ci. -/
theorem allows_effOf {m m' : Mode} {ds : List Mode} (h : Allows (effOf m ds) m') :
    (ds = [] ∧ m'.le m) ∨ (Mode.modify ∉ ds ∧ m' = .observe) := by
  unfold Allows OptP at h
  split at h
  · rename_i e he
    rcases effOf_cases he with ⟨h0, rfl⟩ | ⟨-, hn, rfl⟩
    · exact .inl ⟨h0, h⟩
    · exact .inr ⟨hn, Mode.le_observe h⟩
  · exact h.elim

/-- Une autorité dérivée de `src` avec un mode permis sur `p` et une autorité active couvrant
`p`, non apparentée à la nouvelle, sont en observation. -/
theorem new_vs_old {s : S3} (ht : Tree s) {src b p : Nat} {x y : Authority} {m : Mode}
    (hx : s.A[src]? = some x) (xa : x.active = true) (xp : p ∈ x.footprint)
    (hal : Allows (effective s src p) m) (hy : s.A[b]? = some y) (ya : y.active = true)
    (yp : p ∈ y.footprint) (hbs : b ≠ src) (hbn : b ∉ s.ancs src) :
    m = .observe ∧ y.mode = .observe := by
  rw [effective_eq hx xa xp] at hal
  by_cases hsb : src ∈ s.ancs b
  · have hm : y.mode ∈ descModes s src p := mem_descModes.2 ⟨b, y, hy, ya, yp, hsb, rfl⟩
    rcases allows_effOf hal with ⟨h0, -⟩ | ⟨hn, rfl⟩
    · simp [h0] at hm
    · exact ⟨rfl, mode_eq_observe fun e => hn (e ▸ hm)⟩
  · obtain ⟨h₁, h₂⟩ := ht src b x y p (Ne.symm hbs) hx hy xa ya xp yp hsb hbn
    rcases allows_effOf hal with ⟨-, hl⟩ | ⟨-, rfl⟩
    · exact ⟨Mode.le_observe (h₁ ▸ hl), h₂⟩
    · exact ⟨rfl, h₂⟩

theorem Compat.symm {m₁ m₂ : Mode} (h : Compat m₁ m₂) : Compat m₂ m₁ := ⟨h.2, h.1⟩

theorem effOf_some_of_not_mem {m : Mode} {ds : List Mode} (h : Mode.modify ∉ ds) :
    ∃ e, effOf m ds = some e := by
  unfold effOf; by_cases h0 : ds = []
  · simp [h0]
  · simp [h0, h]

/-- Ajouter une autorité ne fait que réduire les modes effectifs des autorités existantes
(MM-03.3.5) : un mode effectif présent après l'ajout l'était avant, inchangé ou devenu
`Observe`. -/
theorem effective_addAuth_old {s : S3} {y₀ : Authority} {a p : Nat} {e' : Mode}
    (ha : a < s.A.length) (h : effective (s.addAuth y₀) a p = some e') :
    ∃ e, effective s a p = some e ∧ (e' = e ∨ e' = .observe) := by
  obtain ⟨x, hx, xa, xp, he⟩ := effective_some h
  rw [addAuth_lt ha] at hx
  rw [effective_eq hx xa xp]
  rw [descModes_addAuth] at he
  split at he
  · rcases effOf_cases he with ⟨h0, -⟩ | ⟨-, hn, rfl⟩
    · simp at h0
    · obtain ⟨e, he'⟩ := effOf_some_of_not_mem (m := x.mode) fun hm => hn (List.mem_append_left _ hm)
      exact ⟨e, he', .inr rfl⟩
  · rw [List.append_nil] at he; exact ⟨e', he, .inl rfl⟩

/-- Une autorité dérivée de `src`, de mode permis par l'autorité effective de `src` sur chaque
feuille de son empreinte, préserve I1 (MM-03.3 §2, I1 ; §3, O1.3). Seul I1 est supposé. -/
theorem addAuth_I1 {s : S3} (h1 : I1 s) {src : Nat} {x : Authority} {m : Mode} {fp : List Nat}
    {f : Nat} (hx : s.A[src]? = some x) (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    I1 (s.addAuth ⟨m, some src, fp, f, true⟩) := by
  have hs := lt_of_getElem? hx
  have hn : ∀ p e, effective (s.addAuth ⟨m, some src, fp, f, true⟩) s.A.length p = some e →
      p ∈ fp ∧ e = m := by
    intro p e he
    obtain ⟨z, hz, -, zp, hze⟩ := effective_some he
    rw [addAuth_self] at hz; cases hz
    have : descModes (s.addAuth ⟨m, some src, fp, f, true⟩) s.A.length p = [] := by
      apply nil_of_forall_not_mem; intro d hd
      obtain ⟨j, y, hy, -, -, hj, -⟩ := mem_descModes.1 hd
      have h1 := chain_lt hj
      have h2 := lt_of_getElem? hy; simp [S3.addAuth] at h2; omega
    rw [this] at hze; simp [effOf] at hze; exact ⟨zp, hze.symm⟩
  have hrel : ∀ b p e, b < s.A.length → p ∈ fp → (b = src ∨ b ∈ s.ancs src) →
      effective (s.addAuth ⟨m, some src, fp, f, true⟩) b p = some e → e = .observe ∧ m = .observe := by
    intro b p e hb hp hbs he
    obtain ⟨z, hz, za, zp, hze⟩ := effective_some he
    have hm : m ∈ descModes (s.addAuth ⟨m, some src, fp, f, true⟩) b p := by
      rw [descModes_addAuth, ancs_addAuth_self rfl hs]
      simp only [hp, true_and]
      rcases hbs with rfl | hbs <;> simp_all
    rcases effOf_cases hze with ⟨h0, -⟩ | ⟨-, hnm, rfl⟩
    · simp [h0] at hm
    · exact ⟨rfl, mode_eq_observe fun e => hnm (e ▸ hm)⟩
  have hunrel : ∀ b p, b < s.A.length → ¬ (b = src ∨ b ∈ s.ancs src) →
      effective (s.addAuth ⟨m, some src, fp, f, true⟩) b p = effective s b p := by
    intro b p hb hbs
    unfold effective; rw [addAuth_lt hb, descModes_addAuth, ancs_addAuth_self rfl hs]
    have : b ∉ src :: s.ancs src := fun h => hbs (List.mem_cons.1 h)
    simp [this]
  have newold : ∀ b p e e', b < s.A.length →
      effective (s.addAuth ⟨m, some src, fp, f, true⟩) s.A.length p = some e →
      effective (s.addAuth ⟨m, some src, fp, f, true⟩) b p = some e' → Compat e e' := by
    intro b p e e' hb he he'
    obtain ⟨hp, rfl⟩ := hn p e he
    by_cases hbs : b = src ∨ b ∈ s.ancs src
    · obtain ⟨h₁, h₂⟩ := hrel b p e' hb hp hbs he'; exact ⟨h₂, h₁⟩
    · rw [hunrel b p hb hbs] at he'
      have hbs' : src ≠ b := fun h => hbs (.inl h.symm)
      have hal' := hal p hp
      unfold Allows OptP at hal'; split at hal'
      · rename_i e₀ he₀
        obtain ⟨c₁, c₂⟩ := h1 src b p e₀ e' hbs' he₀ he'
        exact ⟨Mode.le_observe (c₁ ▸ hal'), c₂⟩
      · exact hal'.elim
  intro a b p m₁ m₂ hab ha hb
  obtain ⟨_, ha', -⟩ := effective_some ha
  obtain ⟨_, hb', -⟩ := effective_some hb
  rcases addAuth_get ha' with ⟨hal₁, -⟩ | ⟨rfl, -⟩ <;> rcases addAuth_get hb' with ⟨hbl, -⟩ | ⟨rfl, -⟩
  · obtain ⟨e₁, he₁, o₁⟩ := effective_addAuth_old hal₁ ha
    obtain ⟨e₂, he₂, o₂⟩ := effective_addAuth_old hbl hb
    obtain ⟨c₁, c₂⟩ := h1 a b p e₁ e₂ hab he₁ he₂
    exact ⟨by rcases o₁ with rfl | rfl <;> first | rfl | assumption,
      by rcases o₂ with rfl | rfl <;> first | rfl | assumption⟩
  · exact (newold a p m₂ m₁ hal₁ hb ha).symm
  · exact newold b p m₁ m₂ hbl ha hb
  · exact absurd rfl hab

/-- Partie `Inv3` de `addAuth_preserves`, sans `WF3`. -/
theorem addAuth_inv3 {s : S3} (hinv : Inv3 s) {src : Nat} {x : Authority} {m : Mode}
    {fp : List Nat} {f : Nat} (hx : s.A[src]? = some x) (hfp : ∀ p ∈ fp, p ∈ x.footprint)
    (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    Inv3 (s.addAuth ⟨m, some src, fp, f, true⟩) := by
  obtain ⟨i1, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  refine ⟨addAuth_I1 i1 hx hal, fun b y a hb ho => ?_, fun q hq y hy => active_addAuth (i3 q hq y hy),
    i4_always _⟩
  rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
  · obtain ⟨x₁, hx₁, h⟩ := i2 b y a hb'' ho
    exact ⟨x₁, by rw [addAuth_lt (lt_of_getElem? hx₁)]; exact hx₁, h⟩
  · cases ho
    refine ⟨x, by rw [addAuth_lt hs]; exact hx, fun p hp => ⟨hfp p hp, ?_⟩⟩
    have := hal p hp; unfold Allows OptP at this; split at this
    · rename_i e he; exact Mode.le_trans this (effective_le hx he)
    · exact this.elim

/-- Ajout d'une autorité dérivée de `src`, active, d'empreinte incluse dans celle de `src`, de
mode permis sur chaque feuille : `WF3` et `Inv3` sont préservés. Lemme commun à `derive`,
`split` et `arena.issue`. -/
theorem addAuth_preserves {s : S3} (hwf : WF3 s) (hinv : Inv3 s) {src : Nat} {x : Authority}
    {m : Mode} {fp : List Nat} {f : Nat} (hx : s.A[src]? = some x) (xa : x.active = true)
    (hfp : ∀ p ∈ fp, p ∈ x.footprint) (hal : ∀ p ∈ fp, Allows (effective s src p) m) :
    WF3 (s.addAuth ⟨m, some src, fp, f, true⟩) ∧ Inv3 (s.addAuth ⟨m, some src, fp, f, true⟩) := by
  obtain ⟨w0, ht, w2, wn, wl, wp⟩ := hwf
  obtain ⟨-, i2, i3, -⟩ := hinv
  have hs := lt_of_getElem? hx
  have tree : Tree (s.addAuth ⟨m, some src, fp, f, true⟩) := by
    intro a b x' y' p hab ha hb xa' ya' xp yp hnab hnba
    rcases addAuth_get ha with ⟨ha', ha''⟩ | ⟨rfl, rfl⟩ <;>
      rcases addAuth_get hb with ⟨hb', hb''⟩ | ⟨rfl, rfl⟩
    · rw [ancs_addAuth_lt hb'] at hnab; rw [ancs_addAuth_lt ha'] at hnba
      exact ht a b x' y' p hab ha'' hb'' xa' ya' xp yp hnab hnba
    · rw [ancs_addAuth_self rfl hs] at hnab
      exact (new_vs_old ht hx xa (hfp p yp) (hal p yp) ha'' xa' xp
        (fun e => hnab (e ▸ List.mem_cons_self ..)) fun e => hnab (List.mem_cons_of_mem _ e)).symm
    · rw [ancs_addAuth_self rfl hs] at hnba
      exact new_vs_old ht hx xa (hfp p xp) (hal p xp) hb'' ya' yp
        (fun e => hnba (e ▸ List.mem_cons_self ..)) fun e => hnba (List.mem_cons_of_mem _ e)
    · exact absurd rfl hab
  refine ⟨⟨?_, tree, ?_, wn, wl, wp⟩, i1_of_tree tree, ?_, ?_, i4_always _⟩
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨hb', hb''⟩ | ⟨rfl, rfl⟩
    · exact w0 b y a hb'' ho
    · cases ho; exact hs
  · intro a y hy l hl
    rcases addAuth_get hy with ⟨-, hy'⟩ | ⟨-, rfl⟩
    · exact w2 a y hy' l hl
    · exact w2 src x hx l (hfp l hl)
  · intro b y a hb ho
    rcases addAuth_get hb with ⟨-, hb''⟩ | ⟨rfl, rfl⟩
    · obtain ⟨x₁, hx₁, h⟩ := i2 b y a hb'' ho
      exact ⟨x₁, by rw [addAuth_lt (lt_of_getElem? hx₁)]; exact hx₁, h⟩
    · cases ho
      refine ⟨x, by rw [addAuth_lt hs]; exact hx, fun p hp => ⟨hfp p hp, ?_⟩⟩
      obtain ⟨e, he⟩ : ∃ e, effective s src p = some e := by
        have := hal p hp; unfold Allows OptP at this; split at this
        · exact ⟨_, ‹_›⟩
        · exact this.elim
      have := hal p hp; rw [he] at this
      exact Mode.le_trans this (effective_le hx he)
  · intro q hq y hy; exact active_addAuth (i3 q hq y hy)

/-! ## États de même squelette d'autorités -/

/-- Squelette d'une autorité : tout sauf le cadre détenteur. -/
def skel (z : Authority) : Mode × Option Nat × List Nat × Bool := (z.mode, z.origin, z.footprint, z.active)

/-- `s'` a les mêmes autorités que `s` au cadre détenteur près. -/
def SameSkel (s s' : S3) : Prop :=
  s'.A.length = s.A.length ∧ ∀ j : Nat, (s'.A[j]?).map skel = (s.A[j]?).map skel

theorem SameSkel.get {s s' : S3} (h : SameSkel s s') {j : Nat} {y' : Authority}
    (hj : s'.A[j]? = some y') : ∃ y, s.A[j]? = some y ∧ skel y' = skel y := by
  have := h.2 j; rw [hj] at this
  cases hy : s.A[j]? with
  | none => rw [hy] at this; cases this
  | some y => rw [hy] at this; exact ⟨y, rfl, Option.some.inj this⟩

theorem SameSkel.get' {s s' : S3} (h : SameSkel s s') {j : Nat} {y : Authority}
    (hj : s.A[j]? = some y) : ∃ y', s'.A[j]? = some y' ∧ skel y' = skel y := by
  have := h.2 j; rw [hj] at this
  cases hy : s'.A[j]? with
  | none => rw [hy] at this; cases this
  | some y' => rw [hy] at this; exact ⟨y', rfl, Option.some.inj this⟩

theorem SameSkel.org {s s' : S3} (h : SameSkel s s') : s'.org = s.org := by
  funext j
  cases hy : s.A[j]? with
  | none =>
    cases hy' : s'.A[j]? with
    | none => simp [S3.org, hy, hy']
    | some y' => obtain ⟨y, h1, -⟩ := h.get hy'; rw [hy] at h1; cases h1
  | some y => obtain ⟨y', hy', e⟩ := h.get' hy; simp [skel] at e; simp [S3.org, hy, hy', e.2.1]

theorem SameSkel.ancs {s s' : S3} (h : SameSkel s s') : s'.ancs = s.ancs := by
  funext j; simp [S3.ancs, h.org]

theorem SameSkel.active {s s' : S3} (h : SameSkel s s') {x : Nat} : s'.Active x ↔ s.Active x := by
  constructor
  · rintro ⟨y', hy', ha⟩; obtain ⟨y, hy, he⟩ := h.get hy'
    exact ⟨y, hy, by simp [skel] at he; rw [← he.2.2.2]; exact ha⟩
  · rintro ⟨y, hy, ha⟩; obtain ⟨y', hy', he⟩ := h.get' hy
    exact ⟨y', hy', by simp [skel] at he; rw [he.2.2.2]; exact ha⟩

theorem SameSkel.descModes {s s' : S3} (h : SameSkel s s') (a p : Nat) :
    descModes s' a p = descModes s a p := by
  unfold MM03.descModes; rw [h.1, h.ancs]
  refine filterMap_congr' fun j _ => ?_
  cases hy : s.A[j]? with
  | none => have := h.2 j; rw [hy] at this; cases hy' : s'.A[j]? <;> simp_all
  | some y =>
    obtain ⟨y', hy', he⟩ := h.get' hy
    simp [skel] at he; simp [hy', he]

theorem SameSkel.effective {s s' : S3} (h : SameSkel s s') (a p : Nat) :
    effective s' a p = effective s a p := by
  unfold MM03.effective; rw [h.descModes]
  cases hy : s.A[a]? with
  | none => have := h.2 a; rw [hy] at this; cases hy' : s'.A[a]? <;> simp_all
  | some y =>
    obtain ⟨y', hy', he⟩ := h.get' hy
    simp [skel] at he; simp [hy', he]

/-- `WF3` et `Inv3` passent à un état de même squelette, mêmes emplacements, même pile, mêmes
dépendances pour les emplacements encore utilisables. -/
theorem SameSkel.preserves {s s' : S3} (h : SameSkel s s') (hP : s'.P = s.P) (hF : s'.F = s.F)
    (hn : s'.nF = s.nF) (hwf : WF3 s) (hinv : Inv3 s)
    (hD : ∀ q, s.Usable q → ∀ x ∈ s'.D q, s.Active x) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨w0, ht, w2, wn, wl, wp⟩ := hwf
  obtain ⟨-, i2, -, -⟩ := hinv
  have tree : Tree s' := by
    intro a b x' y' p hab ha hb xa ya xp yp hnab hnba
    obtain ⟨x, hx, ex⟩ := h.get ha; obtain ⟨y, hy, ey⟩ := h.get hb
    simp [skel] at ex ey; rw [h.ancs] at hnab hnba
    rw [ex.1, ey.1]
    exact ht a b x y p hab hx hy (ex.2.2.2 ▸ xa) (ey.2.2.2 ▸ ya) (ex.2.2.1 ▸ xp) (ey.2.2.1 ▸ yp)
      hnab hnba
  have us : ∀ q, s'.Usable q ↔ s.Usable q := fun q => by simp [S3.Usable, hP, hF]
  refine ⟨⟨fun b y a hb ho => ?_, tree, fun a x hx l hl => ?_, hF ▸ wn, hF ▸ hn ▸ wl,
    hP ▸ hn ▸ wp⟩, i1_of_tree tree, fun b y a hb ho => ?_,
    fun q hq x hx => h.active.2 (hD q ((us q).1 hq) x hx), i4_always _⟩
  · obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
    exact w0 b y₀ a hy₀ (e.2.1 ▸ ho)
  · obtain ⟨x₀, hx₀, e⟩ := h.get hx; simp [skel] at e
    rw [hP]; exact w2 a x₀ hx₀ l (e.2.2.1 ▸ hl)
  · obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
    obtain ⟨x₀, hx₀, hh⟩ := i2 b y₀ a hy₀ (e.2.1 ▸ ho)
    obtain ⟨x', hx', e'⟩ := h.get' hx₀; simp [skel] at e'
    exact ⟨x', hx', fun p hp => by
      rw [e.1, e'.1, e'.2.2.1]; exact hh p (e.2.2.1 ▸ hp)⟩

theorem SameSkel.refl (s : S3) : SameSkel s s := ⟨rfl, fun _ => rfl⟩

/-- `Inv3` passe à un état de même squelette, mêmes emplacements, même pile, sans `WF3`. -/
theorem SameSkel.inv3 {s s' : S3} (h : SameSkel s s') (hP : s'.P = s.P) (hF : s'.F = s.F)
    (hinv : Inv3 s) (hD : ∀ q, s.Usable q → ∀ x ∈ s'.D q, s.Active x) : Inv3 s' := by
  obtain ⟨i1, i2, -, -⟩ := hinv
  have us : ∀ q, s'.Usable q ↔ s.Usable q := fun q => by simp [S3.Usable, hP, hF]
  refine ⟨fun a b p m₁ m₂ hab ha hb => ?_, fun b y a hb ho => ?_,
    fun q hq x hx => h.active.2 (hD q ((us q).1 hq) x hx), i4_always _⟩
  · rw [h.effective] at ha hb; exact i1 a b p m₁ m₂ hab ha hb
  · obtain ⟨y₀, hy₀, e⟩ := h.get hb; simp [skel] at e
    obtain ⟨x₀, hx₀, hh⟩ := i2 b y₀ a hy₀ (e.2.1 ▸ ho)
    obtain ⟨x', hx', e'⟩ := h.get' hx₀; simp [skel] at e'
    exact ⟨x', hx', fun p hp => by
      rw [e.1, e'.1, e'.2.2.1]; exact hh p (e.2.2.1 ▸ hp)⟩

/-! ## Préservation par opération (MM-03.3 §10) -/

/-- `derive` préserve `WF3` et `Inv3` (MM-03.3 §3, O1 ; §10). La preuve n'utilise pas O1.4. -/
theorem derive_preserves {s s' : S3} {src q : Nat} {m : Mode} (hwf : WF3 s) (hinv : Inv3 s)
    (h : DeriveStep src q m s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, hfp, hal, -⟩, rfl⟩ := derive_ok_iff.1 h
  exact addAuth_preserves hwf hinv hx xa (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal

/-- `derive_preserves_exclusivity` (MM-03.3 §10) : `derive` préserve I1, sous I1 seul. La preuve
n'utilise pas O1.4. -/
theorem derive_preserves_exclusivity {s s' : S3} {src q : Nat} {m : Mode} (h1 : I1 s)
    (h : DeriveStep src q m s (.ok s')) : I1 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, -, hal, -⟩, rfl⟩ := derive_ok_iff.1 h
  exact addAuth_I1 h1 hx hal

/-- `derive` préserve `Inv3`, sans `WF3` (MM-03.3 §3, O1 ; §2). -/
theorem derive_preserves_inv3 {s s' : S3} {src q : Nat} {m : Mode} (hinv : Inv3 s)
    (h : DeriveStep src q m s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, -, hfp, hal, -⟩, rfl⟩ := derive_ok_iff.1 h
  exact addAuth_inv3 hinv hx (fun p hp => by simpa [S3.afp, hx] using hfp p hp) hal

/-- `derive` ne désactive aucune autorité : O1.5 (« Les ancres nécessaires restent valides »)
tient toujours (MM-03.3 §3, O1). -/
theorem derive_keeps_active {s : S3} {src q x : Nat} {m : Mode} (h : s.Active x) :
    (deriveEff s src q m).Active x := active_addAuth h

/-- O1.4 découle de O1.1 et O1.3 sous I1 (MM-03.3 §3, O1). -/
theorem derive_pre4_of {s : S3} {src q : Nat} {m : Mode} (hi1 : I1 s)
    (h1 : s.Active src) (h3 : ∀ p ∈ footprint s.P q, Allows (effective s src p) m) :
    ∀ b ∈ List.range s.A.length, ∀ p ∈ footprint s.P q,
      OptP (effective (deriveEff s src q m) b p) (fun e => Compat e m) True := by
  obtain ⟨x, hx, -⟩ := h1
  have hp := addAuth_I1 (f := s.top) hi1 hx h3
  intro b hb p hpq
  have hn : effective (deriveEff s src q m) s.A.length p = some m := by
    rw [deriveEff, effective_eq (addAuth_self _ _) rfl hpq]
    have : descModes (s.addAuth ⟨m, some src, footprint s.P q, s.top, true⟩) s.A.length p = [] := by
      apply nil_of_forall_not_mem; intro e he
      obtain ⟨j, y, hy, -, -, hj, -⟩ := mem_descModes.1 he
      have h1 := chain_lt hj
      have h2 := lt_of_getElem? hy; simp [S3.addAuth] at h2; omega
    simp [this, effOf]
  cases he : effective (deriveEff s src q m) b p with
  | none => trivial
  | some e => exact hp b _ p e m (by have := List.mem_range.1 hb; omega) he hn

theorem effective_addAuth_notin {s : S3} {y₀ : Authority} {a p : Nat} (ha : a < s.A.length)
    (hp : p ∉ y₀.footprint) : effective (s.addAuth y₀) a p = effective s a p := by
  unfold effective; rw [addAuth_lt ha, descModes_addAuth]; simp [hp]

theorem splitEff_cons (s : S3) (src : Nat) (r : List Nat) (rs : List (List Nat)) :
    splitEff s src (r :: rs) = splitEff (s.addAuth ⟨.modify, some src, r, s.top, true⟩) src rs := by
  simp [splitEff, S3.addAuth, S3.top]

theorem split_aux {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), WF3 s → Inv3 s →
    s.A[src]? = some x → x.active = true →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') →
    WF3 (splitEff s src rs) ∧ Inv3 (splitEff s src rs)
  | [], s, hwf, hinv, _, _, _, _ => by
    have : splitEff s src [] = s := by simp [splitEff]
    rw [this]; exact ⟨hwf, hinv⟩
  | r :: rs, s, hwf, hinv, hx, xa, hr, hpw => by
    rw [splitEff_cons]
    have hs := lt_of_getElem? hx
    obtain ⟨hwf₁, hinv₁⟩ := addAuth_preserves (f := s.top) hwf hinv hx xa
      (fun p hp => (hr r (List.mem_cons_self ..) p hp).2)
      (fun p hp => by rw [(hr r (List.mem_cons_self ..) p hp).1]; simp [Allows, OptP, Mode.le])
    obtain ⟨hpr, hpw⟩ := List.pairwise_cons.1 hpw
    refine split_aux rs _ hwf₁ hinv₁ (by rw [addAuth_lt hs]; exact hx) xa (fun r' hr' p hp => ?_) hpw
    rw [effective_addAuth_notin hs fun h => hpr r' hr' p h hp]
    exact hr r' (List.mem_cons_of_mem _ hr') p hp

/-- `split` préserve `WF3` et `Inv3` (MM-03.3 §3, O2 ; §10), conditionné à l'obligation
`DDSound k` de `DeclaredDisjoint` (MM-03.3.8). -/
theorem split_preserves_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hwf : WF3 s) (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) :
    WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, h1, h2, h3, -⟩, rfl⟩ := split_ok_iff.1 h
  refine split_aux rs s hwf hinv hx xa (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1

theorem split_aux_inv3 {src : Nat} {x : Authority} : ∀ (rs : List (List Nat)) (s : S3), Inv3 s →
    s.A[src]? = some x →
    (∀ r ∈ rs, ∀ p ∈ r, effective s src p = some .modify ∧ p ∈ x.footprint) →
    rs.Pairwise (fun r r' => ∀ l ∈ r, l ∉ r') → Inv3 (splitEff s src rs)
  | [], s, hinv, _, _, _ => by
    have : splitEff s src [] = s := by simp [splitEff]
    rw [this]; exact hinv
  | r :: rs, s, hinv, hx, hr, hpw => by
    rw [splitEff_cons]
    have hs := lt_of_getElem? hx
    have hinv₁ := addAuth_inv3 (m := .modify) (f := s.top) hinv hx (fun p hp => (hr r (List.mem_cons_self ..) p hp).2)
      (fun p hp => by rw [(hr r (List.mem_cons_self ..) p hp).1]; simp [Allows, OptP, Mode.le])
    obtain ⟨hpr, hpw⟩ := List.pairwise_cons.1 hpw
    refine split_aux_inv3 rs _ hinv₁ (by rw [addAuth_lt hs]; exact hx) (fun r' hr' p hp => ?_) hpw
    rw [effective_addAuth_notin hs fun h => hpr r' hr' p h hp]
    exact hr r' (List.mem_cons_of_mem _ hr') p hp

/-- `split` préserve `Inv3`, sans `WF3` (MM-03.3 §3, O2), conditionné à `DDSound k`
(MM-03.3.8). -/
theorem split_preserves_inv3_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨⟨x, hx, -⟩, h1, h2, h3, -⟩, rfl⟩ := split_ok_iff.1 h
  refine split_aux_inv3 rs s hinv hx (fun r hr p hp => ⟨h1 r hr p hp, ?_⟩)
    (h3.imp fun {r r'} h => h.elim id fun hd => hdd r r' hd)
  simpa [S3.afp, hx] using (h2 r hr p hp).1

/-- `split_preserves_exclusivity` (MM-03.3 §10), sous `Inv3` seul, conditionné à `DDSound k`
(MM-03.3.8). -/
theorem split_preserves_exclusivity_underDD {k : K} (hdd : DDSound k) {s s' : S3} {src : Nat}
    {rs : List (List Nat)} (hinv : Inv3 s) (h : SplitStep k src rs s (.ok s')) : I1 s' :=
  (split_preserves_inv3_underDD hdd hinv h).1

theorem set_get {l : List Authority} {a j : Nat} {x' : Authority} (ha : a < l.length) :
    (l.set a x')[j]? = if a = j then some x' else l[j]? := by
  rw [List.getElem?_set]; split <;> simp_all

theorem releaseEff_eq {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    releaseEff s a = { s with A := s.A.set a { x with active := false } } := by
  simp [releaseEff, hx]

theorem release_org {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    (releaseEff s a).org = s.org := by
  funext j; rw [releaseEff_eq hx]
  simp only [S3.org, set_get (lt_of_getElem? hx)]
  split
  · subst_vars; simp [hx]
  · rfl

theorem release_ancs {s : S3} {a : Nat} {x : Authority} (hx : s.A[a]? = some x) :
    (releaseEff s a).ancs = s.ancs := by
  funext j; simp only [S3.ancs, release_org hx]

/-- `release` préserve `WF3` et `Inv3` (MM-03.3 §3, O3 ; §10). -/
theorem release_preserves {s s' : S3} {a : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : ReleaseStep a s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨⟨x, hx, xa⟩, -, h3⟩, rfl⟩ := release_ok_iff.1 h
  obtain ⟨w0, ht, w2, wn, wl, wp⟩ := hwf
  obtain ⟨-, i2, i3, -⟩ := hinv
  have ha := lt_of_getElem? hx
  have get : ∀ j, (releaseEff s a).A[j]? = if a = j then some { x with active := false }
      else s.A[j]? := fun j => by rw [releaseEff_eq hx]; exact set_get ha
  have back : ∀ j z, (releaseEff s a).A[j]? = some z → ∃ z₀, s.A[j]? = some z₀ ∧
      z.mode = z₀.mode ∧ z.origin = z₀.origin ∧ z.footprint = z₀.footprint ∧
      (z.active = true → z₀.active = true ∧ j ≠ a) := fun j z hz => by
    rw [get] at hz; split at hz
    · subst_vars; cases hz; exact ⟨x, hx, rfl, rfl, rfl, by simp⟩
    · exact ⟨z, hz, rfl, rfl, rfl, fun hz' => ⟨hz', Ne.symm ‹_›⟩⟩
  have tree : Tree (releaseEff s a) := by
    intro a' b' x' y' p hab ha' hb' xa' ya' xp yp hnab hnba
    obtain ⟨x₀, hx₀, m₁, -, f₁, ac₁⟩ := back a' x' ha'
    obtain ⟨y₀, hy₀, m₂, -, f₂, ac₂⟩ := back b' y' hb'
    rw [release_ancs hx] at hnab hnba; rw [m₁, m₂]
    exact ht a' b' x₀ y₀ p hab hx₀ hy₀ (ac₁ xa').1 (ac₂ ya').1 (f₁ ▸ xp) (f₂ ▸ yp) hnab hnba
  have act : ∀ y, s.Active y → y ≠ a → (releaseEff s a).Active y := fun y ⟨z, hz, za⟩ hya =>
    ⟨z, by rw [get]; simp only [Ne.symm hya, ↓reduceIte]; exact hz, za⟩
  have e := releaseEff_eq hx
  refine ⟨⟨fun b y o hb ho => ?_, tree, fun b y hb l hl => ?_, by rw [e]; exact wn,
    by rw [e]; exact wl, by rw [e]; exact wp⟩,
    i1_of_tree tree, fun b y o hb ho => ?_, fun q hq y hy => ?_, i4_always _⟩
  · obtain ⟨y₀, hy₀, -, e, -⟩ := back b y hb; exact w0 b y₀ o hy₀ (e ▸ ho)
  · obtain ⟨y₀, hy₀, -, -, e', -⟩ := back b y hb; rw [e]; exact w2 b y₀ hy₀ l (e' ▸ hl)
  · obtain ⟨y₀, hy₀, m₀, e, f₀, -⟩ := back b y hb
    obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ o hy₀ (e ▸ ho)
    refine ⟨if a = o then { x with active := false } else x₁, by rw [get]; split <;> simp_all,
      fun p hp => ?_⟩
    have := hh p (f₀ ▸ hp); rw [m₀]
    split
    · subst_vars; rw [hx] at hx₁; cases hx₁; exact this
    · exact this
  · have hy' := hy; rw [e] at hq hy'
    have hq' : q ∈ List.range s.P.length := by
      obtain ⟨f, hf, -⟩ := hq; simp [placeFrame] at hf
      obtain ⟨pl, hpl, -⟩ := hf; exact List.mem_range.2 (lt_of_getElem? hpl)
    exact act y (i3 q hq y hy') fun e => h3 q hq' hq (e ▸ hy')

/-- `release_restores_authority` (MM-03.3 §3, O3 ; §10) : si `b`, dérivée de `a`, est le seul
descendant actif de `a` couvrant `p`, alors après `release b` l'autorité effective de `a` sur `p`
est son mode ; avant, si `b` est en `Modify` sur `p`, elle était absente. -/
theorem release_restores_authority {s s' : S3} {b a p : Nat} {y x : Authority} (hwf : WF3 s)
    (h : ReleaseStep b s (.ok s')) (hy : s.A[b]? = some y) (ho : y.origin = some a)
    (hx : s.A[a]? = some x) (xa : x.active = true) (xp : p ∈ x.footprint)
    (honly : ∀ j z, s.A[j]? = some z → z.active = true → p ∈ z.footprint → a ∈ s.ancs j → j = b) :
    (y.mode = .modify → p ∈ y.footprint → effective s a p = none) ∧
    effective s' a p = some x.mode := by
  obtain ⟨⟨⟨y', hy', ya⟩, -, -⟩, rfl⟩ := release_ok_iff.1 h
  rw [hy] at hy'; cases hy'
  have hab : a < b := hwf.1 b y a hy ho
  have hanc : a ∈ s.ancs b := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hab]; exact List.mem_cons_self ..
  refine ⟨fun hm hp => ?_, ?_⟩
  · rw [effective_eq hx xa xp]
    have : Mode.modify ∈ descModes s a p := mem_descModes.2 ⟨b, y, hy, ya, hp, hanc, hm⟩
    unfold effOf; simp only [List.ne_nil_of_mem this, this, ↓reduceIte]
  · have hb := lt_of_getElem? hy
    have hx' : (releaseEff s b).A[a]? = some x := by
      rw [releaseEff_eq hy, set_get hb]; simp only [show ¬ b = a by omega, ↓reduceIte]; exact hx
    rw [effective_eq hx' xa xp]
    have : descModes (releaseEff s b) a p = [] := by
      apply nil_of_forall_not_mem; intro e he
      obtain ⟨j, z, hz, za, zp, hj, -⟩ := mem_descModes.1 he
      rw [release_ancs hy] at hj
      rw [releaseEff_eq hy, set_get hb] at hz
      split at hz
      · cases hz; simp at za
      · exact ‹¬b = j› (honly j z hz za zp hj).symm
    simp [this, effOf]

/-- `transfer` ne change que le cadre détenteur des autorités. -/
theorem transfer_skel (s : S3) (src dst : Nat) (auths : List Nat) :
    SameSkel s (transferEff s src dst auths) := by
  refine ⟨by simp [transferEff, length_mapI], fun j => ?_⟩
  simp only [transferEff, getElem?_mapI, Option.map_map]
  cases s.A[j]? with
  | none => rfl
  | some y => simp only [Option.map_some, Function.comp]; split <;> rfl

/-- `transfer` préserve `WF3` et `Inv3` (MM-03.3 §3, O4 ; §10). -/
theorem transfer_preserves {k : K} {s s' : S3} {src dst : Nat} {auths : List Nat} (hwf : WF3 s)
    (hinv : Inv3 s) (h : TransferStep k src dst auths s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨-, -, -, -, -, -, -, h5, -, -⟩, rfl⟩ := transfer_ok_iff.1 h
  refine (transfer_skel s src dst auths).preserves rfl rfl rfl hwf hinv fun q hq x hx => ?_
  simp only [transferEff] at hx
  split at hx
  · rename_i hqd; subst hqd; rcases List.mem_append.1 hx with hx | hx
    · exact hinv.2.2.1 _ hq x hx
    · exact h5 x hx
  · split at hx
    · simp at hx
    · exact hinv.2.2.1 q hq x hx

/-- `transfer` préserve `Inv3`, sans `WF3` (MM-03.3 §3, O4). -/
theorem transfer_preserves_inv3 {k : K} {s s' : S3} {src dst : Nat} {auths : List Nat}
    (hinv : Inv3 s) (h : TransferStep k src dst auths s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨-, -, -, -, -, -, -, h5, -, -⟩, rfl⟩ := transfer_ok_iff.1 h
  refine (transfer_skel s src dst auths).inv3 rfl rfl hinv fun q hq x hx => ?_
  simp only [transferEff] at hx
  split at hx
  · rename_i hqd; subst hqd; rcases List.mem_append.1 hx with hx | hx
    · exact hinv.2.2.1 _ hq x hx
    · exact h5 x hx
  · split at hx
    · simp at hx
    · exact hinv.2.2.1 q hq x hx

/-- `transfer_no_duplicate_authority` (MM-03.3 §3, O4.3 ; §2, I4 ; §10) : aucune autorité n'est
créée ni dupliquée ; chaque autorité garde mode, origine, empreinte et activité ; les autorités
transférées passent au cadre de la destination. -/
theorem transfer_no_duplicate_authority {k : K} {s s' : S3} {src dst : Nat} {auths : List Nat}
    (h : TransferStep k src dst auths s (.ok s')) :
    SameSkel s s' ∧ ∀ b ∈ auths, s'.frameOf b = some ((placeFrame s.P dst).getD 0) := by
  obtain ⟨⟨-, -, -, -, -, hauth, -⟩, rfl⟩ := transfer_ok_iff.1 h
  refine ⟨transfer_skel s src dst auths, fun b hb => ?_⟩
  obtain ⟨⟨y, hy, -⟩, -, -⟩ := hauth b hb
  simp [S3.frameOf, transferEff, getElem?_mapI, hy, hb]

/-- `transfer_invalidates_source` (MM-03.3 §3, O4 ; §2, I4) : après un transfert, chaque feuille
de la source est `Moved` et n'est lisible par aucune autorité. -/
theorem transfer_invalidates_source {k : K} {s s' : S3} {src dst : Nat} {auths : List Nat}
    (h : TransferStep k src dst auths s (.ok s')) :
    ∀ l ∈ footprint s.P src, s'.I l = .moved ∧ ∀ a, ¬ CanReadLeaf s' a l := by
  obtain ⟨⟨-, -, -, -, hov, -⟩, rfl⟩ := transfer_ok_iff.1 h
  intro l hl
  have hm : (transferEff s src dst auths).I l = .moved := by
    simp only [transferEff, show l ∉ footprint s.P dst from fun h' => hov ⟨l, hl, h'⟩, hl,
      ↓reduceIte]
  exact ⟨hm, fun a => i4_always _ a l hm⟩

/-- Dépendances transférées (MM-03.3.6 ; MM-03.3 §3, O4) : celles de la source accompagnent la
destination et quittent la source et ses parties. -/
theorem transfer_moves_deps {k : K} {s s' : S3} {src dst : Nat} {auths : List Nat}
    (h : TransferStep k src dst auths s (.ok s')) :
    (∀ x ∈ depsOf s src, x ∈ s'.D dst) ∧ ∀ r, r ≠ dst → partOf s.P r src → s'.D r = [] := by
  obtain ⟨-, rfl⟩ := transfer_ok_iff.1 h
  exact ⟨fun x hx => by simp [transferEff, hx], fun r hr hp => by simp [transferEff, hr, hp]⟩

/-- `depend` préserve `WF3` et `Inv3` (MM-03.3 §3, O5 ; §10). -/
theorem depend_preserves {s s' : S3} {q x : Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : DependStep q x s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨⟨-, hx, -⟩, rfl⟩ := depend_ok_iff.1 h
  refine (show SameSkel s (dependEff s q x) from ⟨rfl, fun _ => rfl⟩).preserves rfl rfl rfl
    hwf hinv fun r hr y hy => ?_
  simp only [dependEff] at hy
  split at hy
  · subst_vars; rcases List.mem_append.1 hy with hy | hy
    · exact hinv.2.2.1 _ hr y hy
    · simp at hy; exact hy ▸ hx
  · exact hinv.2.2.1 r hr y hy

/-- `depend` préserve `Inv3`, sans `WF3` (MM-03.3 §3, O5). -/
theorem depend_preserves_inv3 {s s' : S3} {q x : Nat} (hinv : Inv3 s)
    (h : DependStep q x s (.ok s')) : Inv3 s' := by
  obtain ⟨⟨-, hx, -⟩, rfl⟩ := depend_ok_iff.1 h
  refine (show SameSkel s (dependEff s q x) from ⟨rfl, fun _ => rfl⟩).inv3 rfl rfl hinv
    fun r hr y hy => ?_
  simp only [dependEff] at hy
  split at hy
  · subst_vars; rcases List.mem_append.1 hy with hy | hy
    · exact hinv.2.2.1 _ hr y hy
    · simp at hy; exact hy ▸ hx
  · exact hinv.2.2.1 r hr y hy

/-- `depend_preserves_anchor_validity` (MM-03.3 §3, O5 ; §2, I3 ; §10) : I3 est préservé et la
validité de toute ancre est inchangée, `depend` n'allongeant celle d'aucune origine. -/
theorem depend_preserves_anchor_validity {s s' : S3} {q x : Nat} (hi3 : I3 s)
    (h : DependStep q x s (.ok s')) : I3 s' ∧ ∀ y, s'.Active y ↔ s.Active y := by
  obtain ⟨⟨-, hx, -⟩, rfl⟩ := depend_ok_iff.1 h
  refine ⟨fun r hr y hy => ?_, fun _ => Iff.rfl⟩
  simp only [dependEff] at hy
  split at hy
  · subst_vars; rcases List.mem_append.1 hy with hy | hy
    · exact hi3 _ hr y hy
    · simp at hy; exact hy ▸ hx
  · exact hi3 r hr y hy

/-- `read3` préserve l'état (MM-03.3 §5 : la lecture ne modifie pas l'état des autorités). -/
theorem read3_preserves {s s' : S3} {a : Nat} {ls : List Nat} (h : Read3Step a ls s (.ok s')) :
    s' = s := (read3_ok_iff.1 h).2

/-- `write3` préserve `Inv3`, sans `WF3` (MM-03.3 §5). -/
theorem write3_preserves_inv3 {s s' : S3} {a : Nat} {ls : List Nat} (hinv : Inv3 s)
    (h : Write3Step a ls s (.ok s')) : Inv3 s' := by
  obtain ⟨-, rfl⟩ := write3_ok_iff.1 h
  exact (show SameSkel s (write3Eff s ls) from ⟨rfl, fun _ => rfl⟩).inv3 rfl rfl hinv
    fun q hq y hy => hinv.2.2.1 q hq y hy

/-- `write3` préserve `WF3` et `Inv3` (MM-03.3 §5 ; §10). -/
theorem write3_preserves {s s' : S3} {a : Nat} {ls : List Nat} (hwf : WF3 s) (hinv : Inv3 s)
    (h : Write3Step a ls s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨-, rfl⟩ := write3_ok_iff.1 h
  exact (show SameSkel s (write3Eff s ls) from ⟨rfl, fun _ => rfl⟩).preserves rfl rfl rfl
    hwf hinv fun q hq y hy => hinv.2.2.1 q hq y hy

/-! ## `enterFrame` -/

theorem mem_footprint {P : List Place} {q l : Nat} :
    l ∈ footprint P q ↔ l < P.length ∧ isLeaf P l ∧ partOf P l q := by
  simp [footprint, List.mem_filter, List.mem_range]

theorem enter_get {s : S3} {ls : List (Option Nat × Nat)} {j : Nat} {z : Authority}
    (h : (enterEff s ls).A[j]? = some z) :
    (j < s.A.length ∧ s.A[j]? = some z) ∨
    (s.A.length ≤ j ∧ ∃ i, (rootIdx ls)[j - s.A.length]? = some i ∧
      z = ⟨.modify, none, footprint (enterP s ls) (s.P.length + i), s.nF, true⟩) := by
  simp only [enterEff] at h
  by_cases hj : j < s.A.length
  · exact .inl ⟨hj, by rwa [List.getElem?_append_left hj] at h⟩
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at h
    cases hi : (rootIdx ls)[j - s.A.length]? with
    | none => rw [hi] at h; cases h
    | some i => rw [hi] at h; cases h; exact .inr ⟨by omega, i, rfl, rfl⟩

theorem enter_lt {s : S3} {ls : List (Option Nat × Nat)} {j : Nat} (h : j < s.A.length) :
    (enterEff s ls).A[j]? = s.A[j]? := List.getElem?_append_left h

theorem enter_ancs_lt {s : S3} {ls : List (Option Nat × Nat)} {j : Nat} (h : j < s.A.length) :
    (enterEff s ls).ancs j = s.ancs j :=
  chain_congr fun i hi => by simp only [S3.org, enter_lt (Nat.lt_of_le_of_lt hi h)]

theorem rootIdx_mem {ls : List (Option Nat × Nat)} {k i : Nat} (h : (rootIdx ls)[k]? = some i) :
    i < ls.length ∧ (ls[i]?).bind (·.1) = none := by
  have := List.mem_of_getElem? h
  simp only [rootIdx, List.mem_filter, List.mem_range, Option.isNone_iff_eq_none] at this
  exact this

theorem enter_root_parent {s : S3} {ls : List (Option Nat × Nat)} {i : Nat}
    (h : (ls[i]?).bind (·.1) = none) : parentOf (enterP s ls) (s.P.length + i) = none := by
  simp only [parentOf, enterP, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map]
  cases hl : ls[i]? with
  | none => rfl
  | some pk => rw [hl] at h; simpa using h

theorem enter_root_fp_ge {s : S3} {ls : List (Option Nat × Nat)} {i l : Nat}
    (h : l ∈ footprint (enterP s ls) (s.P.length + i)) : s.P.length ≤ l := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h
  · omega
  · have := chain_lt h; omega

theorem enter_roots_disjoint {s : S3} {ls : List (Option Nat × Nat)} {i i' l : Nat} (hii : i ≠ i')
    (hi : (ls[i]?).bind (·.1) = none) (hi' : (ls[i']?).bind (·.1) = none)
    (h : l ∈ footprint (enterP s ls) (s.P.length + i))
    (h' : l ∈ footprint (enterP s ls) (s.P.length + i')) : False := by
  obtain ⟨-, -, -, h | h⟩ := mem_footprint.1 h <;> obtain ⟨-, -, -, h' | h'⟩ := mem_footprint.1 h'
  · omega
  · subst h; rw [chain_none (enter_root_parent hi)] at h'; simp at h'
  · subst h'; rw [chain_none (enter_root_parent hi')] at h; simp at h
  · exact hii (by have := chainF_root _ _ _ _ h (enter_root_parent hi) h' (enter_root_parent hi')
                  omega)

/-- `enterFrame` préserve `WF3` et `Inv3` (MM-03.3 §4, O6 ; §10). -/
theorem enter_preserves {s s' : S3} {ls : List (Option Nat × Nat)} (hwf : WF3 s) (hinv : Inv3 s)
    (h : EnterStep ls s (.ok s')) : WF3 s' ∧ Inv3 s' := by
  obtain ⟨-, rfl⟩ := enter_ok_iff.1 h
  obtain ⟨w0, ht, w2, wn, wl, wp⟩ := hwf
  obtain ⟨-, i2, i3, -⟩ := hinv
  have nodup : (rootIdx ls).Nodup :=
    ((pairwise_lt_range _).sublist List.filter_sublist).imp Nat.ne_of_lt
  have tree : Tree (enterEff s ls) := by
    intro a b x y p hab ha hb xa ya xp yp hnab hnba
    rcases enter_get ha with ⟨ha', ha''⟩ | ⟨ha', i, hi, rfl⟩ <;>
      rcases enter_get hb with ⟨hb', hb''⟩ | ⟨hb', i', hi', rfl⟩
    · rw [enter_ancs_lt hb'] at hnab; rw [enter_ancs_lt ha'] at hnba
      exact ht a b x y p hab ha'' hb'' xa ya xp yp hnab hnba
    · have := w2 a x ha'' p xp; have := enter_root_fp_ge yp; omega
    · have := w2 b y hb'' p yp; have := enter_root_fp_ge xp; omega
    · have hk : a - s.A.length ≠ b - s.A.length := by omega
      have hii : i ≠ i' := fun e => hk ((nodup.getElem?_inj (lt_of_getElem? hi)).1 (by
        rw [hi, hi', e]))
      exact (enter_roots_disjoint hii (rootIdx_mem hi).2 (rootIdx_mem hi').2 xp yp).elim
  have act : ∀ x, s.Active x → (enterEff s ls).Active x := fun x ⟨y, hy, ya⟩ =>
    ⟨y, by rw [enter_lt (lt_of_getElem? hy)]; exact hy, ya⟩
  have hP : ∀ q pl, (enterEff s ls).P[q]? = some pl →
      (q < s.P.length ∧ s.P[q]? = some pl) ∨ (s.P.length ≤ q ∧ pl.frame = s.nF) := by
    intro q pl hq
    simp only [enterEff, enterP] at hq
    by_cases hlt : q < s.P.length
    · exact .inl ⟨hlt, by rwa [List.getElem?_append_left hlt] at hq⟩
    · rw [List.getElem?_append_right (by omega), List.getElem?_map] at hq
      cases hl : ls[q - s.P.length]? with
      | none => rw [hl] at hq; cases hq
      | some pk => rw [hl] at hq; cases hq; exact .inr ⟨by omega, rfl⟩
  refine ⟨⟨fun b y a hb ho => ?_, tree, fun a x hx l hl => ?_, ?_, ?_, ?_⟩, i1_of_tree tree,
    fun b y a hb ho => ?_, fun q hq x hx => ?_, i4_always _⟩
  · rcases enter_get hb with ⟨-, hb''⟩ | ⟨-, _, -, hz⟩
    · exact w0 b y a hb'' ho
    · rw [hz] at ho; cases ho
  · have hlen : (enterEff s ls).P.length = s.P.length + ls.length := by
      simp [enterEff, enterP]
    rw [hlen]
    rcases enter_get hx with ⟨-, hx''⟩ | ⟨-, i, -, rfl⟩
    · have := w2 a x hx'' l hl; omega
    · have := (mem_footprint.1 hl).1; simpa [enterP] using this
  · exact List.nodup_cons.2 ⟨fun hm => Nat.lt_irrefl _ (wl _ hm), wn⟩
  · intro f hf; rcases List.mem_cons.1 hf with rfl | hf
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (wl f hf)
  · intro q pl hq; rcases hP q pl hq with ⟨-, hq'⟩ | ⟨-, e⟩
    · exact Nat.lt_succ_of_lt (wp q pl hq')
    · rw [e]; exact Nat.lt_succ_self _
  · rcases enter_get hb with ⟨-, hb''⟩ | ⟨-, _, -, hz⟩
    · obtain ⟨x₁, hx₁, hh⟩ := i2 b y a hb'' ho
      exact ⟨x₁, by rw [enter_lt (lt_of_getElem? hx₁)]; exact hx₁, hh⟩
    · rw [hz] at ho; cases ho
  · obtain ⟨g, hg, hgF⟩ := hq
    simp only [placeFrame, Option.map_eq_some_iff] at hg
    obtain ⟨pl, hpl, rfl⟩ := hg
    rcases hP q pl hpl with ⟨hlt, hpl'⟩ | ⟨hge, -⟩
    · have hne : pl.frame ≠ s.nF := Nat.ne_of_lt (wp q pl hpl')
      have hF : pl.frame ∈ s.F := by
        rcases List.mem_cons.1 hgF with e | e
        · exact absurd e hne
        · exact e
      have hx' : x ∈ s.D q := by simpa [enterEff, show ¬ s.P.length ≤ q by omega] using hx
      exact act x (i3 q ⟨pl.frame, by simp [placeFrame, hpl'], hF⟩ x hx')
    · simp [enterEff, hge] at hx

/-! ## `exitFrame` -/

/-- Retirer d'une chaîne des liens dont la cible vérifie `Fr` en les remplaçant par l'origine de
celle-ci ne fait qu'ôter à chaque chaîne des éléments vérifiant `Fr`. -/
theorem chain_reattach {org org' : Nat → Option Nat} {Fr : Nat → Prop}
    (w : ∀ b a, org b = some a → a < b)
    (hre : ∀ b, org' b = org b ∨ ∃ x, org b = some x ∧ Fr x ∧ org' b = org x) :
    ∀ n i, i < n → (∀ j ∈ chain org' i, j ∈ chain org i) ∧
      (∀ j ∈ chain org i, ¬ Fr j → j ∈ chain org' i)
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, i, hi => by
    rcases hre i with e | ⟨x, hx, fx, e⟩
    · cases ho : org i with
      | none =>
        rw [chain_none ho, chain_none (e.trans ho)]
        exact ⟨fun _ hj => (nomatch hj), fun _ hj => (nomatch hj)⟩
      | some o =>
        have hlt := w i o ho
        have ih := chain_reattach w hre n o (by omega)
        rw [chain_cons ho hlt, chain_cons (e.trans ho) hlt]
        refine ⟨fun j hj => ?_, fun j hj hf => ?_⟩
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih.1 j hj)
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih.2 j hj hf)
    · have hxi := w i x hx
      rw [chain_cons hx hxi]
      cases ho : org x with
      | none =>
        rw [chain_none (e.trans ho), chain_none ho]
        refine ⟨fun j hj => by simp at hj, fun j hj hf => ?_⟩
        simp at hj; exact absurd (hj ▸ fx) hf
      | some o =>
        have hlt := w x o ho
        have ih := chain_reattach w hre n o (by omega)
        rw [chain_cons ho hlt, chain_cons (e.trans ho) (by omega)]
        refine ⟨fun j hj => ?_, fun j hj hf => ?_⟩
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
          · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (ih.1 j hj))
        · rcases List.mem_cons.1 hj with rfl | hj
          · exact absurd fx hf
          · rcases List.mem_cons.1 hj with rfl | hj
            · exact List.mem_cons_self ..
            · exact List.mem_cons_of_mem _ (ih.2 j hj hf)

theorem exitEff_eq {s : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀) :
    exitEff s =
      { s with
        F := F₀
        D := fun q => (s.D q).map (reanchor s f)
        A := s.A.map (exitG s f) } := by
  simp [exitEff, hF]

theorem exitG_fields (s : S3) (f : Nat) (y : Authority) :
    (exitG s f y).mode = y.mode ∧ (exitG s f y).footprint = y.footprint ∧
    (exitG s f y).frame = y.frame ∧
    ((exitG s f y).active = true ↔ y.active = true ∧ y.frame ≠ f) := by
  unfold exitG; split
  · simp_all
  · split <;> simp_all

theorem exitG_origin (s : S3) (f : Nat) (y : Authority) :
    (exitG s f y).origin = y.origin ∨
    ∃ x, y.origin = some x ∧ s.frameOf x = some f ∧ (exitG s f y).origin = s.org x := by
  unfold exitG; split
  · exact .inl rfl
  · split
    · rename_i h; right
      cases ho : y.origin with
      | none => simp [ho] at h
      | some x => simp [ho] at h; exact ⟨x, rfl, h.2, by simp⟩
    · exact .inl rfl

/-- `exitFrame` préserve `WF3` et `Inv3` (MM-03.3 §4, O7 ; §10 ; arbitrage 1). -/
theorem exit_preserves {s s' : S3} (hwf : WF3 s) (hinv : Inv3 s) (h : ExitStep s (.ok s')) :
    WF3 s' ∧ Inv3 s' := by
  obtain ⟨hpre, rfl⟩ := exit_ok_iff.1 h
  unfold ExitPre at hpre
  split at hpre
  · rename_i f F₀ hF
    obtain ⟨-, hR1, -⟩ := hpre
    obtain ⟨w0, ht, w2, wn, wl, wp⟩ := hwf
    obtain ⟨-, i2, i3, -⟩ := hinv
    have e := exitEff_eq hF
    have get : ∀ j, (exitEff s).A[j]? = (s.A[j]?).map (exitG s f) := fun j => by
      rw [e]; exact List.getElem?_map
    have get' : ∀ {j z}, (exitEff s).A[j]? = some z → ∃ z₀, s.A[j]? = some z₀ ∧ z = exitG s f z₀ :=
      fun {j z} hz => by
        rw [get] at hz
        cases h₀ : s.A[j]? with
        | none => rw [h₀] at hz; cases hz
        | some z₀ => rw [h₀] at hz; cases hz; exact ⟨z₀, h₀, rfl⟩
    have worg : ∀ b a, s.org b = some a → a < b := fun b a h => by
      simp only [S3.org] at h
      cases hb : s.A[b]? with
      | none => rw [hb] at h; cases h
      | some y => rw [hb] at h; exact w0 b y a hb h
    have hre : ∀ b, (exitEff s).org b = s.org b ∨
        ∃ x, s.org b = some x ∧ s.frameOf x = some f ∧ (exitEff s).org b = s.org x := fun b => by
      simp only [S3.org, get]
      cases hb : s.A[b]? with
      | none => exact .inl rfl
      | some y =>
        rcases exitG_origin s f y with e' | ⟨x, hx, fx, e'⟩
        · exact .inl (by simp [e'])
        · exact .inr ⟨x, by simp [hx], fx, by simp [e', S3.org]⟩
    have cr := fun i => chain_reattach worg hre (i + 1) i (Nat.lt_succ_self i)
    have tree : Tree (exitEff s) := by
      intro a b x y p hab ha hb xa ya xp yp hnab hnba
      obtain ⟨x₀, hx₀, rfl⟩ := get' ha; obtain ⟨y₀, hy₀, rfl⟩ := get' hb
      obtain ⟨xm, xf, -, xact⟩ := exitG_fields s f x₀
      obtain ⟨ym, yf, -, yact⟩ := exitG_fields s f y₀
      have ⟨xa₀, xnf⟩ := xact.1 xa; have ⟨ya₀, ynf⟩ := yact.1 ya
      rw [xm, ym]
      refine ht a b x₀ y₀ p hab hx₀ hy₀ xa₀ ya₀ (xf ▸ xp) (yf ▸ yp) (fun hm => hnab ?_)
        (fun hm => hnba ?_)
      · exact (cr b).2 a hm (by simp [S3.frameOf, hx₀, xnf])
      · exact (cr a).2 b hm (by simp [S3.frameOf, hy₀, ynf])
    have hnd := List.nodup_cons.1 (hF ▸ wn)
    refine ⟨⟨fun b y a hb ho => ?_, tree, fun a x hx l hl => ?_, by rw [e]; exact hnd.2,
      fun g hg => by rw [e] at hg ⊢; exact wl g (hF ▸ List.mem_cons_of_mem _ hg),
      by rw [e]; exact wp⟩, i1_of_tree tree, fun b y a hb ho => ?_, fun q hq x hx => ?_,
      i4_always _⟩
    · have : (exitEff s).org b = some a := by simp [S3.org, hb, ho]
      rcases hre b with e' | ⟨x, hx, -, e'⟩
      · exact worg b a (e' ▸ this)
      · have := worg x a (e' ▸ this); have := worg b x hx; omega
    · obtain ⟨x₀, hx₀, rfl⟩ := get' hx
      rw [e]; exact w2 a x₀ hx₀ l ((exitG_fields s f x₀).2.1 ▸ hl)
    · obtain ⟨y₀, hy₀, rfl⟩ := get' hb
      obtain ⟨ym, yf, -, -⟩ := exitG_fields s f y₀
      have lift : ∀ {a x₁}, s.A[a]? = some x₁ → (exitEff s).A[a]? = some (exitG s f x₁) :=
        fun h => by rw [get, h]; rfl
      rcases exitG_origin s f y₀ with e' | ⟨x, hx, -, e'⟩
      · obtain ⟨x₁, hx₁, hh⟩ := i2 b y₀ a hy₀ (e' ▸ ho)
        obtain ⟨xm, xf, -, -⟩ := exitG_fields s f x₁
        exact ⟨_, lift hx₁, fun p hp => by rw [ym, xm, xf]; exact hh p (yf ▸ hp)⟩
      · obtain ⟨x₁, hx₁, hh₁⟩ := i2 b y₀ x hy₀ hx
        have hox : x₁.origin = some a := by
          have := e'.symm.trans ho; simpa [S3.org, hx₁] using this
        obtain ⟨x₂, hx₂, hh₂⟩ := i2 x x₁ a hx₁ hox
        obtain ⟨xm, xf, -, -⟩ := exitG_fields s f x₂
        refine ⟨_, lift hx₂, fun p hp => ?_⟩
        rw [ym, xm, xf]
        obtain ⟨p₁, m₁⟩ := hh₁ p (yf ▸ hp); obtain ⟨p₂, m₂⟩ := hh₂ p p₁
        exact ⟨p₂, Mode.le_trans m₁ m₂⟩
    · have hq0 : s.Usable q := by
        obtain ⟨g, hg, hgF⟩ := hq; rw [e] at hg hgF
        exact ⟨g, hg, hF ▸ List.mem_cons_of_mem _ hgF⟩
      have hqin : UsableIn s F₀ q := by
        obtain ⟨g, hg, hgF⟩ := hq; rw [e] at hg hgF; simp [UsableIn, OptP, hg, hgF]
      rw [e] at hx; simp only [List.mem_map] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      have hq' : q ∈ List.range s.P.length := by
        obtain ⟨g, hg, -⟩ := hq0; simp [placeFrame] at hg
        obtain ⟨pl, hpl, -⟩ := hg; exact List.mem_range.2 (lt_of_getElem? hpl)
      have keep : ∀ z, s.Active z → s.frameOf z ≠ some f → (exitEff s).Active z :=
        fun z ⟨y, hy, ya⟩ hzf => ⟨exitG s f y, by rw [get, hy]; rfl,
          (exitG_fields s f y).2.2.2.2 ⟨ya, fun hf => hzf (by simp [S3.frameOf, hy, hf])⟩⟩
      unfold reanchor; split
      · rename_i hfx
        have hR := hR1 q hq' hqin x₀ hx₀ hfx
        unfold Reanch OptP at hR; split at hR
        · rename_i o ho
          obtain ⟨hoa, hof⟩ := hR
          simp only [ho, Option.getD_some]
          refine keep o hoa fun hf => ?_
          rw [hf] at hof; exact hnd.1 hof
        · exact hR.elim
      · rename_i hfx; exact keep x₀ (i3 q hq0 x₀ hx₀) hfx
  · exact hpre.elim

/-- `exitFrame_releases_all` (MM-03.3 §4, O7 ; §10) : après la sortie du cadre `f`, aucune
autorité détenue par `f` n'est active. -/
theorem exitFrame_releases_all {s s' : S3} {f : Nat} {F₀ : Frames} (hF : s.F = f :: F₀)
    (h : ExitStep s (.ok s')) :
    ∀ (j : Nat) (y : Authority), s'.A[j]? = some y → y.frame = f → y.active = false := by
  intro j y hy hf
  rw [(exit_ok_iff.1 h).2, exitEff_eq hF, List.getElem?_map] at hy
  cases h₀ : s.A[j]? with
  | none => rw [h₀] at hy; cases hy
  | some y₀ =>
    rw [h₀] at hy; cases hy
    obtain ⟨-, -, fr, act⟩ := exitG_fields s f y₀
    cases ha : (exitG s f y₀).active
    · rfl
    · exact absurd (fr ▸ hf) (act.1 ha).2

/-- `exitFrame_reanchors_to_origin` (MM-03.3.7 ; MM-03.3 §4, O7 ; arbitrage 1) : toute ancre
détenue par le cadre sortant d'une valeur d'un cadre survivant est remplacée par son origine,
qui est une ancre valide après le retour. -/
theorem exitFrame_reanchors_to_origin {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hinv : Inv3 s) (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    ∀ q, UsableIn s F₀ q → ∀ x ∈ s.D q, s.frameOf x = some f →
      ∃ o, s.org x = some o ∧ o ∈ s'.D q ∧ s'.Active o := by
  have hpres := exit_preserves hwf hinv h
  obtain ⟨hpre, rfl⟩ := exit_ok_iff.1 h
  unfold ExitPre at hpre; rw [hF] at hpre
  obtain ⟨-, hR1, -⟩ := hpre
  intro q hq x hx hfx
  have hq' : q ∈ List.range s.P.length := by
    simp only [UsableIn, OptP] at hq; split at hq
    · rename_i g hg; simp [placeFrame] at hg
      obtain ⟨pl, hpl, -⟩ := hg; exact List.mem_range.2 (lt_of_getElem? hpl)
    · exact hq.elim
  have hR := hR1 q hq' hq x hx hfx
  unfold Reanch OptP at hR; split at hR
  · rename_i o ho
    have hmem : o ∈ (exitEff s).D q := by
      rw [exitEff_eq hF]; exact List.mem_map.2 ⟨x, hx, by simp [reanchor, hfx, ho]⟩
    refine ⟨o, ho, hmem, hpres.2.2.2.1 q ?_ o hmem⟩
    simp only [UsableIn, OptP] at hq; split at hq
    · rename_i g hg; exact ⟨g, by rw [exitEff_eq hF]; exact hg, by rw [exitEff_eq hF]; exact hq⟩
    · exact hq.elim
  · exact hR.elim

/-- `dependent_cannot_escape_frame` (MM-03.3.6 ; MM-03.3 §4, O7.3 ; §10) : après la sortie du
cadre `f`, aucune valeur encore utilisable ne dépend d'une autorité détenue par `f`. -/
theorem dependent_cannot_escape_frame {s s' : S3} {f : Nat} {F₀ : Frames} (hwf : WF3 s)
    (hinv : Inv3 s) (hF : s.F = f :: F₀) (h : ExitStep s (.ok s')) :
    ∀ q, s'.Usable q → ∀ x ∈ s'.D q, ∃ y, s'.A[x]? = some y ∧ y.active = true ∧ y.frame ≠ f := by
  intro q hq x hx
  obtain ⟨y, hy, ya⟩ := (exit_preserves hwf hinv h).2.2.2.1 q hq x hx
  exact ⟨y, hy, ya, fun hf => by rw [exitFrame_releases_all hF h x y hy hf] at ya; cases ya⟩

/-! ## Atteignabilité (MM-03.3 §10) -/

/-- États atteints depuis l'état initial (un cadre, aucun emplacement) par des transitions
`ok` des opérations du noyau, pour des contrats `k` fixés (arbitrage 5). -/
inductive Reachable (k : K) : S3 → Prop where
  | init : Reachable k S3.init
  | derive {s s' : S3} {src q : Nat} {m : Mode} :
      Reachable k s → DeriveStep src q m s (.ok s') → Reachable k s'
  | split {s s' : S3} {src : Nat} {rs : List (List Nat)} :
      Reachable k s → SplitStep k src rs s (.ok s') → Reachable k s'
  | release {s s' : S3} {a : Nat} : Reachable k s → ReleaseStep a s (.ok s') → Reachable k s'
  | transfer {s s' : S3} {src dst : Nat} {auths : List Nat} :
      Reachable k s → TransferStep k src dst auths s (.ok s') → Reachable k s'
  | depend {s s' : S3} {q x : Nat} : Reachable k s → DependStep q x s (.ok s') → Reachable k s'
  | enter {s s' : S3} {ls : List (Option Nat × Nat)} :
      Reachable k s → EnterStep ls s (.ok s') → Reachable k s'
  | exit {s s' : S3} : Reachable k s → ExitStep s (.ok s') → Reachable k s'
  | read {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k s → Read3Step a ls s (.ok s') → Reachable k s'
  | write {s s' : S3} {a : Nat} {ls : List Nat} :
      Reachable k s → Write3Step a ls s (.ok s') → Reachable k s'

theorem init_wf : WF3 S3.init ∧ Inv3 S3.init := by
  have tree : Tree S3.init := fun _ _ _ _ _ _ h => by simp [S3.init] at h
  refine ⟨⟨fun _ _ _ h => by simp [S3.init] at h, tree, fun _ _ h => by simp [S3.init] at h,
    by simp [S3.init], by simp [S3.init], fun _ _ h => by simp [S3.init] at h⟩,
    i1_of_tree tree, fun _ _ _ h => by simp [S3.init] at h, fun _ _ _ h => by simp [S3.init] at h,
    i4_always _⟩

/-- `reachable_access_invariant` (MM-03.3 §10) : tout état atteint satisfait `WF3` et `Inv3`.
Conditionné à l'obligation `DDSound k` de `DeclaredDisjoint` (MM-03.3.8), utilisée par
`split`. -/
theorem reachable_access_invariant_underDD {k : K} (hdd : DDSound k) {s : S3}
    (h : Reachable k s) : WF3 s ∧ Inv3 s := by
  induction h with
  | init => exact init_wf
  | derive _ hs ih => exact derive_preserves ih.1 ih.2 hs
  | split _ hs ih => exact split_preserves_underDD hdd ih.1 ih.2 hs
  | release _ hs ih => exact release_preserves ih.1 ih.2 hs
  | transfer _ hs ih => exact transfer_preserves ih.1 ih.2 hs
  | depend _ hs ih => exact depend_preserves ih.1 ih.2 hs
  | enter _ hs ih => exact enter_preserves ih.1 ih.2 hs
  | exit _ hs ih => exact exit_preserves ih.1 ih.2 hs
  | read _ hs ih => rw [read3_preserves hs]; exact ih
  | write _ hs ih => exact write3_preserves ih.1 ih.2 hs

/-! ## Arène : instance du modèle (MM-03.3 §6, arbitrage 3)

L'empreinte de la valeur `arena` couvre ses seules métadonnées ; son autorité racine est
`anchor`. Le stockage administré est sous une autorité racine séparée `internal`. `issue` dérive
les blocs de `internal` et ancre la valeur qui reçoit le bloc sur l'autorité par laquelle
l'arène est atteinte. `reset` est gouverné par I3 (via `Invalidates`), jamais par I1. -/

/-- État logique de l'arène (MM-03.3 §6 : `Arena { anchor, storage, available, issued,
internal_authority }`) : `issued` associe chaque région émise à l'autorité émise. -/
structure Arena where
  anchor : Nat
  storage : List Nat
  available : List Nat
  issued : List (List Nat × Nat)
  internal : Nat

/-- Invariant de l'arène (MM-03.3 §6). Clause 0, ajoutée : l'espace disponible fait partie du
stockage administré. Clauses 1 à 3 de MM-03.3 §6 : régions émises incluses dans le stockage
administré ; deux régions émises simultanément valides (autorités actives) disjointes ;
régions disponibles disjointes des régions encore distribuées. La clause 4 (accès distribués
dépendants de l'ancre de l'arène) n'est pas représentée : l'état ne relie pas une autorité à la
valeur qui la contient. La clause suivante, propre à l'abstraction, relie chaque émission à son
autorité dérivée de `internal`. Les dernières clauses traduisent l'arbitrage 3 : `internal` est
une autorité racine distincte de l'ancre, le stockage administré est sous `internal`, et
l'empreinte de la valeur `arena` (celle de l'ancre) ne contient pas ce stockage. -/
def ArenaInv (s : S3) (ar : Arena) : Prop :=
  (∀ l ∈ ar.available, l ∈ ar.storage) ∧
  (∀ e ∈ ar.issued, ∀ l ∈ e.1, l ∈ ar.storage) ∧
  ar.issued.Pairwise (fun e e' => s.Active e.2 → s.Active e'.2 → ∀ l ∈ e.1, l ∉ e'.1) ∧
  (∀ e ∈ ar.issued, s.Active e.2 → ∀ l ∈ e.1, l ∉ ar.available) ∧
  (∀ e ∈ ar.issued, ∃ y, s.A[e.2]? = some y ∧ y.origin = some ar.internal ∧
    y.footprint = e.1 ∧ y.mode = .modify) ∧
  s.org ar.internal = none ∧ ar.internal ≠ ar.anchor ∧
  (∀ l ∈ ar.storage, l ∈ s.afp ar.internal) ∧ (∀ l ∈ ar.storage, l ∉ s.afp ar.anchor)

/-- Préconditions de `arena.issue(region)` (MM-03.3 §6), dans l'ordre : la région est disponible ;
elle est disjointe des régions émises encore actives ; l'abstraction dispose, par `internal`, de
l'autorité effective de modification sur la région ; l'autorité `via` atteint l'arène (`anchor`
ou une dérivée) et peut modifier les métadonnées, par un mode effectif `Modify` ou, à défaut,
par `SharedMutable` (MM-03.3.8) ; la destination `dst` du bloc est encore utilisable
(MM-03.3.1), peut recevoir une valeur (sans feuille `Init`, comme pour O4.2) et respecte la
restriction de non-échappement envers `via` (MM-03.3.6). -/
def IssuePre (k : K) (s : S3) (ar : Arena) (via : Nat) (region : List Nat) (dst : Nat) : Prop :=
  (∀ l ∈ region, l ∈ ar.available) ∧
  (∀ e ∈ ar.issued, s.Active e.2 → ∀ l ∈ region, l ∉ e.1) ∧
  s.Active ar.internal ∧ (∀ l ∈ region, effective s ar.internal l = some .modify) ∧
  s.Active via ∧ (via = ar.anchor ∨ ar.anchor ∈ s.ancs via) ∧
  (∀ l ∈ s.afp ar.anchor, effective s via l = some .modify ∨
    (effective s via l ≠ none ∧ k.SharedMutable l)) ∧
  s.Usable dst ∧ (∀ l ∈ footprint s.P dst, s.I l ≠ .init) ∧ NoEscape s via (placeFrame s.P dst)

instance (k : K) [DecidablePred k.SharedMutable] (s : S3) (ar : Arena) (via : Nat)
    (region : List Nat) (dst : Nat) : Decidable (IssuePre k s ar via region dst) := by
  unfold IssuePre NoEscape; infer_instance

/-- Effet de `arena.issue(region)` (MM-03.3 §6) : retrait de `available` ; autorité exclusive
dérivée de `internal` sur la région, détenue par le cadre courant ; ajout à `issued` ; la valeur
reçue en `dst` est initialisée et ancrée sur `via` ; les régions déjà émises sont inchangées. -/
def issueEff (s : S3) (ar : Arena) (via : Nat) (region : List Nat) (dst : Nat) : S3 × Arena :=
  ({ s.addAuth ⟨.modify, some ar.internal, region, s.top, true⟩ with
      I := fun l => if l ∈ footprint s.P dst then .init else s.I l
      D := fun q => if q = dst then s.D dst ++ [via] else s.D q },
   { ar with
      available := ar.available.filter fun l => decide (l ∉ region)
      issued := (region, s.A.length) :: ar.issued })

/-- `arena.issue` comme relation (MM-03.3 §6). -/
def IssueStep (k : K) (ar : Arena) (via : Nat) (region : List Nat) (dst : Nat) (s : S3) :
    Outcome3 (S3 × Arena) → Prop :=
  Guarded (IssuePre k s ar via region dst) (issueEff s ar via region dst)

/-- Préconditions de `arena.reset()` (MM-03.3 §6 ; I3) : aucune autorité émise encore active ;
aucune valeur encore utilisable n'a une ancre que la réinitialisation invalide (`Invalidates`,
MM-03.3.8). Aucune condition d'exclusivité (arbitrage 3). -/
def ResetPre (k : K) (s : S3) (ar : Arena) : Prop :=
  (∀ e ∈ ar.issued, ¬ s.Active e.2) ∧
  (∀ q ∈ List.range s.P.length, s.Usable q → ∀ x ∈ s.D q, ¬ k.Invalidates s ar.anchor x)

instance (k : K) [∀ s r x, Decidable (k.Invalidates s r x)] (s : S3) (ar : Arena) :
    Decidable (ResetPre k s ar) := by
  unfold ResetPre; infer_instance

/-- Effet de `arena.reset()` (MM-03.3 §6) : le stockage administré redevient disponible et les
anciennes émissions sont oubliées ; l'état `S3` est inchangé. -/
def resetEff (s : S3) (ar : Arena) : S3 × Arena :=
  (s, { ar with available := ar.storage, issued := [] })

/-- `arena.reset` comme relation (MM-03.3 §6). -/
def ResetStep (k : K) (ar : Arena) (s : S3) : Outcome3 (S3 × Arena) → Prop :=
  Guarded (ResetPre k s ar) (resetEff s ar)

/-- Issue `ok` de `arena.issue` (MM-03.3 §6). -/
theorem issue_ok_iff {k : K} {ar ar' : Arena} {via dst : Nat} {region : List Nat} {s s' : S3} :
    IssueStep k ar via region dst s (.ok (s', ar')) ↔
      IssuePre k s ar via region dst ∧ (s', ar') = issueEff s ar via region dst := Guarded.ok_iff

/-- Issue `ok` de `arena.reset` (MM-03.3 §6). -/
theorem reset_ok_iff {k : K} {ar ar' : Arena} {s s' : S3} :
    ResetStep k ar s (.ok (s', ar')) ↔ ResetPre k s ar ∧ (s', ar') = resetEff s ar :=
  Guarded.ok_iff

/-- Une autorité active dérivée de `internal` couvrant `l` retire à `internal` l'autorité
effective de modification sur `l` : la disjonction d'une nouvelle émission avec les émissions
actives découle de la discipline d'accès (MM-03.3 §6). -/
theorem arena_issue_disjoint_of_authority {s : S3} {ar : Arena} {region : List Nat}
    (hwf : WF3 s) (hai : ArenaInv s ar)
    (hm : ∀ l ∈ region, effective s ar.internal l = some .modify) :
    ∀ e ∈ ar.issued, s.Active e.2 → ∀ l ∈ region, l ∉ e.1 := by
  intro e he ha l hl hle
  obtain ⟨y, hy, ho, hf, hmd⟩ := hai.2.2.2.2.1 e he
  obtain ⟨y', hy', ya⟩ := ha; rw [hy] at hy'; cases hy'
  have hlt := hwf.1 e.2 y ar.internal hy ho
  have hanc : ar.internal ∈ s.ancs e.2 := by
    unfold S3.ancs; rw [chain_cons (by simp [S3.org, hy, ho]) hlt]; exact List.mem_cons_self ..
  have hd : Mode.modify ∈ descModes s ar.internal l :=
    mem_descModes.2 ⟨e.2, y, hy, ya, hf ▸ hle, hanc, hmd⟩
  obtain ⟨x, hx, -, -, he'⟩ := effective_some (hm l hl)
  rcases effOf_cases he' with ⟨h0, -⟩ | ⟨-, hn, -⟩
  · simp [h0] at hd
  · exact hn hd

theorem org_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).org j = s.org j := by simp only [S3.org, addAuth_lt h]

theorem afp_addAuth_lt {s : S3} {y₀ : Authority} {j : Nat} (h : j < s.A.length) :
    (s.addAuth y₀).afp j = s.afp j := by simp only [S3.afp, addAuth_lt h]

theorem active_addAuth_iff {s : S3} {y₀ : Authority} {x : Nat} (hx : x < s.A.length) :
    (s.addAuth y₀).Active x ↔ s.Active x := by
  simp only [S3.Active, addAuth_lt hx]

/-- `arena_issue_preserves_disjointness` (MM-03.3 §6, §10) : `issue` préserve `WF3`, `Inv3` et
l'invariant de l'arène. La disjonction de la nouvelle région avec les émissions actives est
obtenue de la discipline d'accès (`arena_issue_disjoint_of_authority`), non de la précondition
correspondante. Aucune hypothèse sur `K`. -/
theorem arena_issue_preserves_disjointness {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hinv : Inv3 s) (hai : ArenaInv s ar)
    (h : IssueStep k ar via region dst s (.ok (s', ar'))) :
    WF3 s' ∧ Inv3 s' ∧ ArenaInv s' ar' := by
  obtain ⟨⟨h1, -, ⟨x, hx, xa⟩, h4, hvia, hvr, -, -⟩, e⟩ := issue_ok_iff.1 h
  have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
  simp only [issueEff] at e1 e2; subst e1 e2
  have hs := lt_of_getElem? hx
  have hfp : ∀ l ∈ region, l ∈ x.footprint := fun l hl => by
    obtain ⟨x', hx', -, hp, -⟩ := effective_some (h4 l hl); rw [hx] at hx'; cases hx'; exact hp
  obtain ⟨hwf₁, hinv₁⟩ := addAuth_preserves (f := s.top) hwf hinv hx xa hfp
    (fun l hl => by rw [h4 l hl]; simp [Allows, OptP, Mode.le])
  obtain ⟨hwf', hinv'⟩ := (show SameSkel (s.addAuth ⟨.modify, some ar.internal, region, s.top, true⟩)
      { s.addAuth ⟨.modify, some ar.internal, region, s.top, true⟩ with
        I := fun l => if l ∈ footprint s.P dst then .init else s.I l
        D := fun q => if q = dst then s.D dst ++ [via] else s.D q } from ⟨rfl, fun _ => rfl⟩).preserves
    rfl rfl rfl hwf₁ hinv₁ fun q hq y hy => by
      simp only at hy; split at hy
      · rename_i hqd; subst hqd; rcases List.mem_append.1 hy with hy | hy
        · exact hinv₁.2.2.1 _ hq y hy
        · simp at hy; subst hy; exact active_addAuth hvia
      · exact hinv₁.2.2.1 q hq y hy
  have hdis := arena_issue_disjoint_of_authority hwf hai h4
  obtain ⟨c0, c1, c2, c3, c4, a1, a2, a3, a4⟩ := hai
  have old : ∀ e ∈ ar.issued, e.2 < s.A.length := fun e he => by
    obtain ⟨y, hy, -⟩ := c4 e he; exact lt_of_getElem? hy
  have hanc : ar.anchor < s.A.length := by
    obtain ⟨y, hy, -⟩ := hvia; have := lt_of_getElem? hy
    rcases hvr with e | e
    · omega
    · have := chain_lt e; omega
  refine ⟨hwf', hinv', fun l hl => ?_, fun e he l hl => ?_, ?_, fun e he ha l hl => ?_,
    fun e he => ?_, (org_addAuth_lt hs).trans a1, a2, fun l hl => ?_, fun l hl => ?_⟩
  · exact c0 l (List.mem_filter.1 hl).1
  · rcases List.mem_cons.1 he with rfl | he
    · exact c0 l (h1 l hl)
    · exact c1 e he l hl
  · refine List.pairwise_cons.2 ⟨fun e he _ ha l hl hle => ?_, c2.imp_of_mem fun {e e'} he he' h ha ha' =>
      h ((active_addAuth_iff (old e he)).1 ha) ((active_addAuth_iff (old e' he')).1 ha')⟩
    · exact hdis e he ((active_addAuth_iff (old e he)).1 ha) l hl hle
  · rcases List.mem_cons.1 he with rfl | he
    · intro h'; have := (List.mem_filter.1 h').2; simp at this; exact this hl
    · have := c3 e he ((active_addAuth_iff (old e he)).1 ha) l hl
      exact fun h' => this (List.mem_filter.1 h').1
  · rcases List.mem_cons.1 he with rfl | he
    · exact ⟨_, addAuth_self _ _, rfl, rfl, rfl⟩
    · obtain ⟨y, hy, hh⟩ := c4 e he
      exact ⟨y, by show (s.addAuth _).A[e.2]? = _; rw [addAuth_lt (old e he)]; exact hy, hh⟩
  · show l ∈ (s.addAuth _).afp ar.internal; rw [afp_addAuth_lt hs]; exact a3 l hl
  · show l ∉ (s.addAuth _).afp ar.anchor; rw [afp_addAuth_lt hanc]; exact a4 l hl

/-- `arena_issue_keeps_earlier_blocks` (MM-03.3 §6, §10) : les émissions antérieures restent
émises avec leur autorité inchangée, et la nouvelle région est disjointe de celles qui sont
encore actives. Aucune hypothèse sur `K`. -/
theorem arena_issue_keeps_earlier_blocks {k : K} {s s' : S3} {ar ar' : Arena} {via dst : Nat}
    {region : List Nat} (hwf : WF3 s) (hai : ArenaInv s ar)
    (h : IssueStep k ar via region dst s (.ok (s', ar'))) :
    ∀ e ∈ ar.issued, e ∈ ar'.issued ∧ s'.A[e.2]? = s.A[e.2]? ∧
      (s.Active e.2 → ∀ l ∈ region, l ∉ e.1) := by
  obtain ⟨⟨-, -, -, h4, -⟩, e⟩ := issue_ok_iff.1 h
  have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
  simp only [issueEff] at e1 e2; subst e1 e2
  intro e he
  obtain ⟨y, hy, -⟩ := hai.2.2.2.2.1 e he
  exact ⟨List.mem_cons_of_mem _ he, addAuth_lt (lt_of_getElem? hy),
    arena_issue_disjoint_of_authority hwf hai h4 e he⟩

/-- Une autorité émise encore active rend `reset` refusé (MM-03.3 §6). Aucune hypothèse sur
`K`. -/
theorem arena_reset_rejects_live_issued {k : K} {s : S3} {ar : Arena} {e : List Nat × Nat}
    (he : e ∈ ar.issued) (ha : s.Active e.2) : ResetStep k ar s .reject :=
  .reject fun h => h.1 e he ha

/-- Obligation de `Invalidates` pour l'arène (MM-03.3.8, arbitrage 3) : `reset` invalide
l'ancre de l'arène et toute autorité qui en dérive. -/
def ArenaResetContract (k : K) (s : S3) (ar : Arena) : Prop :=
  ∀ x, (x = ar.anchor ∨ ar.anchor ∈ s.ancs x) → k.Invalidates s ar.anchor x

/-- `arena_reset_rejects_live_dependents` (MM-03.3 §6, I3, §10), conditionné à l'obligation
`ArenaResetContract` de `Invalidates` (MM-03.3.8) : si une valeur encore utilisable est ancrée
sur l'arène ou sur une autorité qui en dérive, `reset` est refusé. -/
theorem arena_reset_rejects_live_dependents_underInv {k : K} {s : S3} {ar : Arena}
    (hk : ArenaResetContract k s ar) {q x : Nat} (hq : s.Usable q) (hx : x ∈ s.D q)
    (hxa : x = ar.anchor ∨ ar.anchor ∈ s.ancs x) : ResetStep k ar s .reject := by
  refine .reject fun h => h.2 q ?_ hq x hx (hk x hxa)
  obtain ⟨f, hf, -⟩ := hq; simp [placeFrame] at hf
  obtain ⟨pl, hpl, -⟩ := hf; exact List.mem_range.2 (lt_of_getElem? hpl)

/-- `reset` préserve l'invariant de l'arène (MM-03.3 §6 : préservation des invariants de
disjonction) ; l'état `S3` est inchangé. -/
theorem arena_reset_preserves {k : K} {s s' : S3} {ar ar' : Arena} (hai : ArenaInv s ar)
    (h : ResetStep k ar s (.ok (s', ar'))) : s' = s ∧ ArenaInv s' ar' := by
  obtain ⟨-, e⟩ := reset_ok_iff.1 h
  have e1 := congrArg Prod.fst e; have e2 := congrArg Prod.snd e
  simp only [resetEff] at e1 e2; subst e1 e2
  obtain ⟨-, -, -, -, -, a1, a2, a3, a4⟩ := hai
  exact ⟨rfl, fun l hl => hl, fun _ he => (by cases he), List.Pairwise.nil,
    fun _ he => (by cases he), fun _ he => (by cases he), a1, a2, a3, a4⟩

/-! ## Cas d'épreuve (MM-03.3 §11)

Chaque verdict est obtenu par `decide` sur la précondition de l'opération en cause. Les états
sont construits par les effets des opérations à partir de `S3.init`. Le classement de chaque cas
(noyau, abstraction avec `K` instancié, hors noyau) est donné dans le rapport. -/

/-- Contrats vides : aucune déclaration, aucune mutation partagée, aucun épinglage, aucune
invalidation. -/
def K0 : K := ⟨fun _ _ => False, fun _ => False, fun _ => False, fun _ _ _ => False⟩
instance : ∀ r r', Decidable (K0.DeclaredDisjoint r r') := fun _ _ => instDecidableFalse
instance : DecidablePred K0.Pinned := fun _ => instDecidableFalse

/-- Contrats de l'arène : métadonnées (feuille 0) en mutation partagée ; `reset` de l'arène
d'ancre `r` invalide `r` et toute autorité qui en dérive. -/
def KA : K := ⟨fun _ _ => False, fun l => l = 0, fun _ => False, fun s r x => x = r ∨ r ∈ s.ancs x⟩
instance : DecidablePred KA.SharedMutable := fun l => inferInstanceAs (Decidable (l = 0))
instance : DecidablePred KA.Pinned := fun _ => instDecidableFalse
instance : ∀ s r x, Decidable (KA.Invalidates s r x) := fun s r x =>
  inferInstanceAs (Decidable (x = r ∨ r ∈ s.ancs x))

/-- `KA` satisfait l'obligation `ArenaResetContract` dans tout état, pour toute arène. -/
theorem KA_contract (s : S3) (ar : Arena) : ArenaResetContract KA s ar := fun _ h => h

/-- Contrats d'épinglage : la feuille 0 est épinglée. -/
def KP : K := ⟨fun _ _ => False, fun _ => False, fun l => l = 0, fun _ _ _ => False⟩
instance : DecidablePred KP.Pinned := fun l => inferInstanceAs (Decidable (l = 0))

/-! ### Cas 1 : deux observations d'une même feuille (attendu : autorisé) -/

def c1a : S3 := enterEff S3.init [(none, 0)]
def c1b : S3 := write3Eff c1a [0]
def c1c : S3 := deriveEff c1b 0 0 .observe
def c1d : S3 := deriveEff c1c 0 0 .observe
example : EnterStep [(none, 0)] S3.init (.ok c1a) := .ok (by decide)
example : Write3Step 0 [0] c1a (.ok c1b) := .ok (by decide)
example : DeriveStep 0 0 .observe c1b (.ok c1c) := .ok (by decide)
example : DeriveStep 0 0 .observe c1c (.ok c1d) := .ok (by decide)
example : Read3Step 1 [0] c1d (.ok c1d) ∧ Read3Step 2 [0] c1d (.ok c1d) :=
  ⟨.ok (by decide), .ok (by decide)⟩

/-! ### Cas 2 : observation et modification incompatibles (attendu : rejet) -/

example : DeriveStep 0 0 .modify c1c .reject := .reject (by decide)
example : Write3Step 0 [0] c1c .reject := .reject (by decide)

/-! ### Cas 3 : deux champs réellement disjoints (attendu : modifications autorisées) -/

def c3a : S3 := enterEff S3.init [(none, 0), (some 0, 0), (some 0, 0)]
def c3b : S3 := deriveEff c3a 0 1 .modify
def c3c : S3 := deriveEff c3b 0 2 .modify
example : DeriveStep 0 1 .modify c3a (.ok c3b) := .ok (by decide)
example : DeriveStep 0 2 .modify c3b (.ok c3c) := .ok (by decide)
example : Write3Step 1 [1] c3c (.ok (write3Eff c3c [1])) := .ok (by decide)
example : Write3Step 2 [2] (write3Eff c3c [1]) (.ok (write3Eff (write3Eff c3c [1]) [2])) :=
  .ok (by decide)

/-! ### Cas 4 : observation d'un élément et modification invalidante du conteneur
(attendu : rejet). Le conteneur est l'emplacement 0, ses éléments 1 et 2 en sont des parties
(arbitrage 3) ; la modification invalidante est une écriture de toute son empreinte. -/

def c4b : S3 := deriveEff c3a 0 1 .observe
example : DeriveStep 0 1 .observe c3a (.ok c4b) := .ok (by decide)
example : Write3Step 0 [1, 2] c4b .reject := .reject (by decide)
example : Write3Step 0 [1, 2] c3a (.ok (write3Eff c3a [1, 2])) := .ok (by decide)

/-! ### Cas 5 : séparation d'une région en deux parties (attendu : autorités indépendantes) -/

def c5b : S3 := splitEff c3a 0 [[1], [2]]
example : SplitStep K0 0 [[1], [2]] c3a (.ok c5b) := .ok (by decide)
example : Write3Step 1 [1] c5b (.ok (write3Eff c5b [1])) := .ok (by decide)
example : Write3Step 2 [2] c5b (.ok (write3Eff c5b [2])) := .ok (by decide)
example : effective c5b 0 1 = none ∧ effective c5b 0 2 = none := by decide
example : I1b c5b := by decide
/-- Après un `split` partiel, l'origine garde le mode effectif `Modify` sur la partie non
distribuée (MM-03.3.5). -/
example : effective (splitEff c3a 0 [[1]]) 0 2 = some .modify ∧
    effective (splitEff c3a 0 [[1]]) 0 1 = none := by decide

/-! ### Cas 6 : deux émissions successives depuis une arène (attendu : autorisées) -/

/-- Emplacements : 0 métadonnées de l'arène, 1 stockage administré de feuilles 2 et 3, 4 et 5
destinations des blocs. Autorités racines : 0 (ancre), 1 (`internal`), 2, 3. -/
def c6a : S3 := enterEff S3.init [(none, 0), (none, 0), (some 1, 0), (some 1, 0), (none, 0), (none, 0)]
def ar6 : Arena := ⟨0, [2, 3], [2, 3], [], 1⟩
def c6b : S3 × Arena := issueEff c6a ar6 0 [2] 4
example : IssueStep KA ar6 0 [2] 4 c6a (.ok c6b) := .ok (by decide)
example : IssueStep KA c6b.2 0 [3] 5 c6b.1 (.ok (issueEff c6b.1 c6b.2 0 [3] 5)) := .ok (by decide)
example : IssueStep KA c6b.2 0 [2] 5 c6b.1 .reject := .reject (by decide)

/-- L'arène du cas 6 satisfait son invariant, et l'état de départ `WF3 ∧ Inv3` : les hypothèses
de `arena_issue_preserves_disjointness` ne sont pas vides. -/
example : ArenaInv c6a ar6 :=
  ⟨(by decide), (by decide), (by decide), (by decide), fun _ h => (nomatch h), (by decide),
    (by decide), (by decide), (by decide)⟩
example : WF3 c6a ∧ Inv3 c6a :=
  reachable_access_invariant_underDD (k := K0) (fun _ _ h => h.elim) (.enter .init (.ok (by decide)))

/-! ### Cas 7 : `arena.reset()` avec dépendant encore utilisable (attendu : rejet) -/

example : ResetStep KA c6b.2 c6b.1 .reject := .reject (by decide)
def c7a : S3 := releaseEff c6b.1 4
example : ReleaseStep 4 c6b.1 (.ok c7a) := .ok (by decide)
example : ResetStep KA c6b.2 c7a .reject := .reject (by decide)

/-! ### Cas 8 : retour d'un buffer dépendant d'un paramètre de l'appelant (attendu : autorisé
sous contrat). Appelant : 0 donnée, 1 destination. Appelé : 2 valeur ; paramètre `let` dérivé
de l'autorité 0 de l'appelant (arbitrage 1). -/

def c8a : S3 := enterEff (enterEff S3.init [(none, 0), (none, 0)]) [(none, 0)]
def c8b : S3 := deriveEff c8a 0 0 .observe
def c8c : S3 := write3Eff c8b [2]
def c8d : S3 := dependEff c8c 2 3
def c8e : S3 := transferEff c8d 2 1 []
example : EnterStep [(none, 0)] (enterEff S3.init [(none, 0), (none, 0)]) (.ok c8a) := .ok (by decide)
example : DeriveStep 0 0 .observe c8a (.ok c8b) := .ok (by decide)
example : Write3Step 2 [2] c8b (.ok c8c) := .ok (by decide)
example : DependStep 2 3 c8c (.ok c8d) := .ok (by decide)
example : TransferStep K0 2 1 [] c8d (.ok c8e) := .ok (by decide)
example : ExitStep c8e (.ok (exitEff c8e)) := .ok (by decide)
example : (exitEff c8e).D 1 = [0] ∧ effective (exitEff c8e) 0 0 = some .modify := by decide

/-! ### Cas 9 : capture temporaire d'un accès par une valeur non échappante (attendu :
autorisée). La valeur en 1 dépend de l'accès 2 à la donnée 0, dans le même cadre. -/

def c9a : S3 := enterEff S3.init [(none, 0), (none, 0)]
def c9b : S3 := deriveEff c9a 0 0 .observe
def c9c : S3 := write3Eff c9b [1]
example : DeriveStep 0 0 .observe c9a (.ok c9b) := .ok (by decide)
example : Write3Step 1 [1] c9b (.ok c9c) := .ok (by decide)
example : DependStep 1 2 c9c (.ok (dependEff c9c 1 2)) := .ok (by decide)
/-- Tant que la valeur est utilisable, l'accès capturé ne peut pas être restitué (O3.3). -/
example : ReleaseStep 2 (dependEff c9c 1 2) .reject := .reject (by decide)

/-! ### Cas 10 : capture d'un accès local dans une valeur échappante (attendu : rejet).
Appelant : 0 destination. Appelé : 1 local, 2 valeur capturant l'accès 3 dérivé du local. -/

def c10a : S3 := enterEff (enterEff S3.init [(none, 0)]) [(none, 0), (none, 0)]
def c10b : S3 := write3Eff (deriveEff c10a 1 1 .observe) [2]
def c10c : S3 := transferEff (dependEff c10b 2 3) 2 0 []
example : DeriveStep 1 1 .observe c10a (.ok (deriveEff c10a 1 1 .observe)) := .ok (by decide)
example : Write3Step 2 [2] (deriveEff c10a 1 1 .observe) (.ok c10b) := .ok (by decide)
example : DependStep 2 3 c10b (.ok (dependEff c10b 2 3)) := .ok (by decide)
example : TransferStep K0 2 0 [] (dependEff c10b 2 3) (.ok c10c) := .ok (by decide)
example : ExitStep c10c .reject := .reject (by decide)

/-! ### Cas 11 : transfert invalidant une projection active (attendu : rejet) -/

def c11a : S3 := write3Eff (enterEff S3.init [(none, 0), (some 0, 0), (some 0, 0), (none, 0)]) [1, 2]
def c11b : S3 := deriveEff c11a 0 1 .observe
example : DeriveStep 0 1 .observe c11a (.ok c11b) := .ok (by decide)
example : TransferStep K0 0 3 [] c11b .reject := .reject (by decide)
example : TransferStep K0 0 3 [] c11a (.ok (transferEff c11a 0 3 [])) := .ok (by decide)

/-! ### Cas 13 : stockage épinglé (attendu : déplacement physique interdit) -/

def c13a : S3 := write3Eff (enterEff S3.init [(none, 0), (none, 0)]) [0]
example : TransferStep KP 0 1 [] c13a .reject := .reject (by decide)
example : TransferStep K0 0 1 [] c13a (.ok (transferEff c13a 0 1 [])) := .ok (by decide)

/-! ### Cas 15 : deux colonnes SoA disjointes (attendu : modifications indépendantes) -/

def c15a : S3 := enterEff S3.init
  [(none, 0), (some 0, 0), (some 0, 0), (some 1, 0), (some 1, 0), (some 2, 0), (some 2, 0)]
def c15b : S3 := deriveEff (deriveEff c15a 0 1 .modify) 0 2 .modify
example : DeriveStep 0 1 .modify c15a (.ok (deriveEff c15a 0 1 .modify)) := .ok (by decide)
example : DeriveStep 0 2 .modify (deriveEff c15a 0 1 .modify) (.ok c15b) := .ok (by decide)
example : Write3Step 1 [3, 4] c15b (.ok (write3Eff c15b [3, 4])) := .ok (by decide)
example : Write3Step 2 [5, 6] (write3Eff c15b [3, 4])
    (.ok (write3Eff (write3Eff c15b [3, 4]) [5, 6])) := .ok (by decide)

/-! ### Cas 16 : retour d'un buffer dépendant de l'arène de l'appelant (attendu : `ok`).
Appelant : 0 métadonnées, 1 stockage (feuilles 2, 3), 4 destination. Appelé : 5 bloc reçu ;
paramètre `let` 4 dérivé de l'ancre 0. -/

def c16a : S3 := enterEff (enterEff S3.init
  [(none, 0), (none, 0), (some 1, 0), (some 1, 0), (none, 0)]) [(none, 0)]
def ar16 : Arena := ⟨0, [2, 3], [2, 3], [], 1⟩
def c16b : S3 := deriveEff c16a 0 0 .observe
def c16c : S3 × Arena := issueEff c16b ar16 4 [2] 5
def c16d : S3 := transferEff c16c.1 5 4 [5]
def c16e : S3 := exitEff c16d
example : DeriveStep 0 0 .observe c16a (.ok c16b) := .ok (by decide)
example : IssueStep KA ar16 4 [2] 5 c16b (.ok c16c) := .ok (by decide)
example : TransferStep KA 5 4 [5] c16c.1 (.ok c16d) := .ok (by decide)
example : ExitStep c16d (.ok c16e) := .ok (by decide)
example : c16e.D 4 = [0] ∧ c16e.Active 5 ∧ c16e.frameOf 5 = some 1 := by decide
/-- Après le retour, le buffer reste utilisable dans l'appelant : `reset` est refusé, même
après restitution de l'autorité du bloc. -/
example : ResetStep KA c16c.2 c16e .reject := .reject (by decide)
example : ReleaseStep 5 c16e (.ok (releaseEff c16e 5)) := .ok (by decide)
example : ResetStep KA c16c.2 (releaseEff c16e 5) .reject := .reject (by decide)

/-! ### Cas 17 : retour d'une valeur ancrée sur un emplacement local de l'appelé (attendu :
rejet). Appelant : 0 destination. Appelé : 1 local, 2 valeur ancrée sur l'autorité racine 1. -/

def c17a : S3 := write3Eff (enterEff (enterEff S3.init [(none, 0)]) [(none, 0), (none, 0)]) [2]
example : DependStep 2 1 c17a (.ok (dependEff c17a 2 1)) := .ok (by decide)
example : TransferStep K0 2 0 [] (dependEff c17a 2 1) .reject := .reject (by decide)

/-! ## Constats cités par le rapport -/

/-- Contrats déclarant disjointes toutes les régions, sans l'obligation `DDSound`. -/
def KT : K := ⟨fun _ _ => True, fun _ => False, fun _ => False, fun _ _ _ => False⟩
instance : ∀ r r', Decidable (KT.DeclaredDisjoint r r') := fun _ _ => instDecidableTrue

/-- Sans l'obligation `DDSound` (MM-03.3.8), `split` (MM-03.3 §3, O2) accepte deux régions qui
se chevauchent et viole I1 : l'hypothèse de `split_preserves_underDD` est nécessaire. -/
theorem split_unsound_without_DD :
    SplitStep KT 0 [[1], [1]] c3a (.ok (splitEff c3a 0 [[1], [1]])) ∧
    ¬ I1 (splitEff c3a 0 [[1], [1]]) := by
  refine ⟨.ok (by decide), fun h => ?_⟩
  have := h 1 2 1 .modify .modify (by decide) (by decide) (by decide)
  simp [Compat] at this

/-- `transfer` (MM-03.3 §3, O4) n'exige aucun droit d'accès : l'appelé déplace un emplacement
local de l'appelant (0) vers son propre emplacement (2). -/
example : TransferStep K0 0 2 [] (enterEff (write3Eff (enterEff S3.init [(none, 0), (none, 0)]) [0])
    [(none, 0)]) (.ok (transferEff (enterEff (write3Eff (enterEff S3.init [(none, 0), (none, 0)])
      [0]) [(none, 0)]) 0 2 [])) := .ok (by decide)

/-- `transfer` refuse de transférer l'autorité racine d'un local de l'appelé (1) avec une valeur
rendue à l'appelant (O4 ; arbitrage 2). -/
example : TransferStep K0 2 0 [1] (write3Eff (write3Eff (enterEff (enterEff S3.init [(none, 0)])
    [(none, 0), (none, 0)]) [1]) [2]) .reject := .reject (by decide)

/-- `canRead3` (MM-03.3 §5) n'exige pas que l'autorité soit détenue par le cadre courant :
l'appelé lit un emplacement de l'appelant par l'autorité racine de celui-ci. -/
example : Read3Step 0 [0] (enterEff (write3Eff (enterEff S3.init [(none, 0), (none, 0)]) [0])
    [(none, 0)]) (.ok (enterEff (write3Eff (enterEff S3.init [(none, 0), (none, 0)]) [0])
      [(none, 0)])) := .ok (by decide)

end Ern.MM03
