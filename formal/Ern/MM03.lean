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

end Ern.MM03
