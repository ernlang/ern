# Spec 2, jalon 4, tranche 2 — couche E, fragment d'événements

Formalisation exploratoire, branche `formal/spec2-m4`, jamais mergée. Sources lues : le brief « couche E, fragment d'événements » et `ERN_WC5_1_FINAL.md`, appelé ici « WC5.1 corrigé », clauses C26, C27, C30–C34, C36–C42, C48 et C53. Le corpus n'est pas utilisé. Les numéros de ligne sont ceux du commit qui suit `e774bef` (docstrings ajoutées). Modules dans `formal/Ern/Concurrency/EventModel/`.

C'est le niveau « fragment ERN » de WC5.1 corrigé C53. Le fragment ne dépend pas de la machine d'autorités : aucun module existant de `Ern.Concurrency` n'est importé, aucune définition existante n'est modifiée.

## Hypothèses du fragment

1. Exécutions finies ; une seule unité atomique `x` et une seule feuille ordinaire `d` par graphe. Rien n'est affirmé au-delà.
2. La feuille ordinaire n'a pas de valeurs : elle ne sert qu'aux conflits et aux courses. L'unité atomique a des valeurs, y compris pour ses accès ordinaires.
3. `sw` par lecture directe seulement (C32 point 1, C48). Aucune séquence de libération.
4. `seq_cst` n'est pris que pour ses rôles de libération et d'acquisition (C40). Aucune contrainte globale n'est formalisée.
5. `rf` n'est contraint par aucun ordre d'exécution, seulement par `EventConsistent`. Le fragment n'adopte pas `NoThinAir_RC11` et ne dit rien de l'acyclicité de `po ∪ rf`.
6. La forme de cohérence est un choix du fragment. Aucune équivalence ni inclusion avec RC11 n'est revendiquée ; les résultats herdtools7 servent de comparaison, pas de source.

## Résultats

| Tâche | Obtenu |
|---|---|
| 1, définitions et décision | toutes les définitions du brief ; typage, chaque conjoint, `EventConsistent`, `sw`, `hb` et la course sont décidables |
| 2, lemmes généraux | les six énoncés prouvés |
| 3, témoins | G1 à G19 : tous les attendus du brief obtenus, aucun écart |

| Commit | Tâche |
|---|---|
| `978ce1d` | 1 : `Closure.lean`, `Graph.lean` |
| `ef55b0f` | 2 : `Lemmas.lean` |
| `599aead` | 3 : `Witness.lean` |

## Définitions (`Graph.lean`)

- **Ordres** `MOrd` (`:25`) : `rlx`, `rel`, `acq`, `acqRel`, `sc` (C40).
- **Genres** `Kind` (`:34`) : `readD`, `writeD` (sans valeur, C36) ; `readX v`, `writeX v` (accès ordinaires à `x`, C36, C42) ; `rsh o v` (`readShared`, C37) ; `wsh o v` (`writeShared`, C39) ; `rmw o vr vw` (RMW réussi, un seul événement, C39). Une comparaison-échange échouée est un `rsh` (C39).
- **Graphe** `Graph` (`:53`) : la valeur de l'écriture initiale, la liste des autres événements (contexte et genre), et `rf`, `mo` comme listes de paires.
- **Prédicats d'événement** : `onX`, `onD`, `isMod` (modifications de `x`, C31 : écriture initiale, `writeShared`, RMW, `write3(x, v)`), `isReadX`, `isRMW`, `isWrite`, `isAtomic`, `valW`, `valR`, `relCap`, `acqCap` (C32 point 1, C40), `:76`–`:139`.
- **Typage** `WellTyped` (`:160`), par `Kind.OrdOk` (`:150`) : les lignes de C40. Ce n'est pas un conjoint de `EventConsistent`.
- **Relations** : `PO` (`:169`), `RF` (`:173`), `MO` (`:176`), `SW` (`:180`), `HB` (`:188`), `RB` (`:192`), `ECO` (`:198`).
- **`EventConsistent`** (`:287`) : `RfWF` (`:256`), `MoTotal` (`:264`), `RmwAtomic` (`:275`), `Coherent` (`:280`), `HbIrrefl` (`:284`), nommés séparément.
- **Conflit** `Conflict` (`:309`), **course** `RaceOn` (`:316`) sur une paire, `Racy` (`:320`) pour le graphe.

### Décision de `hb` et d'`eco` (`Closure.lean`)

La clôture transitive d'une relation sur les événements `0, …, N - 1` est calculée par tours sur une table de booléens (`reach`, `:31`). Un tour ajoute les successeurs des nœuds atteints. `transGen_iff_reach` (`:215`) prouve que la table après `N + 1` tours est la clôture transitive, pour toute relation dont les extrémités sont des événements. Aucun ordre des arêtes n'est supposé.

La complétude repose sur un comptage. Tant que la table n'est pas close, chaque tour ajoute au moins une entrée (`cnt_succ`, `:194`), et il n'y en a que `N`. Elle est donc close après `N + 1` tours (`closed_final`, `:209`). Une table close contient tout le reachable (`complete`, `:89`). `decTransGen` (`Graph.lean:230`) en tire les instances de `HB` et d'`ECO`.

### Choix de représentation et écarts au brief

1. **L'écriture initiale est l'événement `0`**, hors de la liste. Il y en a donc exactement une par construction (C31), sans contexte.
2. **`po` est l'ordre de la liste** entre les événements d'un même contexte. C'est un ordre total strict par contexte ; tout tel ordre s'obtient en ordonnant la liste.
3. **`rf` et `mo` sont des données**, des listes de paires lues sur les événements du graphe (`RF`, `MO` exigent des extrémités `< size`). Les conjoints 1 et 2 peuvent donc échouer.
4. **Typage des extrémités de `rf`.** Il est dans le conjoint 1 : toute arête `rf` va d'une modification de `x` vers une lecture de `x` de même valeur, et chaque lecture de `x` a exactement une source.
5. **`hb`** est défini à la lettre du brief : la clôture transitive de `po ∪ sw`, ou bien la paire `(init, e)` pour tout autre événement `e`. Cette dernière règle est une convention du fragment : elle représente l'état construit avant le lancement des contextes.
6. **L'écriture initiale n'est dans aucun conflit**, n'ayant pas de contexte (« contextes distincts »). Cela ne change aucun verdict de course : elle est `hb`-avant tout autre événement, donc aucune paire qui la contient ne serait en course.
7. **Valeur de l'écriture initiale.** Tous les témoins la prennent à `0`, comme le brief.

## Tâche 2 — lemmes généraux (`Lemmas.lean`)

Tous **prouvés**, pour tout graphe, sans hypothèse sur sa forme.

| Lemme | Énoncé | Conjoints utilisés | Théorème |
|---|---|---|---|
| conjoint 5 depuis 4 | `Coherent g → HbIrrefl g` | 4 | `hbIrrefl_of_coherent` `:16` |
| init minimale pour `mo` | `EventConsistent g → ¬ MO g m 0` | 2 (irréflexivité de `mo`), 4, et la convention `hb` de l'écriture initiale | `init_mo_minimal` `:30` |
| pas de lecture d'une modification `hb`-postérieure | `EventConsistent g → RF g w r → ¬ HB g r w` | 4 | `rf_not_hb_later` `:42` |
| deux RMW distincts, même source | impossible dans un graphe cohérent, quels que soient leurs ordres (C31) | 2 (totalité de `mo`), 3 | `rmw_sources_distinct` `:52` |
| deux événements atomiques | jamais en course (C33 point 3) | aucun | `atomic_no_race` `:66` |
| paire ordonnée par `hb` | pas en course | aucun | `hb_no_race` `:74` |

Lemme auxiliaire : un RMW réussi est une modification de `x` (`isMod_of_isRMW`, `:20`).

## Tâche 3 — témoins (`Witness.lean`)

Chaque graphe est donné explicitement. `chain` (`:18`) écrit `mo` comme l'ordre qui énumère ses éléments dans l'ordre donné. Les faits sont écrits depuis le brief, puis décidés par `decide`. « Cohérent » se lit `EventConsistent`. Tous les graphes sauf G19 sont aussi `WellTyped`.

### *Message passing* (C32 point 1, C33, C40)

Événements : `init` (0), `a` (1), `b` (2), `e` (3), `g` (4) ; graphe `mp` (`:32`).

| Graphe | Attendu | Obtenu | Théorème | herdtools7 |
|---|---|---|---|---|
| G1 `release`, `acquire` | cohérent ; `sw(b, e)` ; `hb(a, g)` ; pas de course | obtenu | `G1` `:39` | A1 |
| G2 `e` lit `0` de `init`, pas de `g` | cohérent ; aucune arête `sw` ; pas de course | obtenu | `G2` `:49` | A1 |
| G3 `relaxed`, `relaxed` | cohérent ; pas de `sw` ; course `(a, g)` | obtenu | `G3` `:52` | A2 |
| G4 `release`, `relaxed` | idem | obtenu | `G4` `:57` | — |
| G5 `relaxed`, `acquire` | idem | obtenu | `G5` `:62` | — |
| G6 `seq_cst`, `seq_cst` | cohérent ; `sw(b, e)` ; pas de course | obtenu | `G6` `:68` | A3 |

### Accès mixtes (C30, C31, C33, C36, C42)

| Graphe | Attendu | Obtenu | Théorème | herdtools7 |
|---|---|---|---|---|
| G7 `writeShared` relaxed contre `read3(x)` | cohérent ; course `(s, r)` | obtenu | `G7` `:80` | C1 |
| G8 `writeShared` relaxed contre `write3(x, 2)` | cohérent ; `w` dans `mo` ; course `(s, w)` | obtenu : `w` est une modification et `mo(s, w)` | `G8` `:88` | — |
| G9 deux `writeShared` relaxed | cohérent ; pas de course | obtenu | `G9` `:98` | C2 |
| G10 deux `write3(d)` | cohérent ; course | obtenu | `G10` `:105` | C3 |

### RMW (C31, C32 point 1, C39, C40)

| Graphe | Attendu | Obtenu | Théorème | herdtools7 |
|---|---|---|---|---|
| G11 `m0` lit `0`, `m1` lit `1` | cohérent | obtenu | `G11` `:116` | D1 |
| G12 `m1` lit aussi `0`, deux ordres `mo` | non cohérent, le conjoint 3 échoue dans les deux cas | obtenu ; dans les deux cas, les conjoints 1, 2, 4 et 5 tiennent, seul le 3 échoue | `G12` `:127` | D1 à D3 |
| G13 RMW contre comparaison-échange échouée | cohérent ; `f` n'est pas une modification | obtenu | `G13` `:140` | — |
| G14 verrou, prises `acquire`, libérations `release` | cohérent ; `sw(U0, A1)` ; `hb(w0, w1)` ; pas de course | obtenu | `G14` `:153` | B1 |
| G15 libérations `relaxed` | cohérent ; pas de `sw` ; course `(w0, w1)` | obtenu | `G15` `:159` | B2 |
| G16 prises `relaxed` | idem | obtenu | `G16` `:165` | B3 |
| G17 RMW `acq_rel` lu par `readShared` acquire | cohérent ; `sw(m, e)` ; pas de course | obtenu | `G17` `:176` | — |

**G12, observation.** La cohérence du fragment (`hb ; eco?` irréflexif) ne rejette pas G12. Le cycle `eco` entre les deux RMW, `m0 →mo m1 →rb m0` dans le premier ordre, ne passe par aucune arête `hb` : les deux prises en `acquire` ne se synchronisent pas, et l'écriture initiale ne reçoit aucune arête `eco`. Seule l'atomicité des RMW (conjoint 3) l'exclut.

La portée de ce résultat est limitée aux deux RMW non ordonnés par `hb`. Une vérification hors dépôt, par `#eval` des cinq conjoints, place les deux mêmes RMW dans un seul contexte, `po` les ordonnant. Dans les deux ordres `mo`, le conjoint 3 échoue, et le conjoint 4 aussi : `hb(m0, m1)` avec `eco(m1, m0)`.

Différence avec `rc11.cat` : dans le complément herdtools7, `coherencermw` seul suffisait à exclure les deux prises simultanées, le groupe D restant `Never` avec `atomicity` sauté. Le fragment n'a pas d'équivalent de `coherencermw` : pour deux RMW de contextes distincts non synchronisés, le conjoint 3 est le seul à les exclure. Le jugement sur cette forme de cohérence vous revient (hypothèse 6).

### Séquence de libération et typage (C32 point 1, C40, C48)

| Graphe | Attendu | Obtenu | Théorème | herdtools7 |
|---|---|---|---|---|
| G18 libération puis écriture atomique non-RMW du même thread, lue en `acquire` | cohérent ; aucune arête `sw` vers `e` ; course `(a, g)` | obtenu | `G18` `:191` | E1 : pas de course sous `rc11.cat` |
| G19 `readShared(x, release)` | mal typé (C40) | obtenu | `G19` `:199` | — |

**Couverture de la décision.** Dans tous les témoins, les arêtes `rf`, donc toutes les arêtes de `hb`, vont vers un événement plus loin dans la liste. Pour `hb`, la propriété « la décision ne suppose pas que les arêtes croissent dans l'ordre d'énumération » n'est établie que par la preuve générale (`transGen_iff_reach`). Le même moteur décide `eco`, qui a des arêtes vers l'arrière sous `decide` : l'arête `rb` de `e` (3) vers `b` (2) dans G2, et `mo(2, 1)` dans le second ordre de G12. La clôture est donc exercée sur des arêtes non croissantes à travers `eco`.

## Divergence avec `rc11.cat` : G18

G18 est le programme du test herdtools7 E1 (`RS+rel+rlx`).

- **Le programme.** Le thread 0 écrit `d`, puis fait `writeShared(x, 1, release)`, puis l'écriture atomique non-RMW `writeShared(x, 2, relaxed)`. Le thread 1 lit `2` en `acquire`, puis lit `d`.
- **Dans le fragment.** Le fragment n'a que l'arête `sw` par lecture directe : `e` lit `c`, qui est `relaxed`, et n'est donc la cible d'aucune arête `sw`. La lecture de `d` n'est pas `hb`-ordonnée avec l'écriture de `d` : course `(a, g)`, obtenue par `decide`.
- **Sous `rc11.cat`.** La séquence de libération `rs` contient, par le facteur `(sb & loc)?`, l'écriture atomique non-RMW suivante du même thread sur la même case. La lecture de `2` synchronise donc avec la libération de `1`, et herd7 ne signale pas de course.
- **Ce que le fragment exécute.** WC5.1 corrigé C48 donnait cette course comme prédite par l'analyse, non vérifiée par l'exécution d'un modèle. G18 l'exécute dans le fragment d'événements. Le fragment ne modélise aucune séquence de libération (hypothèse 3) : il ne tranche donc pas entre la forme C++20 de C48 et celle de `rc11.cat`. Il établit seulement que, sans séquence de libération, ce programme a une course.

Rien n'est corrigé.

## Ce qui n'est pas couvert

- Les valeurs de la feuille ordinaire, une seconde unité atomique, plusieurs feuilles.
- Les séquences de libération, prolongées par un RMW ou par une écriture du même thread.
- Les contraintes globales de `seq_cst`.
- No-thin-air : le fragment ne dit rien de l'acyclicité de `po ∪ rf`, et aucun témoin de *load buffering* n'est construit.
- Toute correspondance avec la machine d'autorités et les traces existantes (couche R).
- Les barrières, `consume`, et les accès des autres opérations (`store`, `transfer`, `issue`, …).

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat.** 1956 théorèmes, dont 1348 non internes, contre 1801 (1275) avant cette passe. Aucun axiome hors `{propext, Quot.sound}`.
- **Modules nouveaux**, théorèmes (non internes) :
  - `EventModel.Closure` : 26 (16) ;
  - `EventModel.Graph` : 103 (31) ;
  - `EventModel.Lemmas` : 7 (7) ;
  - `EventModel.Witness` : 19 (19).
- **Build.** `lake build` réussit (97 jobs), sans avertissement.
- **Contrôles.**
  - Le `grep` d'`AGENTS.md` est vide.
  - Aucun `noncomputable`.
  - `set_option autoImplicit false` dans les quatre modules nouveaux.
  - Aucun fichier protégé n'est touché : `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md`, `formal/Ern/MemoryModel/`.
