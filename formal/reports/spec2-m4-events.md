# Spec 2, jalon 4 — graphe d'événements abstrait et ordre de passation

Formalisation exploratoire, branche `formal/spec2-m4`, jamais mergée. Sources lues : les briefs « graphe d'événements abstrait et ordre de passation » et « arête stricte du mutex », `ERN_Concurrency_Model_WC5.1.md` (C1–C8, C12, C15–C18, C21, C22, C26–C33, C43–C52), `corpus-spec2-m3.md` v8 (§ 2 bis, § 2 septies) et v9 (§ 2 octies), Spec 1 §47 et §80. Les numéros de ligne sont ceux de `c049ed7` pour la première passe, et de `cdfc947` pour la section « Arête stricte du mutex » ; les modules de la première passe n'ont pas changé entre les deux.

## Hypothèse du modèle

L'arête de synchronisation du mutex est prise sous sa forme abstraite : d'un `unlock(e)` vers le premier `acquire(e)` réussi qui le suit dans l'ordre de la trace. WC5.1 C48 demande que l'`acquire` lise directement (`rf`) la publication de l'`unlock`. Que le protocole concret du contrôleur réalise cette arête relève d'`OB-C05`. Ce n'est pas prouvé ici.

**Arête stricte.** Cette forme abstraite ordonne aussi deux sections critiques que rien n'ordonne, quand un `resetLock(e)` ou un `transfer` du mutex intervient sur le contrôleur entre les deux pas (W-RL, W-TR). Le graphe strict, ajouté à côté, ne garde l'arête que si aucun `resetLock(e)` n'est entre les deux pas, et si le contrôleur de `e` (`ControlOf`, WC5.1 C21 point 3) désigne la même feuille dans tous les états de l'issue de l'`unlock` à l'entrée de l'`acquire`. Ces deux conditions ne suffisent pas à établir la lecture directe de C48 : elles écartent les deux interventions du corpus v9, sans classer les autres pas qui pourraient toucher le contrôleur (hors de portée du brief).

Le graphe ne contient ni valeur, ni `rf`, ni `mo`, ni atomique, ni ordre mémoire, ni réalisation physique.

## Résultats

| Tâche | Attendu | Obtenu | Théorème |
|---|---|---|---|
| 1 | `hb` croît en position, donc est irréflexif | prouvé | `hb_pos` (`Events:361`), `hb_irrefl` (`Events:368`) |
| 1 | `hb` décidable sur une exécution finie | prouvé | `hb_iff_reach` (`Events:420`), instance (`Events:426`) |
| 2 | W-HO, W-HO′, W-HO″ : paire exclusive, sans `hb`, qui viole `HandoffOrdered` | obtenu, les trois | `Corpus/HandoffEvents` (§ Tâche 2) |
| 2 | W-HO″ : le `join(c1)` réussi est entre les deux écritures | obtenu | `W_HO3_join_between` (`HandoffEvents:136`) |
| 3 | W-HO-J, W-HO″-J : verdicts `ok`, `EncapsulatedTrace5R` depuis l'état initial | obtenu | `W_HOJ_ok`, `W_HOJ_trace`, `W_HO3J_ok`, `W_HO3J_trace` |
| 3 | W-HO-J, W-HO″-J, `lc_trace` : paire ordonnée par `hb`, `HandoffOrdered` | obtenu, les trois, et `HandoffOrdered` sur toute la trace | `W_HOJ_ordered`, `W_HO3J_ordered`, `lc_ordered`, `*_handoffOrdered` |
| 4 | `lossStep_own` | prouvé | `EventsCompose:94` |
| 4 | `handoffOrdered_no_race` | prouvé ; hypothèse satisfaite sur trois traces | `EventsCompose:201`, `*_noRace` |
| 5 | `spawn_orders` | prouvé | `EventsProtocols:22` |
| 5 | `join_orders` | prouvé | `EventsProtocols:137` |
| 5 | `lock_orders` | prouvé, sous l'hypothèse de reddition des prises intermédiaires | `EventsProtocols:179`, `lock_orders_holder` (`:214`) |

Aucun fait attendu du corpus v8 n'a été démenti par le modèle.

## Commits

| Commit | Tâche |
|---|---|
| `3a5699a` | 1 : `Events.lean` |
| `3df7237` | 2 : `Corpus/HandoffEvents.lean`, W-HO, W-HO′, W-HO″ |
| `8b5f961` | 3 : W-HO-J, W-HO″-J, `lc_trace` |
| `e6b2c4e` | 4 : `EventsCompose.lean` |
| `2f24b97` | 5 : `EventsProtocols.lean` |
| `db706b7` | rapport |
| `c049ed7` | `HandoffOrdered` et `¬ Race` sur trois traces entières ; citations de WC5.1 alignées sur les clauses lues ; docstrings manquantes |

## Définitions

Toutes sont dans `Events.lean`. Aucune définition existante n'est modifiée.

- **Exécution.** Des étiquettes `lbls` et des états nommés `σ`, comme `Run5C`. `Run5R` (`:24`) est `Run5C` avec `Encap5R`. `run5R_imp` (`:29`) l'inclut dans `Run5C` ; `run5R_trace` (`:34`) en tire une `EncapsulatedTrace5R`. `Steps5R` (`:45`) donne une exécution par la liste explicite de ses états, pour que `decide` calcule sur les vrais états.
- **Événements** (`Ev`, `:236`). `step i` pour le pas `i`, de contexte `Label.ctx`. `start i` pour le marqueur `start(c)` du contexte créé par le pas `i`, quand ce pas est un `spawn` ou un `spawnVal`. Le contexte créé est `created σ i = |C|` dans l'état `σ i` (`:293`). WC5.1 C4 (point 2) demande une identité fraîche ; `|C|` est la représentation du modèle (`spawnEff`).
- **Positions** (`Ev.pos`, `:242`). `step i` est en `2i`, `start i` en `2i + 1`, juste après son `spawn`.
- **`po`** (`PO`, `:298`). Deux pas du même contexte, dans l'ordre de la trace. `start(c)` précède tous les pas de `c`.
- **`sw`** (`SW`, `:314`). Du `spawn` ou `spawnVal` qui crée `c` vers `start(c)`. De `terminate(c)` vers tout `join` de `c` qui le suit. D'`unlock(e)` vers le premier `acquire(e)` qui le suit.
- **`hb`** (`HB`, `:337`). La clôture transitive `Relation.TransGen` de `po ∪ sw`.
- **Paire exclusive** (`ExclPair`, `:434`). `i < j`, contextes distincts, les deux pas accèdent à `l` (`Label.Access`), l'un au moins exige `Modify`.
- **`Race`** (`:441`). Une paire exclusive sans `hb (step i) (step j)`.
- **Pas de perte** (`lossStep`, `:461`). Le premier `k > i` de la trace à l'issue duquel `cap5` du contexte de `i` sur `l` est compatible avec le mode du pas `j` (`CapCompat`, `:453`). `none` s'il n'y en a pas.
- **`HandoffOrdered`.** `HandoffOrderedAt` (`:470`) : `∃ r, lossStep … = some r ∧ hb (step r) (step j)`. `HandoffOrdered` (`:490`) : cette propriété pour toute paire exclusive.

### Écarts au brief

1. **`po` depuis `start(c)` porte la clause `i < j`.** Le brief dit « `start(c)` précède tous les pas de `c` », sans condition d'ordre. Sur toute trace de pas `ok`, les deux formes coïncident (`po_start_iff`, `:513`). La raison : le contexte créé a l'identité `|C|`, seul un contexte vivant fait un pas, et `C` ne raccourcit jamais (`step_after_create`, `:498`). Avec la clause, `hb_pos` et la procédure de décision ne demandent aucune hypothèse de trace.
2. **Les marqueurs `start` sont indexés par la position du `spawn`, pas par le contexte.** Chaque `spawn` crée un seul contexte, et l'identité de ce contexte se lit dans l'état. Le graphe dépend donc de `σ`, à travers `created`.
3. **`complete(c)` n'est pas un événement séparé.** WC5.1 C28 fait partir l'arête vers `join` d'un marqueur `complete(c)` émis après le dernier événement de `c`. Le brief la fait partir du pas `terminate(c)`, et c'est ce qui est encodé. Le pas `terminate(c)` est le dernier pas de `c` (`done_iff`, `EventsProtocols:86`), donc il occupe la place de `complete(c)`.
4. **« Réussi » est automatique.** Tout pas d'une trace est un pas `ok` (`LStep`), donc tout `join` et tout `acquire` d'une trace est réussi.
5. **L'entrée `e` est l'indice du registre.** `newMutex` ajoute en fin de liste ; `acquire`, `unlock` et `resetLock` modifient en place. L'indice d'une entrée est donc stable. Écart accepté ; c'est maintenant prouvé (`reg_stable`, `RegIndex:64`, § Arête stricte du mutex, tâche 6).
6. **Une seule direction de `hb` dans `Race`.** C33 demande l'absence de `hb` dans les deux sens. Comme `hb` croît en position et `i < j`, `hb (step j) (step i)` est toujours faux ; seule `hb (step i) (step j)` est testée.
7. **Le pas de perte est cherché dans toute la trace, pas seulement avant `j`.** S'il se trouvait après `j`, `hb (step r) (step j)` serait faux. Le borner par `j` rendrait `r < j` vrai par construction dans `lossStep_own`.
8. **Un marqueur absent est un échec.** `HandoffOrderedAt` est existentiel : sans pas de perte, la paire ne satisfait pas `HandoffOrdered` (WC5.1 C46 : un marqueur manquant n'autorise pas à en supposer un).

## Tâche 1 — le graphe

- **Attendu.** `hb` ne relie que des événements en position croissante, donc il est irréflexif.
- **Obtenu.** Chaque arête de `po ∪ sw` va vers une position plus grande, dans la trace (`edge_pos`, `:348`). Par induction, `hb` aussi (`hb_pos`), d'où `hb_irrefl`.
- **Décision.** `reachList` (`:376`) calcule l'accessibilité en une passe par position croissante. `reachList_spec` (`:390`) montre qu'elle calcule la clôture transitive dès que les arêtes croissent en position. La récursion est structurelle, donc `decide` la réduit dans le noyau.
- **Cycle de vie des contextes.** Un lemme du modèle sert aux tâches 1 et 5 : tout pas `ok` est fait par un contexte vivant, et change la liste des états de cycle de vie par `Label.lifeEff` (`lstep_lifes`, `:150`). `spawn` et `spawnVal` ajoutent un contexte vivant ; `terminate c` complète `c` ; les autres pas la gardent.
- **Sans registre.** `encap5R_nil` (`:73`) : sans entrée enregistrée, tout pas `ok` satisfait `Encap5R`. Il sert aux traces sans mutex des tâches 2 et 3.

## Tâche 2 — témoins sans synchronisation

Les traces et les verdicts sont ceux de `Corpus/Handoff.lean`, avec leurs états nommés. Chacune est une `Run5R` depuis l'état initial (`W_HO_run` `:41`, `W_HO2_run` `:80`, `W_HO3_run` `:120`).

| Témoin | Paire | Attendu (corpus v8 § 2 septies) | Obtenu | Théorèmes |
|---|---|---|---|---|
| W-HO | écriture de `c1` (pas 2), écriture de `c0` (pas 4), feuilles `1` et `2` | pas de `hb` ; viole C46 | obtenu | `W_HO_excl` `:49`, `W_HO_noHb` `:55`, `W_HO_unordered` `:59` |
| W-HO′ | écriture de `c0` via `b` (pas 3), écriture de `c1` via `a` (pas 5) | pas de `hb` ; viole C46 | obtenu | `W_HO2_excl` `:88`, `W_HO2_noHb` `:95`, `W_HO2_unordered` `:98` |
| W-HO″ | écriture de `c2` (pas 4), écriture de `c0` (pas 9) | pas de `hb` malgré le `join(c1)` ; viole C46 | obtenu | `W_HO3_excl` `:130`, `W_HO3_noHb` `:143`, `W_HO3_unordered` `:146` |
| W-HO″ | `join(c1)` réussi (pas 8) | entre les deux écritures | obtenu | `W_HO3_join_between` `:136` |

`W_HO_unordered`, `W_HO2_unordered` et `W_HO3_unordered` donnent aussi `¬ HandoffOrdered` et `Race` pour la trace entière.

Clauses : WC5.1 C32 (une `release` d'O3 ne crée aucune arête `sw`) ; C46 ; C47 (un `join` n'ordonne que le contexte dont il observe la fin).

## Tâche 3 — jumeaux synchronisés

Verdicts d'autorité par `decide`, tous `ok` comme attendu (O10.1, O3, WC5.1 C7, C8) :

- **W-HO-J** (`W_HOJ_ok`, `:161`) : `c1 : terminate`, `c0 : join(c1)`, `c0 : write3(X)`. Les autres pas viennent de W-HO.
- **W-HO″-J** (`W_HO3J_ok`, `:221`) : `c2 : terminate`, `c1 : join(c2)`, `c1 : release(a)`, `c1 : terminate`, `c0 : join(c1)`, `c0 : write3(X)`. Les autres pas viennent de W-HO″.

Chaque jumeau est une `EncapsulatedTrace5R` depuis l'état initial (`W_HOJ_trace` `:189`, `W_HO3J_trace` `:257`). `lc_trace` est rejouée avec ses états nommés (`lc_run`, `:291`), avec les preuves d'`Encap5R` de `lc_trace5R`.

| Trace | Paire | Chemin `hb` attendu | Obtenu | Théorème |
|---|---|---|---|---|
| W-HO-J | écriture de `c1` (2), écriture de `c0` (6) | 2 →`po` `terminate(c1)` (4) →`sw` `join(c1)` (5) →`po` 6 | chemin, `hb`, `HandoffOrdered` sur les deux feuilles | `W_HOJ_ordered` `:201` |
| W-HO″-J | écriture de `c2` (4), écriture de `c0` (11) | 4 →`po` 6 →`sw` 7 →`po` 9 →`sw` 10 →`po` 11 | chemin, `hb`, `HandoffOrdered` | `W_HO3J_ordered` `:270` |
| `lc_trace` | lecture de `c1` (8), écriture de `c0` (11) | 8 →`po` `unlock(e)` (9) →`sw` `acquire(e)` (10) →`po` 11 | chemin, `hb`, `HandoffOrdered` | `lc_ordered` `:323` |

Chaque théorème énonce séparément les arêtes du chemin du corpus.

Les seuls accès de chaque trace sont les deux pas de la paire. `HandoffOrdered` tient donc sur toute la trace : `W_HOJ_handoffOrdered` (`:338`), `W_HO3J_handoffOrdered` (`:357`), `lc_handoffOrdered` (`:378`).

## Tâche 4 — théorème de composition (C52, feuilles ordinaires)

Les hypothèses sont celles de `handoff_loss_exists_C`, rien de plus : `DDSound k`, `StaticsOK statics`, `σ 0` initial, `Run5C k L σ lbls`. Le cas `Run5R` s'en déduit par `run5R_imp`.

- **`lossStep_own`** (`EventsCompose:94`). **Prouvé.** Pour toute paire exclusive, `lossStep = some r` avec `i < r < j`, et `r` est un pas du contexte de `i`. Ce n'est pas un corollaire de `handoff_loss_exists_C` : le pas qui y fait baisser `cap5` n'est pas forcément celui qui franchit le seuil de compatibilité. La preuve refait l'argument en quatre temps :
  1. Après le pas `i`, `cap5` est incompatible : `access_cap5` en `i`, puis l'invariance de `cap5` par un pas d'accès (`inert_effect`, `cap5_same`).
  2. Avant le pas `j`, il est compatible : `access_cap5` en `j`, puis `cap5_compat`.
  3. Donc `j - 1` est candidat, et le premier candidat `r` vérifie `i < r < j`.
  4. Au pas `r`, `capRank` baisse strictement ; `cap5_drop_own` donne son contexte.
- **`handoffOrdered_no_race`** (`EventsCompose:201`). **Prouvé.** `HandoffOrdered` entraîne `¬ Race`. Par `lossStep_own`, `po (step i) (step r)` ; `HandoffOrdered` donne `hb (step r) (step j)` ; par transitivité, `hb (step i) (step j)`.

La preuve est un argument de composition (WC5.1 C46, C52) : elle suppose `HandoffOrdered`, elle ne le prouve pas.

**Non-vacuité.** L'hypothèse `HandoffOrdered` est satisfaite par trois traces réelles qui ont une paire exclusive. Le théorème s'y applique et donne `¬ Race` : `W_HOJ_noRace` (`HandoffEvents:351`), `W_HO3J_noRace` (`:372`), `lc_noRace` (`:392`).

## Tâche 5 — protocoles de référence (C47, C48)

- **`spawn_orders`** (`EventsProtocols:22`). **Prouvé.** Tout pas `p ≤ s` du créateur est `hb`-avant tout pas de `c`, où `s` est le `spawn` ou `spawnVal` qui crée `c`. Le pas de création lui-même est inclus.
  - Seule hypothèse : les pas de la trace sont des pas `ok`. Aucune encapsulation n'est requise.
  - Le fait que les pas de `c` suivent `s` n'est pas supposé : il est déduit (`step_after_create`).
- **`join_orders`** (`EventsProtocols:137`). **Prouvé.** Tout pas d'un contexte `d` est `hb`-avant tout `join` réussi de `d`.
  - Hypothèses : pas `ok`, et aucun contexte complété dans le premier état. Les états initiaux de Spec 1 §47 satisfont la seconde.
  - Aucune hypothèse d'ordre entre le pas et le `join` : la trace place chaque pas de `d` avant son `terminate`, et ce `terminate` avant le `join` (`done_iff`, `:86`).
- **`lock_orders`** (`EventsProtocols:179`). **Prouvé.** Pour une entrée `e`, un `unlock(e)` en `u` est `hb`-avant tout `acquire(e)` en `a > u`, à une condition. Chaque `acquire(e)` intermédiaire en `p` doit être suivi, avant `a`, d'un `unlock(e)` en `p'` avec `hb (step p) (step p')`.
  - L'énoncé ne lit que les étiquettes.
  - `lock_orders_holder` (`:214`) est la forme du brief : le `unlock(e)` est fait par le contexte qui a pris le verrou. Le grant est tenu par la frame courante de ce contexte (WC5.1 C15, effet ; C16), et `unlock` le libère sous O3 (C17 point 2).
  - La forme en `hb` est plus générale. Raisonnement non formalisé : elle admettrait un `unlock` fait par un autre contexte, à condition qu'il soit `hb`-après l'`acquire`. Aucun cas de ce genre n'est testé : rien ne montre qu'un grant puisse être cédé par `spawn` puis rendu par le fils.

**Hors de `lock_orders`.**

- **Grant abandonné puis `resetLock`.** Quand une prise intermédiaire est abandonnée, par sortie de frame sans `unlock`, puis récupérée par `resetLock` (WC5.1 C18, C49), aucune arête `sw` ne part de la section critique abandonnée. L'hypothèse du lemme exclut ce cas. WC5.1 C49 précise que la récupération ne remplace pas une arête `acquire`/`release` manquante.
- **`unlock` non ordonné.** Un `unlock(e)` sans `hb` depuis l'`acquire` correspondant est aussi exclu.

## Arête stricte du mutex

Brief « arête stricte du mutex », corpus v9 § 2 octies, WC5.1 C18, C21, C32, C45, C46, C48, C49. Le défaut corrigé est dans la définition du brief précédent, pas dans son encodage : il est conservé comme contre-exemple. Aucune définition existante n'est modifiée ; `SW`, `HB`, `Race`, `HandoffOrdered` et leurs théorèmes restent tels quels.

### Définitions ajoutées

Toutes dans `EventsStrict.lean`.

- **`Label.resetLockOf`** (`:23`) : l'entrée réinitialisée par un pas `resetLock`.
- **`ctlAt σ L i k`** (`:29`) : le contrôleur de l'entrée `i` dans l'état `σ k`, tel que `ControlOf` le calcule ; `none` s'il n'y a pas d'entrée `i` ou pas de contrôleur.
- **`MutexGap σ L lbls e u a`** (`:37`) : les deux conditions de l'arête stricte d'un `unlock(e)` en `u` vers un `acquire(e)` en `a`. Aucun `resetLock(e)` en `k` avec `u < k < a` ; `ctlAt` est défini en `σ (u + 1)` et lui est égal dans tout état `σ k`, `u + 1 ≤ k ≤ a`.
- **`SWS`** (`:51`) : les arêtes de `spawn` et de `join`, recopiées de `SW` sans changement, plus l'arête du mutex de `SW` restreinte par `MutexGap`. **`EdgeS`** (`:68`) : `PO` ou `SWS`. **`HBS`** (`:78`) : clôture transitive.
- **`RaceS`** (`:83`), **`HandoffOrderedAtS`** (`:88`), **`HandoffOrderedS`** (`:93`) : les définitions de la passe précédente lues sur `HBS`. `ExclPair` et `lossStep` sont inchangés.

**Écarts et choix de représentation.**

1. **Un graphe recopié plutôt que paramétré.** Un graphe paramétré par sa relation `sw` aurait demandé de redéfinir `SW` et `HB`, ce que le brief interdit. `SWS` recopie donc les clauses de `spawn` et de `join` mot pour mot ; `sws_sw` (`:100`) vérifie l'inclusion.
2. **« Désigne la même feuille ».** Lu comme : le contrôleur est défini à l'issue de l'`unlock` et vaut cette feuille dans chaque état jusqu'à l'entrée de l'`acquire`. Un contrôleur indéfini en `σ (u + 1)` coupe l'arête.
3. **Le graphe strict dépend de la disposition du mutex `L`**, à travers `ControlOf`. `spawn_ordersS` et `join_ordersS` laissent la disposition du graphe libre, distincte de celle des pas : c'est plus général que « même énoncé », puisque les arêtes de `spawn` et de `join` ne lisent pas `L`.

### Tâche 1 — témoins au niveau des autorités (`Corpus/MutexEdge.lean`)

Chaque trace part de l'état initial de `mxst`, qui contient déjà `M′ = {slot′, lock′}` `Uninit`. Le préfixe P est commun (`prefix_steps`, `:44`).

| Trace | Attendu (corpus v9 § 2 octies) | Obtenu | Théorèmes |
|---|---|---|---|
| P | `acquire`, `write3(T)`, `unlock`, `release(o1)` : `ok` | `ok` ; après P, `root_M` a `Modify` effectif sur `slot` et `lock`, `ControlOf(e) = lock` | `P_ok` `:27`, `P_facts` `:33` |
| W-RL₀ | `acquire(e)`, `write3(T)` : `ok` | `ok` ; `Run5R` | `W_RL0_ok` `:69`, `W_RL0_run` `:86` |
| W-RL | `resetLock(e)`, `acquire(e)`, `write3(T)` : `ok` | `ok` ; `Run5R` | `W_RL_ok` `:98`, `W_RL_run` `:113` |
| W-RL-J | `terminate`, `join`, puis W-RL : `ok` | `ok` ; `Run5R` | `W_RLJ_ok` `:133`, `W_RLJ_run` `:152` |
| W-TR | `transfer(M, M′)`, `acquire(e)`, `write3(T)` : `ok` | `ok`, et `ControlOf(e) = lock′` après le transfert ; `Run5R` | `W_TR_ok` `:177`, `W_TR_run` `:193` |
| W-TR-J | `terminate`, `join`, puis W-TR : `ok` | `ok` ; `Run5R` | `W_TRJ_ok` `:216`, `W_TRJ_run` `:235` |

**Aucun pas attendu `ok` n'est refusé.**

- **`resetLock` avec un grant à `none`.** Le modèle l'accepte : `ResetLockOk` ne lit pas le grant enregistré, comme le dit le corpus.
- **`Encap5R` admet `resetLock`, mais sans rien vérifier.** Aucun de ses conjoints ne contraint cette étiquette : `Encap`, `ChainExcl` et `CtlExcl` la laissent à `True`, et `PlaceExcl` aussi, parmi les étiquettes laissées à `True` lors de la passe `PlaceExcl`. C'est plus permissif que l'exception de C22.6, qui exige que le droit sur `slot` ait une chaîne de détention sans le `guarded` d'une autre entrée vivante (`OB-C28`). Ici il n'y a qu'une entrée, donc l'exception l'admettrait aussi. Raisonnement non formalisé : l'exception n'est pas encodée.
- **Restriction utilisée.** Les traces sont des `Run5R`, la plus forte restriction encodée ; aucun affaiblissement n'a été nécessaire.

### Tâche 2 — le défaut, sur le graphe existant

| Trace | Attendu | Obtenu | Théorème |
|---|---|---|---|
| W-RL | paire exclusive ; ordonnée par `hb`, l'arête du mutex passant par-dessus le `resetLock` ; `HandoffOrderedAt` | paire (6, 11, `T`) exclusive ; chemin 6 →`po` 7 →`sw` 10 →`po` 11 ; `HB` ; `HandoffOrderedAt` | `W_RL_excl` `:253`, `W_RL_defect` `:262` |
| W-TR | idem, alors que le contrôleur a changé de feuille au pas 9 | même chemin, `HB`, `HandoffOrderedAt` | `W_TR_excl` `:269`, `W_TR_defect` `:277` |

Ces théorèmes restent comme contre-exemple de l'arête abstraite (WC5.1 C45, dernier alinéa).

### Tâche 3 — le graphe strict

Tous **prouvés** (`EventsStrict.lean`) :

- **Inclusion.**
  - `sws_sw` (`:100`) et `edgeS_edge` (`:117`) : toute arête stricte est une arête du graphe ;
  - `hbS_hb` (`:122`) : `HBS` entraîne `HB` ;
  - `race_raceS` (`:129`) : `Race` entraîne `RaceS` ;
  - `handoffOrderedAtS_imp` (`:135`) et `handoffOrderedS_imp` (`:142`) : le strict entraîne l'existant.
- **Ordre.** `hbS_pos` (`:149`) : `HBS` croît en position ; `hbS_irrefl` (`:154`) : il est irréflexif.
- **Décision.** `hbS_iff_reach` (`:159`) réutilise `reachList_spec` de la première passe ; l'instance suit, ainsi que celle de `HandoffOrderedAtS` (`handoffOrderedAtS_iff`, `:172`).

### Tâche 4 — faits sur le graphe strict (`Corpus/MutexEdgeStrict.lean`)

Faits par `decide`. Pour les énoncés sur toute la trace, les lemmes `exclPair_of_two` (`:24`), `handoffOrderedS_of_two` (`:38`) et `not_raceS_of_two` (`:49`) ramènent la trace à sa seule paire, ses seuls accès étant les deux écritures.

| Trace | Attendu (corpus v9 § 2 octies) | Obtenu | Théorème |
|---|---|---|---|
| W-RL | aucun chemin `hb` strict ; viole C46 | l'arête 7 → 10 est coupée ; pas de `HBS` (6, 11) ; `¬ HandoffOrderedAtS`, `¬ HandoffOrderedS`, `RaceS` | `W_RL_strict` `:64` |
| W-TR | aucun chemin `hb` strict ; viole C46 | arête 7 → 10 coupée, `ctlAt` vaut `lock` (2) en `σ 8` et `lock′` (6) en `σ 10` ; pas de `HBS` ; `¬ HandoffOrderedAtS`, `¬ HandoffOrderedS`, `RaceS` | `W_TR_strict` `:75` |
| W-RL₀ | 6 →`po` `unlock` →`sw` `acquire` →`po` écriture ; C46 | chemin 6 → 7 → 9 → 10, arête par arête ; `HBS` ; `HandoffOrderedS` sur toute la trace ; `¬ RaceS` | `W_RL0_strict` `:89` |
| W-RL-J | 6 →`po` `terminate(c1)` →`sw` `join(c1)` →`po` écriture ; C46 | chemin 6 → 9 → 10 → 13 ; `HBS` ; `HandoffOrderedS` ; `¬ RaceS` | `W_RLJ_strict` `:106` |
| W-TR-J | idem par le `join` ; C46 | chemin 6 → 9 → 10 → 13 ; `HBS` ; `HandoffOrderedS` ; `¬ RaceS` | `W_TRJ_strict` `:123` |
| W-HO, W-HO′, W-HO″ | gardent leurs faits | pas de `HBS` ; `¬ HandoffOrderedAtS` ; `RaceS` ; `¬ HandoffOrderedS`, par l'inclusion | `W_HO_all_strict` `:141`, `W_HO_all_raceS` `:152` |
| W-HO-J, W-HO″-J | gardent leur chemin, `HandoffOrderedS`, `¬ RaceS` | obtenu | `W_HOJ_strict` `:161`, `W_HO3J_strict` `:176` |
| `lc_trace` | idem ; l'arête du mutex 9 → 10 est stricte | obtenu | `lc_strict` `:194` |

`¬ RaceS` sur les traces entières est montré directement, sans `handoffOrdered_no_raceS`, pour que la tâche 4 ne dépende pas de la tâche 5.

### Tâche 5 — théorèmes sur le graphe strict (`EventsStrictProtocols.lean`)

Tous **prouvés**.

- **`handoffOrdered_no_raceS`** (`:24`) : mêmes hypothèses que `handoffOrdered_no_race`.
- **`spawn_ordersS`** (`:42`) et **`join_ordersS`** (`:61`) : mêmes énoncés et hypothèses, la disposition du graphe étant libre (choix 3).
- **`lock_ordersS`** (`:149`) : l'énoncé de `lock_orders` sur `HBS`, avec deux hypothèses de plus sur l'intervalle de `u` à `a`. Aucun `resetLock(e)` en un pas strictement entre `u` et `a` ; il existe une feuille `ctl` telle que `ctlAt` vaut `some ctl` dans chaque état `σ k`, `u + 1 ≤ k ≤ a`.
- **Forme plus fine, `lock_ordersS_gaps`** (`:105`). `MutexGap` n'y est demandé qu'entre chaque `unlock(e)` (en un pas `u' ≥ u`) et le premier `acquire(e)` qui le suit, jusqu'à `a`. Un `resetLock(e)` ou un changement de contrôleur à l'intérieur d'une section critique intermédiaire n'est donc pas exclu. `lock_ordersS` s'en déduit.

Comme pour `lock_orders`, l'abandon d'un grant suivi d'un `resetLock` est hors de ces énoncés (WC5.1 C49) : le `resetLock` coupe l'arête, et rien ne la remplace.

### Tâche 6 — stabilité de l'indice d'une entrée (`RegIndex.lean`)

Tous **prouvés**.

- **`reg_set_guarded`** (`:19`) : réécrire une entrée en place, en gardant son `guarded`, garde la longueur du registre et le `guarded` à chaque indice.
- **`lstep_reg`** (`:32`) : un pas `ok`, quel qu'il soit, ne raccourcit pas le registre et garde le `guarded` à chaque indice existant.
- **`reg_stable`** (`:64`) : le long de pas `ok`, de toute position `a` à toute position `b ≥ a`, le registre ne raccourcit pas, et l'entrée de chaque indice existant en `a` garde la même identité `guarded`.
- **`reg_stable_run5C`** (`:81`) : la même chose le long de toute `Run5C`.

La forme prouvée est plus forte que le brief : elle ne demande aucune encapsulation, seulement que les pas soient `ok`.

### Hors de portée

La réalisation physique du contrôleur (`OB-C05`), `rf`, `mo`, les atomiques ; les accès engendrés par les autres opérations (`OB-C20`) ; la couverture complète de C22.6, dont l'exception de `resetLock` (`OB-C28`). Aucune classification des pas qui changent `ControlOf(e)` n'est faite.

### Commits

| Commit | Tâche |
|---|---|
| `358ce63` | 1 : `Corpus/MutexEdge.lean`, P et les cinq témoins |
| `4c15888` | 2 : W-RL et W-TR sur le graphe existant |
| `c48e835` | 3 : `EventsStrict.lean` |
| `fe5697d` | 4 : `Corpus/MutexEdgeStrict.lean` |
| `1619fd4` | 5 : `EventsStrictProtocols.lean` |
| `cdfc947` | 6 : `RegIndex.lean` |

## Ce qui n'est pas couvert

- Valeurs, `rf`, `mo` (WC5.1 C31), atomiques et ordres mémoire (partie IX de WC5.1, non relue ici).
- L'ordre interne des pas composés et les marqueurs internes, qu'ils soient de gain, de perte, de `spawn` ou de `complete(c)` (WC5.1 C28 points 1–3). Un pas est un seul événement.
- Les accès engendrés par les autres opérations : `store`, `transfer`, `issue`, `alloc`, phases de `spawnVal`, `newMutex`, métadonnées (WC5.1 C27, C29, `OB-C20`). `Race` et `ExclPair` ne regardent que `read3`, `write3` et `writeShared`.
- Les paires sans membre en `Modify` (`read3` contre `writeShared`), hors de C44.
- La réalisation de l'arête du mutex par `rf` (`OB-C05`), `LockOrder` concret (C49), `resetLock`. L'arête stricte écarte le `resetLock` et le déplacement du contrôleur, sans établir la lecture directe.
- La preuve de `HandoffOrdered` pour une trace quelconque : il n'est prouvé que sur trois traces, W-HO-J, W-HO″-J et `lc_trace` ; `HandoffOrderedS`, sur ces trois traces et sur W-RL₀, W-RL-J et W-TR-J.

## Problèmes de spécification

Aucun bloquant. Une observation :

- **WC5.1 C28 et C32 point 3 contre le brief.** WC5.1 fait partir l'arête vers `join` d'un marqueur `complete(c)` distinct. Le brief la fait partir du pas `terminate(c)`. Dans ce modèle, les deux coïncident en position, puisque `terminate(c)` est le dernier pas de `c` (`done_iff`). Si une passe ultérieure modélise l'ordre interne des pas, il faudra fixer où se place `complete(c)` dans le pas `terminate`.

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat à `c049ed7`.** 1726 théorèmes, dont 1225 non internes, contre 1523 (1107) à `bbf1c0b`. Aucun axiome hors `{propext, Quot.sound}` : `lossStep_own`, `handoffOrdered_no_race`, `spawn_orders`, `join_orders`, `lock_orders` compris.
- **Modules nouveaux**, théorèmes (non internes) :
  - `Events` : 98 (51) ;
  - `Corpus.HandoffEvents` : 40 (34) ;
  - `EventsCompose` : 18 (8) ;
  - `EventsProtocols` : 47 (25).
- **`Classical.choice` évité.** Deux sources l'introduisaient pendant le développement : un `omega` fermant une conjonction, et `List.getElem?_modify`. Elles sont remplacées, par des `omega` sur chaque membre et par des preuves par récurrence (`lifes_modify`, `lifes_done`).
- **Après l'arête stricte, à `cdfc947`.** 1800 théorèmes, dont 1274 non internes. Aucun axiome hors `{propext, Quot.sound}`, les théorèmes des tâches 3, 5 et 6 compris. Modules nouveaux :
  - `EventsStrict` : 19 (10) ;
  - `EventsStrictProtocols` : 16 (5) ;
  - `RegIndex` : 7 (4) ;
  - `Corpus.MutexEdge` : 17 (17) ;
  - `Corpus.MutexEdgeStrict` : 15 (13).
- **Build.** `lake build` réussit (88 jobs à `c049ed7`, 93 à `cdfc947`), sans avertissement.
- **Contrôles.**
  - Le `grep` d'`AGENTS.md` est vide.
  - Aucun `noncomputable` dans les modules nouveaux.
  - Aucun fichier protégé n'est touché : `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md`, `formal/Ern/MemoryModel/`.
