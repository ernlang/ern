# Jalon 4, tranche 4 — passation abstraite étendue aux opérations composées

Branche `formal/spec2-m4`, à la suite du complément de la tranche 3 (`a234683`, rapport `spec2-m4-encap.md`, section « Complément »). Formalisation exploratoire, jamais mergée. Textes de référence : WC5.3 (remplace WC5.2 ; aucune règle de WC5.2 n'y change) et `corpus-spec2-m3.md` v15, § 2 quaterdecies. Aucun fichier de `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md` ni `formal/Ern/MemoryModel/` n'est modifié ; aucune définition ni aucun énoncé existant n'est modifié ou affaibli.

## Portée du résultat

- Les énoncés portent sur les pas abstraits et sur le graphe à un événement par pas. Ils ne disent pas quels accès physiques un pas composé engendre, ni dans quel ordre (`OB-C19`, `OB-C20`).
- « Toucher une feuille » est une notion du modèle. Elle n'étend pas le domaine normatif de C44 à C46, qui parle d'événements d'accès.
- Le critère d'exclusivité est le mode exigé par la clause (C44), pas le conflit par octets de C30.
- La passation ordonnée étendue est l'analogue abstrait de C46 ; elle n'est pas C46. Une course étendue est un fait sur le modèle, pas un verdict normatif. Dire qu'une paire étendue relève de C46 demande de justifier les événements physiques de ses deux pas, ce qui est hors de cette tranche. C27 prévoit des écritures pour `transfer`, `store`, les phases par valeur de `spawn` et `newMutex`, et dit qu'une sortie de frame abstraite ne crée, par ce seul effet, aucun accès physique.
- La conclusion est conditionnelle : ce n'est pas une preuve d'absence de course.

## Commits

| Commit | Contenu |
|---|---|
| `f1c05c5` | définitions (`HandoffExt`) et témoins de la tâche 1 (`HandoffExtWitness`) |
| `f6fd09a` | tâche 2 : classes, feuilles mortes, identités, corollaires (`HandoffExtClass`) ; témoin de la classe N |
| `fafc631` | tâche 3 et composition de la tâche 5 (`HandoffExtFrontier`) ; W-HT sans `Race` |
| `7c3040d` | tâche 5, balayage des 55 traces `RunFull` (`HandoffExtSweep`) |
| `f8362e2` | tâche 4 (`HandoffExtSame`) |
| `a028efd` | tâche 6 (`OBC28Check`) |
| `fe2101d` | première version de ce rapport |
| `212a0e6` | tâche 4 : réfutation de « `r = i ⇒ hb(i, j)` » par `unlock` ; balayage des traces de `HandoffExtSame` ; clause O7.2 du négatif de W-HX |
| commit qui suit `212a0e6` | ce rapport, mis à jour |

Sept modules nouveaux sous `formal/Ern/Concurrency/FullEncap/`, tous importés par `formal/Ern.lean`. Les numéros de ligne cités sont ceux de `212a0e6`.

## Définitions ajoutées

Toutes dans `HandoffExt.lean`, à côté des définitions existantes.

| Notion du brief | Définition | Ligne | Encodage |
|---|---|---|---|
| place créée | `Created st st' l` | 44 | `|P| ≤ l < |P'|` (§40 ; §71, §72 effets ; C4, C5 phase 1) |
| feuille créée et écrite | `CW st st' l` | 55 | créée, feuille après le pas, `Init` après le pas (§59 ; C5 effets) |
| toucher | `TouchL L st st' lbl l` | 68 | feuille existante dans `TouchesF`, ou feuille créée dans `TouchesF`, ou `CW` |
| feuille où la clause exige un mode | `HasReq st lbl l` | 85 | lu sur `CapReq` |
| mode exigé | `ReqMode k st lbl l m` | 106 | relation, fonctionnelle (`reqMode_unique`, 126) |
| classes D, C, E, N | `ClassD` 168, `ClassC` 171, `ClassE` 174, `ClassEm` 178, `ClassN` 183 | | prédicats, ordre de priorité D, C, E, N |
| toucher exclusif | `ExclTouch` | 211 | D, C, ou E avec `Modify` exigé |
| paire exclusive étendue | `ExtPair k L σ lbls i j l` | 225 | `i < j`, contextes distincts, deux touchers, l'un exclusif |
| compatibilité avec le toucher de `j` | `TouchCompat` | 242 | D : `o = none` ; E : `CapCompat o m` pour le mode exigé ; C, N : jamais |
| frontière | `FrontAt` 281, `IsFrontier` 297 | | premier `r ≥ i` de la trace (`r < |lbls|`) ; unique (`isFrontier_unique`, 308) |
| passation ordonnée étendue | `HandoffOrderedExtAt` 318, `…S` 323, `HandoffOrderedExt` 340, `…S` 345 | | la frontière existe et `hb(r, j)` (`HB` ou `HBS`) |
| course étendue | `RaceExt` 351, `RaceExtS` 356 | | paire étendue sans `hb(i, j)` |

### Choix d'encodage et écarts au brief

1. **Toucher lu sur les feuilles.** Pour `enterFrame`, `spawn`, `alloc` et le `spawn` par valeur, `TouchesF` contient toute identité `l ≥ |P|` (`st.1.P.length ≤ l`). Il contient donc toutes les feuilles créées, y compris les destinations du `spawn` par valeur, mais aussi des identités que le pas ne crée pas. `TouchL` ne retient que les feuilles existantes avant le pas et les feuilles créées par lui. Aucun prédicat à part n'est nécessaire pour les destinations ; la classe C est `CW`.
2. **« Écrite ».** Une feuille créée est écrite si elle est `Init` après le pas. C'est la lecture de « se lit dans l'état d'après le pas » : selon §59, une feuille ne devient `Init` que par une écriture permise ou un transfert, et C5 (effets) rend `Init` les feuilles de destination.
3. **Classes.** Ce sont des prédicats. L'ordre de priorité les rend disjointes : E exige `¬ Dying` ; C et E sont disjointes, l'une étant créée et l'autre existante. La classe E porte un mode par la relation `ReqMode` (`ClassEm`).
4. **`alloc`, fournisseur.** `CapReq` encode les deux branches de §71.2 feuille par feuille : `Allows Observe ∧ (Allows Modify ∨ K.SharedMutable l)`. Le mode exigé est donc `Observe` sur une feuille `SharedMutable` et `Modify` sur les autres. Le fournisseur n'est exclusif que dans le second cas. La branche effectivement utilisée par le pas n'est pas enregistrée : les deux peuvent valoir sur une feuille `SharedMutable`.
5. **Compatibilité.** `TouchCompat` lit le mode exigé universellement. C'est équivalent à la lecture existentielle, puisque ce mode est unique (`touchCompat_iff_of_classEm`, 254 ; `touchCompat_iff_of_classD`, 270). Ce choix permet de raisonner sans décider `K.SharedMutable`.
6. **Frontière.** `IsFrontier` est une relation (le premier `r`, unique). « `none` s'il n'y en a pas » est l'absence de tout `r`. La recherche porte sur toute la trace, sans borne par `j`.
7. **Hypothèse ajoutée, un seul énoncé.** `frontier_exists` porte l'instance `[DecidablePred k.SharedMutable]`. La construction du premier pas doit décider la compatibilité. Quand le toucher de `j` est le fournisseur d'un `alloc`, le mode exigé dépend de `K.SharedMutable`. Sans l'instance, il faudrait `Classical.choice`, exclu par la règle des axiomes. Aucun autre énoncé ne la porte : bornes, contexte propre, composition et inclusions n'en ont pas besoin. Tous les contrats des traces du dépôt ont cette instance.
8. **Forme par pas de la non-réutilisabilité.** `usable_back_step` prend `DDSound` en plus de `KInvCA`. Elle en a besoin pour l'état intermédiaire de `issue` et de `reset`, via `opStepC_preservesC`. La forme sur les traces, `unusable_run`, n'a que les quatre hypothèses admises.

## Tâche 1 — Témoins

Tous les attendus du corpus v15 sont obtenus. Aucun pas attendu `ok` n'est refusé par le noyau ni exclu par l'encapsulation complète. Les indices sont ceux de la trace Lean ; les pas « 1, 2, 3 » du corpus suivent la mise en place.

| Témoin | Attendu (corpus v15) | Obtenu | Clause | Théorème (`HandoffExtWitness`) |
|---|---|---|---|---|
| W-HT, mise en place et pas 1 à 3 | `ok`, admis | `ok` ; `RunFull` depuis l'état initial | O1, C4, O10.1, O3, O4 (§63.1–§63.9) | `W_HT_run` (64) |
| W-HT, pas 3 avant le pas 2 | `reject`, §63.1 | `reject` ; `effective root_X X = none` | §63.1, §43.3 | `W_HT_neg` (84) |
| W-HT-J | `ok`, admis | `ok` ; `RunFull` | C7, C8 | `W_HTJ_run` (106) |
| W-HS, mise en place et pas 1 à 3 | `ok`, admis | `ok` ; `RunFull` | O8 (§65.1–§65.5) | `W_HS_run` (191) |
| W-HS, pas 3 avant le pas 2 | `reject`, §65.2 | `reject` | §65.2, §43.3 | `W_HS_neg` (211) |
| W-HS-J | `ok`, admis | `ok` ; `RunFull` | C7, C8 | `W_HSJ_run` (232) |
| W-HX, mise en place de S1a et pas 1 à 3 | `ok`, admis ; `X` meurt | `ok` ; `X` inutilisable après ; `RunFull` | O7.1, O7.2, O7.4, C6 | `W_HX_run` (293) |
| W-HX, pas 3 avant le pas 2 | `reject`, O7.2 | `reject` ; `a` survivant sans origine survivante (`firstSurv … = none`) | O7.2, §73.4 | `W_HX_neg` (312) |
| W-HX-J | `ok`, admis | `ok` ; `RunFull` | C7, C8 | `W_HXJ_run` (334) |
| W-HT, W-HS, W-HX, graphe | `(1, 3, X)` exclusive étendue ; frontière = pas 2, de `c1` ; aucun `hb` ; course étendue ; pas de passation ordonnée étendue | idem (indices `(2,4)`, `(3,5)`, `(4,6)` ; frontière 3, 4, 5) ; W-HX : classe D au pas 3 | §67.1 ; §63.1 ; §65.2 ; §73 | `W_HT_graph` (124), `W_HS_graph` (255), `W_HX_graph` (353) |
| idem, jumeaux | même paire et même frontière ; ordonnée par `terminate`, `join` | idem : `po`, `sw`, `po`, `HBS`, passation ordonnée étendue | C32.3, C47 | `W_HTJ_graph` (133), `W_HSJ_graph` (265), `W_HXJ_graph` (363) |
| ces paires ne sont pas des `ExclPair` | — | non (le pas 3 n'est pas un accès) | — | `W_HT_notExcl` (140), conjonct de `W_HS_graph`, `W_HX_graph` |
| W-SV, pas 2 ; négatif | pas 2 `ok`, admis ; `read3(v)` `reject` (O9.1) | idem ; feuille `1` de `v` `Moved` ; `RunFull` | O10.1, C5 point 2 ; O9.1 | `W_SV_run` (393) |
| W-SV, les quatre faits (feuille `4` de `d`) | exclusive étendue ; frontière = pas 1 ; recherche `k > i` = pas 2, ni avant `j` ni de `c0` ; ordonnée par l'arête de création | idem ; classe C ; `cap5(c0, d) = none` après le pas 1 ; `lossStep = some 5` ; `SWS (pas 4) (start 4)` | C5, C32.2 | `W_SV_graph` (414) |
| W-SV, arête de création au genre `spawnVal` | à rapporter si absente | **présente** : `SWS` relie `step i` à `start i` quand `Label.creates`, vrai pour `spawnVal` (`Events.lean:266`) | C32.2 | `W_SV_graph` |
| W-NM | `MX₄` puis `c1 : acquire(e)` `ok` | `RunFull` (préfixe de W-RL₀) | C16 | `W_NM_run` (427) |
| W-NM, les trois faits | `(newMutex, acquire, lock)` exclusive étendue ; frontière = `derive` de l'étape 4 (Modify → Observe) ; ordonnée | idem (indices `(2,5)`, frontière 3 ; `cap5(c0, lock)` passe de `Modify` à `Observe`) | C13.11, C14.3, §43.4, C32.2 | `W_NM_graph` (437) |
| W-TR | `(unlock, transfer, lock)`, `(acquire, transfer, lock)` exclusives étendues ; frontière = `release(o1)` ; aucun `hb` | idem (indices `(7,9)`, `(5,9)` ; frontière 8) | C17.4, C14.3, §63.1 | `W_TR_graph` (456) |
| W-TR-J | même frontière ; ordonnées par le `join` | idem (indices `(7,11)`, `(5,11)`) | C47 | `W_TRJ_graph` (466) |
| W-CR | depuis `MX₃`, `read3(lock)` via `root_M` `ok` au noyau, exclu par C22.4 | idem. `MX₃` est atteint par une `RunFull` (préfixe de W-RL₀). `PremG` (C22.6), `Encap` et `ChainExcl` valent. Les deux encodages de C22.4 échouent : `CtlExcl` et `CtlRestrF`. | O9 ; C22.4 | `W_CR_excluded` (487) |
| W-CR, jumeau | avant `newMutex` : `ok`, admis | `RunFull` | O9 | `W_CR_twin` (511) |

Le pas exclu de W-CR est un verdict local : une trace qui le contient n'est pas une `RunFull`.

## Tâche 2 — Classes des touchers

### Table des 28 genres

Les feuilles touchées sont des feuilles de l'état d'avant (existantes) ou d'après (créées). « — » : `TouchesF` est vide sur les feuilles.

| Genre | D | C | E (mode exigé) | N |
|---|---|---|---|---|
| `derive`, `split`, `release`, `depend`, `pin`, `unpin` | — | — | — | — |
| `transfer` | — | — | feuilles de la source et de la destination (`Modify`, §63.1) | — |
| `enterFrame` | — | — | — | locaux frais, `Uninit` (§72) |
| `exitFrame` | feuilles qui meurent (§73) | — | — | — |
| `read3`, `writeShared` | — | — | feuilles lues ou écrites (`Observe`, §66.2, §68.2) | — |
| `write3` | — | — | feuilles écrites (`Modify`, §67.1) | — |
| `endUse` | stockage possédé qui meurt (§69 effet) | — | feuilles de `place`, qui reste utilisable (`Modify`, §69.1) | — |
| `free` | feuilles qui meurent, dont celles de `place` (§70.3) ; le mode exigé reste lisible dans `CapReq` | — | — | — |
| `alloc` | — | — | fournisseur (`Modify`, ou `Observe` sur une feuille `SharedMutable`, §71.2) ; propriétaire s'il est une feuille (`Modify`, §71.3) | feuilles fraîches, `Uninit` (§71) |
| `store` | — | — | cible (`Modify`, §65.2) | — |
| `spawn` | — | — | — | locaux de l'enfant, `Uninit` (C4) |
| `terminate` | feuilles qui meurent (C7) | — | — | — |
| `join`, `deriveSync` brut, `newArena`, `reset` | — | — | — | — |
| `newMutex` | — | — | contrôleur (`Modify`, C13.11) | — |
| `acquire`, `unlock`, `resetLock` | — | — | contrôleur (`Observe`, C14.3, C17.4, C18.4) | — |
| `spawnVal` | — | destinations, `Init` après la phase de transfert (C5 effets) | feuilles des sources (`Modify`, C5 point additionnel 1) | autres locaux de l'enfant, `Uninit` (C5 phase 1) |
| `issue` | — | — | destination (`Modify`, §77.2) | — |

Les lignes non vides comptent 18 genres : les 16 genres à empreinte du brief, plus `enterFrame` et `spawn`, qui ne touchent que des feuilles créées. Les 10 autres genres n'ont aucune feuille touchée.

### Énoncés

« Quatre hypothèses » désigne `DDSound`, `StaticsOK`, `σ 0` initial et `RunFull`.

| Énoncé du brief | Statut | Théorème (`HandoffExtClass`) | Hypothèses |
|---|---|---|---|
| Partition : classes disjointes | prouvé | `classes_disjoint` (40) | aucune |
| Partition : elles couvrent tout toucher | prouvé | `classes_cover` (53) | aucune |
| La classe N est vide | **réfuté** | `classN_created` (125) ; témoin `classN_witness` (`HandoffExtWitness:526`) | `LStep` (pas `ok`) |
| Classe C : seul `spawnVal` crée et écrit | prouvé | `cw_spawnVal` (187) ; effets `enterC_fresh_uninit` (167), `spawn_fresh_uninit` (176), `alloc` dans la preuve | `LStep` |
| Feuilles mortes 1 : un pas qui touche une feuille existante exige qu'elle soit utilisable avant le pas | prouvé | `touch_usable_run` (372) | les quatre |
| Feuilles mortes 2 : une place qui n'est plus utilisable ne le redevient jamais | prouvé | `unusable_run` (607) ; forme par pas `usable_back_step` (539) | les quatre ; par pas : `KInvCA`, `DDSound`, `LStep` |
| Identités : une place créée par un pas n'existe dans aucun état antérieur | prouvé | `created_fresh_run` (626) | les quatre |
| Corollaire : aucune paire étendue n'a pour premier membre un pas où `l` meurt | prouvé | `extPair_first_not_dying` (691) | les quatre |
| Corollaire : aucune n'a pour second membre un pas qui crée `l` | prouvé | `extPair_second_not_created` (649) | les quatre |
| Lien E – capacité (`capacity_run`, `spawnVal_cap_pre`) | prouvé | `classEm_cap_run` (339), via `capReq_mode` (268) | les quatre |
| Lien D – capacité (`other_cap_dying_run`) | prouvé | `classD_other_run` (356) | les quatre |

**Classe N.** Une feuille touchée de classe N est créée et non écrite (`classN_created`) : on y trouve les locaux frais de `enterFrame` et `spawn`, les feuilles fraîches de `alloc` et les locaux du `spawn` par valeur qui ne sont pas des destinations. Témoins sur des `RunFull` depuis l'état initial :

- le local `X` créé par `enterFrame f1` dans W-HX (indice 0) ;
- la feuille créée par `alloc` dans S4 et W-SV (indice 3).

La réfutation tient à la définition du toucher, qui suit `TouchesF`. Elle n'a pas de conséquence sur les paires :

- un toucher N n'est jamais le second membre d'une paire (`extPair_second_classDE`, 678 : le second membre est de classe D ou E) ;
- comme premier membre, un toucher N n'est pas exclusif.

**Classe C.** Hors de `enterFrame`, `spawn`, `alloc` et `spawnVal`, aucun pas ne crée de place (`opStepC_len`, 140, et cas non noyau de `cw_spawnVal`). `enterFrame`, `spawn` et `alloc` laissent leurs feuilles fraîches `Uninit` : effet de §72 (`enterEff.I`), de C4 (`spawnEff`, même effet) et de §71 (`allocEff.I`). Le `spawn` par valeur crée et écrit dans W-SV (`W_SV_graph`).

**Feuilles mortes, premier énoncé.**

- Classe D : la feuille est utilisable avant le pas, par définition de `Dying`.
- Classe E : le contexte du pas a sur la feuille une capacité `cap5` présente (`capacity_run`, `spawnVal_cap_pre`, `capReq_observe`). Une autorité active la couvre donc, et `NoDangling` (§54) donne l'utilisabilité (`usable_of_cap5`, 320).

**Feuilles mortes, second énoncé.** Preuve par cas sur les 28 genres :

- les places existantes sont conservées ;
- les marques de mort ne sont que posées ;
- les cadres ne sont qu'empilés frais (`nF`) ou dépilés (`Pop.mem_frames`) ;
- `transfer` et les phases du `spawn` par valeur reprennent `transfer_usable_back` existant, avec §63.1 au départ de chaque phase.

## Tâche 3 — Frontière

| Énoncé du brief | Statut | Théorème (`HandoffExtFrontier`) | Hypothèses |
|---|---|---|---|
| Toute frontière vérifie `i ≤ r < j` | prouvé | `frontier_lt` (113) | les quatre |
| Existence de la frontière | prouvé | `frontier_exists` (128) | les quatre et `[DecidablePred k.SharedMutable]` (écart 7) |
| Contexte propre : `r > i` est un pas du contexte de `i` | prouvé | `frontier_own` (157) | les quatre |
| Coïncidence : toute `ExclPair` est une paire étendue | prouvé | `exclPair_extPair` (235) | les quatre |
| Coïncidence : sur une `ExclPair`, la frontière est `lossStep` et `i < r` | prouvé | `exclPair_frontier` (256) | les quatre |
| La forme stricte ne s'étend pas (W-SV) | prouvé | `W_SV_graph` (`HandoffExtWitness:414`) | trace W-SV |

**Existence et bornes.** Le second membre touche une feuille de classe D ou E (tâche 2). Dans l'état d'avant le pas `j`, la capacité du contexte de `i` est donc compatible avec ce toucher (`touchCompat_at_j`, 73) :

- classe D : `other_cap_dying_run` donne une capacité nulle ;
- classe E : la capacité exigée du contexte de `j` (`capacity_run`, `spawnVal_cap_pre`) et `cap5_compat` excluent toute capacité incompatible.

Le pas `j − 1` est donc candidat, d'où `r ≤ j − 1`. La borne `i ≤ r` est dans la définition. Les deux cas, E (par `capacity_run`, `spawnVal_cap_pre` et `cap5_compat`) et D (par `other_cap_dying_run`), sont traités séparément dans `touchCompat_at_j`.

**Contexte propre.** Si `r > i`, la capacité est incompatible avant le pas `r` et compatible après lui. Comme la compatibilité est close vers le bas (`touchCompat_mono`, 57), le rang de `cap5` baisse strictement au pas `r`, et `cap5_drop_own` (L1) attribue cette baisse au contexte de `i`.

**Les genres signalés par le brief.** `spawnVal`, `transfer`, `store`, `issue`, `exitFrame`, `terminate` et `unlock` touchent `l` et changent la capacité de leur propre contexte. L'argument ne distingue aucun genre : la recherche commence à `k = i`, et pour `r > i`, L1 s'applique au pas `r` quel qu'il soit. Le cas `r = i` est celui de la tâche 4.

**Forme stricte.** Sur W-SV, la recherche de l'événement précédent, à partir de `k > i` (`lossStep`), donne le pas 2 (indice 5). Ce pas n'est pas strictement avant `j` et n'est pas un pas de `c0`.

## Tâche 4 — Le cas où la frontière est le pas d'accès

### Inventaire

| Couple (genre, classe du premier membre) | `r = i` | Preuve ou témoin |
|---|---|---|
| tout genre, D (`exitFrame`, `terminate`, `free`, `endUse`) | impossible | `extPair_first_not_dying` |
| `read3`, `write3`, `writeShared`, E | impossible | `frontier_gt_access` (`HandoffExtSame:84`) : un accès garde toute capacité |
| `store`, E | impossible | `frontier_gt_store` (148) : `PremG` lit le droit de §65.5 dans l'état résultant, donc `cap5 = Modify` après le pas |
| `issue`, E | impossible | `frontier_gt_issue` (199) : même argument, §77.6 avec le §65.5 du `store` interne |
| tout genre autre que `spawnVal`, C | impossible | `cw_spawnVal` |
| tout genre autre que `enterFrame`, `spawn`, `alloc`, `spawnVal`, N | impossible | `classN_created` et `opStepC_len` |
| `spawn`, N (locaux de l'enfant) | **se produit** | `r_eq_i_witnesses` (235) : témoin `terminate` de la tranche 3 (indices `(0,2)`) et S3 (indices `(7,9)`) |
| `spawnVal`, C (destinations) | **se produit** | W-SV (`W_SV_graph`, `r_eq_i_witnesses`) |
| `spawnVal`, N (autre local de l'enfant) | **se produit** | `spawnVal_N_witness` (269), trace nouvelle dérivée de S4, `RunFull` |
| `enterFrame`, N | limite | but : `cap5(c, l) = some Modify` après le pas, `l` frais. Manque : la capacité d'une racine fraîche tenue par la nouvelle frame (`Attr5.base`, mode effectif d'une racine sans descendant, `NotGuarded` d'une identité fraîche). |
| `alloc`, N | limite | même but. Manque : le transport du droit du contexte sur le propriétaire à travers `alloc` (`Attr5.held`). |
| `unlock`, E (contrôleur) | **se produit** | `unlock_r_eq_i_no_hb` (`HandoffExtSame:399`) : le droit de `c1` sur le contrôleur passe par une autorité rangée dans la donnée protégée, exercée par son grant ; l'`unlock` relâche le grant et `cap5(c1, lock)` passe de `Observe` à none |
| `transfer`, `alloc`, `endUse`, `newMutex`, `acquire`, `resetLock`, `spawnVal` (sources), E | limite | but : `capRank (cap5 (σ (i+1)) c l) ≥` rang du mode exigé. Manque : la conservation de la capacité propre sur les feuilles touchées, genre par genre. C'est l'argument de transport des lemmes par label de `CapDrop`, établi pour les autres contextes. Le cas `unlock` montre que cette conservation n'est pas acquise d'avance : un pas qui relâche ou déplace une autorité peut couper une chaîne de détenteurs. |

Dans les 59 traces balayées, `r = i` apparaît pour `(spawn, N)`, `(spawnVal, C)`, `(spawnVal, N)` et `(unlock, E)`.

### Question : quand `r = i`, `hb(i, j)` tient-il toujours ?

**Réfuté.** Trace `RunFull` depuis l'état initial (`unlock_r_eq_i_no_hb`, `HandoffExtSame:399` ; étapes `ul_steps`, 377). Les étapes 1 à 3 du bloc MX donnent `MX₃` ; puis :

| Indice | Pas | Fondement |
|---|---|---|
| 3 | `c0 : o1′ := derive(root_M, Observe, {lock})` | O1 |
| 4 | `c0 : spawn c1` cédant `o1′` | C4 |
| 5 | `c1 : acquire(e)`, grant `g` | C16, C14.3 par `o1′` |
| 6 | `c1 : store(o1′, T)` | O8 par `g` ; ancre de `o1′` dans `f0`, frame de `T` (§65.4) |
| 7 | `c1 : unlock(e)` | C17 ; C17.4 par `o1′` tenue par `T`, exercée par `g` (C43, chaîne de détenteurs) |
| 8 | `c0 : resetLock(e)` | C18.1 par `slot`, que `o1′` ne couvre pas ; C18.4 par `root_M` |
| 9 | `c0 : acquire(e)`, grant `g′` | C16 |
| 10 | `c0 : release(o1′)` | O3, §62.2 par `g′` sur `T` |
| 11 | `c0 : unlock(e)` | C17 |
| 12 | `c0 : transfer(M, M′)` | O4 ; `lock` est une feuille de la source (§63.1) |

Faits obtenus :

- la paire `(7, 12, lock)` est exclusive étendue (`transfer` exige `Modify`) ;
- `cap5(c1, lock)` vaut `Observe` avant le pas 7 et none après : la frontière est le pas 7 lui-même ;
- `resetLock(e)` au pas 8 supprime l'arête stricte du mutex (C49), et aucun chemin `HBS` ne relie le pas 7 au pas 12.

Le jumeau sans `resetLock` (`unlock_r_eq_i_twin`, 435) a la même paire et la même frontière ; il est ordonné par l'arête stricte de l'`unlock` de `c1` vers l'`acquire` de `c0`. La paire `(5, 12, lock)` est elle aussi une course étendue, de frontière 7.

C'est la forme de W-RL, avec un droit sur le contrôleur rangé dans la donnée protégée. Ce fait porte sur le modèle abstrait : dire qu'il relève de C46 demanderait de justifier les événements physiques de l'`unlock` et du `transfer` (C27 à C29).

La piste du brief, qui passe par une feuille créée au pas `i`, échoue au noyau. Depuis `MX₄`, `c0` crée `c2` avec un local `L`, et `c2` dérive `z` sur `L` puis prend le mutex : ce préfixe est une `RunFull`. Mais `c2 : store(z, T)` est `reject`, par §65.4 (`AnchorOrder`) : l'ancre effective de `z` est dans la frame initiale de `c2`, qui n'est pas un ancêtre de la frame de `T` (`hint_store_rejected`, 317). Dans toutes les traces du dépôt où `r = i` vient d'une création (témoins `terminate`, S3, S3 en entier, W-SV, `spawnVal_N_witness`), `hb(i, j)` tient par l'arête de création. Que `hb(i, j)` tienne toujours quand le premier membre crée `l` n'est pas prouvé : il faudrait un invariant sur les détenteurs des autorités qui couvrent un local de l'enfant (§54, C3, C6). Je n'en tire pas de conclusion générale.

### Ordre dans le pas, tiré des clauses (entrée du travail sur les événements internes)

- **`(spawn, N)`.** C4, effets :
  - la frame initiale de l'enfant, ses places locales et leurs racines sont créées ensemble ;
  - les racines sont tenues par cette frame ;
  - les paramètres sont cédés à la frame.

  Le créateur n'a jamais de capacité sur `l` : il n'y a ni accès du créateur à `l` ni marqueur de perte. La frontière est la création elle-même. C28 et C47 placent l'événement de synchronisation du `spawn` dans le contexte parent, après le marqueur de cession des paramètres. `start(c)` précède le premier pas de l'enfant.
- **`(spawnVal, C)`.** C5, phases ordonnées :
  1. création des destinations, feuilles `Uninit`, racine `Modify` tenue par la frame de l'enfant (point additionnel 2) ;
  2. transfert, qui écrit les feuilles de destination (`Init`) ;
  3. cession des paramètres ;
  4. vérifications finales.

  L'écriture de `l` (phase 2) suit sa création (phase 1). Le créateur n'a de capacité sur `l` à aucune phase : C5 point 3 remplace l'exigence d'exercice côté destination par la condition de construction fraîche. Il n'y a donc pas de marqueur de perte, et l'écriture précède la cession. C47 : les événements d'accès des transferts appartiennent au contexte et à la phase qui les produisent, dans l'ordre création, transfert, cession. `start(c)` suit le pas.
- **`(spawnVal, N)`.** C5, phase 1 : la feuille est créée `Uninit` et jamais écrite par le pas ; ni accès ni perte. Comme pour `spawn`.
- **`(unlock, E)`.** C17, effet : le grant est relâché selon O3, le registre note `grant = none`, et l'état logique du contrôleur est rendu disponible, en une transition cohérente. C28 point 1 et C48 placent dans `po` le marqueur logique de perte du grant **avant** la publication atomique de l'état disponible du contrôleur, qui est l'accès à `lock`. Dans la trace ci-dessus, la capacité de `c1` sur `lock` tient à ce grant. La clause donne donc l'ordre : perte (marqueur du grant), puis accès (écriture de publication sur `lock`). L'accès physique suit la perte de la capacité qui le justifiait. C'est une entrée pour le travail sur les événements internes (`OB-C20`) ; ce n'est pas un verdict.

## Tâche 5 — Composition, inclusions, balayage

| Énoncé | Statut | Théorème (`HandoffExtFrontier`) | Hypothèses |
|---|---|---|---|
| Passation ordonnée étendue ⇒ pas de course étendue, sur `HB` | prouvé | `handoffOrderedExt_no_race` (317) | les quatre |
| idem sur `HBS` | prouvé | `handoffOrderedExtS_no_raceS` (330) | les quatre |
| Toute `Race` est une course étendue | prouvé | `race_raceExt` (344) | les quatre |
| Toute `RaceS` est une course étendue stricte | prouvé | `raceS_raceExtS` (352) | les quatre |
| La réciproque est fausse : W-HT | prouvé | `W_HT_noRace` (`HandoffExtWitness:147`) et `W_HT_graph` | trace W-HT |

**Preuve de la composition.** Elle ne demande ni l'existence de la frontière ni l'instance de décidabilité.

- Si `i < r` : `po(i, r)` par `frontier_own`, puis `hb(r, j)`.
- Si `r = i` : `hb(r, j)` est `hb(i, j)`.

Aucun ordre interne aux pas n'est invoqué.

**Réutilisation de `handoffOrdered_no_raceS`.** Elle ne demande aucune hypothèse que `RunFull` ne donne pas. `runFull_run5C` (50) donne `Run5C`, et `handoffOrdered_no_raceS_full` (361) l'applique avec les quatre hypothèses.

### Balayage

Les 59 traces `RunFull` du dépôt sont :

- les 33 traces du balayage du complément de la tranche 3 ;
- les 13 traces rejouées ;
- la trace de la réfutation de la tranche 3 (`Protected.ab`) ;
- les 12 traces nouvelles de cette tranche : W-HT, W-HT-J, W-HS, W-HS-J, W-HX, W-HX-J, W-SV, le jumeau de W-CR, le témoin `(spawnVal, N)`, le préfixe de la construction du brief, la trace `(unlock, E)` et son jumeau.

Les préfixes W-NM et `MX₃` sont des préfixes de W-RL₀.

`sweep_ext_1` à `sweep_ext_5` (`HandoffExtSweep:70`, 101, 131, 163, 194) et `sweep_ext_6` (`HandoffExtSame:456`) établissent par `decide`, pour chaque trace, la liste complète des paires exclusives étendues. `sweepExt_complete` (55) en garantit la complétude, sous les quatre hypothèses. Pour chaque paire, la table donne sa frontière `r`, `HBS(r, j)` (passation ordonnée étendue) et `HBS(i, j)` (absence de course étendue).

Traces sans paire exclusive étendue (30) : `cv`, `ce`, `cr`, le jumeau de W-GS, S10, `ts`, `ti`, `ta`, `tdt`, `am`, `td`, `lv`, W-GI jumeau (`gt`), W-RX B, `fr`, `ex`, W-GR suite, W-GC suite, S4, S9, `mt`, `dt`, `tA`, `tB`, `km`, `ks`, `tb`, `sa`, `Protected.ab`, jumeau de W-CR.

| Trace | Paires `(i, j, l)` → frontière `r` | Ordonnée (`HBS r j`) | `HBS i j` |
|---|---|---|---|
| W-HO | `(2,4,1)`, `(2,4,2)` → 3 | non | non |
| W-HO′ | `(3,5,0)` → 4 | non | non |
| W-HO″ | `(4,9,0)` → 5 | non | non |
| W-HO-J | `(2,6,1)`, `(2,6,2)` → 3 | oui | oui |
| W-HO″-J | `(4,11,0)` → 5 | oui | oui |
| `lc_trace` | `(4,7,2)`, `(4,9,2)` → 5 ; `(8,11,4)` → 9 | oui | oui |
| W-RL₀ | `(2,5,2)`, `(2,7,2)` → 3 ; `(6,10,3)` → 7 | oui | oui |
| W-RL | `(2,5,2)`, `(2,7,2)` → 3 | oui | oui |
| | `(6,11,3)` → 7 | non | non |
| W-RL-J | `(2,5,2)`, `(2,7,2)` → 3 ; `(6,13,3)` → 7 | oui | oui |
| W-TR | `(2,5,2)`, `(2,7,2)` → 3 | oui | oui |
| | `(5,9,2)`, `(7,9,2)` → 8 ; `(6,11,3)` → 7 | non | non |
| W-TR-J | `(2,5,2)`, `(2,7,2)` → 3 ; `(5,11,2)`, `(7,11,2)` → 8 ; `(6,13,3)` → 7 | oui | oui |
| S11 | `(2,7,2)` → 3 | oui | oui |
| S3 (jusqu'à l'étape 3) | `(5,8,2)` → 6 ; `(7,9,8)` → **7 = i** | oui | oui |
| témoin `terminate` (tranche 3) | `(0,2,2)`, `(0,3,3)`, `(0,4,3)`, `(0,5,2)`, `(0,5,3)`, `(0,5,4)` → **0 = i** | oui | oui |
| W-AG | `(9,13,3)` → 10 | non | non |
| W-AG-J | `(9,15,3)` → 10 | oui | oui |
| W-AG′ | `(9,13,3)` → 11 | oui | oui |
| S3 en entier | `(5,8,2)`, `(5,10,2)` → 6 ; `(7,9,8)` → **7 = i** | oui | oui |
| W-HT | `(2,4,0)` → 3 | non | non |
| W-HT-J | `(2,6,0)` → 3 | oui | oui |
| W-HS | `(3,5,0)` → 4 | non | non |
| W-HS-J | `(3,7,0)` → 4 | oui | oui |
| W-HX | `(0,4,0)`, `(1,4,0)` → 3 | oui | oui |
| | `(4,6,0)` → 5 | non | non |
| W-HX-J | `(0,4,0)`, `(1,4,0)` → 3 ; `(4,8,0)` → 5 | oui | oui |
| W-SV | `(4,5,4)` → **4 = i** | oui | oui |
| témoin `(spawnVal, N)` | `(4,5,5)` → **4 = i** | oui | oui |
| préfixe de la construction du brief | `(2,8,2)` → 3 | oui | oui |
| trace `(unlock, E)` | `(2,5,2)`, `(2,7,2)` → 3 | oui | oui |
| | `(5,12,2)` → 7 ; `(7,12,2)` → **7 = i** | non | non |
| jumeau sans `resetLock` | `(2,5,2)`, `(2,7,2)` → 3 ; `(5,11,2)` → 7 ; `(7,11,2)` → **7 = i** | oui | oui |

Les faits du corpus v15 (W-HT, W-HS, W-HX et leurs jumeaux, W-SV, W-NM dans W-RL₀, W-TR, W-TR-J) sont obtenus. Les traces jusqu'ici tenues pour ordonnées sont W-HO-J, W-HO″-J, `lc_trace`, W-RL₀, W-RL-J, W-TR-J et W-AG-J. Aucune n'a de course étendue. Les courses étendues sont toutes dans des traces déjà connues pour leurs courses (W-HO, W-HO′, W-HO″, W-RL, W-TR, W-AG), dans les nouveaux témoins attendus, ou dans la trace `(unlock, E)` construite pour la tâche 4. Les paires nouvelles de W-TR, `(5,9,2)` et `(7,9,2)`, sont les faits attendus par le corpus. Dans chaque trace, une paire est ordonnée exactement quand elle n'est pas une course.

## Paires hors de portée (listées, non traitées)

- `acquire`, `unlock` et `resetLock` entre eux sur le contrôleur, sous des droits `Observe` compatibles. Non exclusives (C44), elles relèvent de C35 à C42. Le modèle n'en fait pas des paires étendues : leur mode exigé est `Observe` des deux côtés.
- `alloc` par la branche `SharedMutable` : le fournisseur, de mode exigé `Observe`, n'est pas exclusif.
- Les genres sans empreinte dans le modèle mais avec des écritures physiques : `reset`, `newArena`, les métadonnées d'arène.
- L'ordre interne aux pas et les événements physiques (`OB-C19`, `OB-C20`).

## Tâche 6 — Contrôle ciblé d'`OB-C28`

| Point | Statut | Théorème (`OBC28Check`) | Hypothèses |
|---|---|---|---|
| Droit de §78.1 : tout pas `reset` satisfait `MetaRightG` dans l'état d'avant | prouvé | `reset_metaRightG_run` (80) ; forme par pas `reset_metaRightG_step` (50) | les quatre ; par pas : `LibInv` et `PremG` |
| idem, sur les traces du dépôt | vérifié | `reset_metaRightG_lv` (97) : le seul pas `reset` des traces `RunFull`, indice 6 de `NonRegression.lv` | trace |
| `AcquireOk` = droits de la table ∧ reste | prouvé | `acquireOk_iff` (134), reste `AcquireRest` (127), `DeriveSyncRest` (107) | aucune |
| `UnlockOk` = droits de la table ∧ reste | prouvé | `unlockOk_iff` (168), reste `UnlockRest` (160), `ReleaseRest` (146) | aucune |
| `ResetLockOk` = droit de la table ∧ reste | prouvé | `resetLockOk_iff` (189), reste `ResetLockRest` (181) | aucune |
| les restes n'atteignent aucune constante de droit | vérifié par `ScanRights` | sortie ci-dessous | — |
| `IssueStepC` n'appelle `opStepC` que pour `split` et `store` | prouvé | `issueStepC_iff` (223), forme `IssueSplitStore` (203) | aucune |
| `ParamOriginHidden` est une lecture négative | prouvé | `paramOriginHidden_iff` (252), `paramOriginHidden_no_exer5` (277) | aucune |
| aucune réimplantation sous un autre nom | non prouvable | laissé à la relecture | — |

**Preuve pour §78.1.** `PremG` du `reset` exige `Exer5` de `internal` en `Modify`. Sous `ArenaInvC` (§55, point 2), `internal` est tenu par une place, la valeur d'arène. L'exercice passe donc par le cas « tenue par une place » d'`Exer5`, c'est-à-dire par une autorité exerçable de mode effectif `Modify` sur toutes les feuilles de cette place : c'est `HasRight5` sur la valeur d'arène, donc `MetaRightG`. `metaRight_of_metaRightG` en tire `MetaRight` (§78.1) depuis la frame courante.

**Parcours `ScanRights`.** Le script est celui de l'annexe de `spec2-m4-encap.md`, lancé sur des noms donnés au lieu des constructeurs de `LStep` (`scratchpad/ScanRest.lean`). Sortie :

```
OBC28.DeriveSyncRest → []
OBC28.AcquireRest → []
OBC28.ReleaseRest → []
OBC28.UnlockRest → []
OBC28.ResetLockRest → []
AcquireOk → [CtrlRight]
UnlockOk → [HolderRight, CtrlRight]
ResetLockOk → [ExercisableAt]
```

Les restes n'atteignent aucune des sept constantes de droit. Les définitions complètes n'atteignent que celles de la table : C14.3 et C15.3 (`CtrlRight`, par `EntryAuth` et `LibSyncAuthorized`) ; C17.2 (§62.2) et C17.4 ; C18.1.

**Réponse : encodage, pas règle.** Aucune des deux lacunes d'`OB-C28` ne demande de changer une règle de WC5.3.

- **§78.1.** Le pas `reset` du modèle (`ResetStepC`) ne lit pas `MetaRight`. Sur les exécutions admises depuis l'état initial, le droit de §78.1 tient néanmoins dans sa forme sans `guarded` vivant : il se déduit de la prémisse que `PremG` lit déjà, l'exercice de `internal`, et de l'invariant d'arène, qui place `internal` dans la valeur d'arène. L'écart tient à l'encodage du pas, pas à la règle. Le combler revient à ajouter la lecture de `MetaRight` à `ResetStepC`, ce qui ne changerait aucune trace `RunFull` d'après `reset_metaRightG_run`. Je ne l'ai pas fait : c'est une définition existante.
- **Points établis par relecture.** Trois des quatre sont maintenant des lemmes. La relecture établissait qu'ils ne changeaient aucune lecture des règles ; les lemmes le confirment. Le quatrième, l'absence de réimplantation sous un autre nom, ne se prouve pas et reste à la relecture.

## Ce que la tranche établit, et ce qu'elle n'établit pas

Elle établit, dans le graphe abstrait à un événement par pas et sur `RunFull` depuis l'état initial :

- une composition conditionnelle étendue aux 16 genres à empreinte : la passation ordonnée étendue exclut la course étendue ;
- l'existence, les bornes `i ≤ r < j` et le contexte propre de la frontière ;
- la coïncidence avec la passation des accès directs ;
- les faits du corpus v15.

Elle n'établit pas :

- les accès physiques des pas composés, ni leur ordre (`OB-C19`, `OB-C20`) ;
- l'ordre interne aux pas (C27 à C29) ;
- que les exécutions sûres sont en passation ordonnée étendue ;
- l'absence de course (C52, `OB-C06`).

La question `r = i ⇒ hb(i, j)` est réfutée (tâche 4) : la frontière peut être le premier membre sans que `hb(i, j)` tienne.

## Pas refusés et contre-exemples

- Aucun pas attendu `ok` n'est refusé par le noyau ni exclu par l'encapsulation complète.
- Deux réfutations, rapportées sans correction :
  - « La classe N est vide » est faux : les feuilles créées non écrites sont de classe N. C'est sans effet sur les paires.
  - « Quand `r = i`, `hb(i, j)` tient » est faux : `unlock_r_eq_i_no_hb` est une `RunFull` depuis l'état initial, de forme W-RL, où l'`unlock` est sa propre frontière et où aucun `hb` ne relie la paire. C'est une course étendue, un fait sur le modèle abstrait, pas un verdict de C46.
- La construction suggérée par le brief pour cette question est refusée au noyau par §65.4. La réfutation passe par une autre construction.

## Audit des axiomes

`lake build` (dans `formal/`) : 142 jobs, succès, aucun avertissement. Les sept nouveaux modules sont recompilés un par un, sans message. Le `grep` d'`AGENTS.md` ne renvoie rien, et aucun `noncomputable` n'apparaît dans les nouveaux modules.

Décompte des théorèmes `Ern.Concurrency*` (script `scratchpad/Audit8.lean`) :

- **avant cette tranche** (`a234683`) : 2822 théorèmes, dont 1878 non internes ;
- **après** (`212a0e6`) : **3030**, dont **2010** non internes ;
- **dépendances d'axiomes** : aucune hors de `{propext, Quot.sound}` ;
- **noms retirés** : aucun (comparaison des listes de noms).

| Module | Théorèmes | Non internes |
|---|---|---|
| `HandoffExt` | 69 | 20 |
| `HandoffExtWitness` | 27 | 26 |
| `HandoffExtClass` | 41 | 34 |
| `HandoffExtFrontier` | 33 | 19 |
| `HandoffExtSweep` | 7 | 6 |
| `HandoffExtSame` | 17 | 15 |
| `OBC28Check` | 14 | 12 |
| **Total** | **208** | **132** |

Sommes : 69 + 27 + 41 + 33 + 7 + 17 + 14 = 208 et 20 + 26 + 34 + 19 + 6 + 15 + 12 = 132. Ensuite 2822 + 208 = 3030 et 1878 + 132 = 2010.

Nature des 208 ajouts :

- **117 théorèmes écrits**, tous non internes ;
- **15 lemmes d'équation générés** `ReqMode.eq_1` à `eq_15`, non internes : 117 + 15 = 132 ;
- **76 lemmes internes générés** :
  - équations de `match` de `HasReq` et de `ReqMode` : 15 + 15 ;
  - `_sparseCasesOn` : 3 ;
  - lemmes auxiliaires `_proof` de théorèmes écrits : 20 ;
  - preuves des instances de décidabilité de `HasReq`, `ReqMode` et `SweepExt` : 15 + 1 + 1 ;
  - équations de `match` de `releaseEff` : 4 ;
  - équations de `match` de `OptP` : 2.

  Total : 30 + 3 + 20 + 17 + 4 + 2 = 76.

Enfin 132 + 76 = 208. `releaseEff` et `OptP` ne sont pas modifiés : leurs équations sont générées dans les nouveaux modules par `unfold` et `split`.

## Fichiers protégés

Base de comparaison : `main` = `d0c2d87` (base de fusion). Commandes lancées à HEAD = `212a0e6`, puis de nouveau après le commit de ce rapport.

```
$ git diff --stat main...HEAD -- specs AGENTS.md CLAUDE.md formal/DESIGN.md formal/Ern/MemoryModel
$ git status --short -- specs AGENTS.md CLAUDE.md formal/DESIGN.md formal/Ern/MemoryModel
```

Les deux sorties sont vides. `git status --short` sur tout le dépôt était vide avant le commit de ce rapport.

## Limites et points non relus

- Couples « limite » de la tâche 4 : voir l'inventaire. Ils sont ouverts. Que `hb(i, j)` tienne quand le premier membre crée `l` n'est pas prouvé.
- La table des 28 genres est lue sur les définitions `TouchesF`, `CapReq`, `HasReq` et `ReqMode`, et sur les effets du noyau. Seuls `classN_created`, `cw_spawnVal` et `touchesF_existing` en prouvent le contenu.
- WC5.3 a été relu en entier pour les clauses C1 à C8, C13 à C23, C26 à C34 et C43 à C53, ainsi que la partie IV. Les clauses C9 à C12, C24, C25 et C35 à C42 ne l'ont pas été.
- Spec 1 a été relue pour §40 à §44 et §58 à §78. §79 à §90 ne l'ont pas été.

## Contrôle de C17 point 4

Brief « contrôle ciblé de la correction de C17 point 4 ». Branche `formal/spec2-m4`, à la suite de `ebbc311`. Le texte contrôlé est le point 4 proposé pour C17, non adopté ; il est cité ainsi dans les docstrings. WC5.3 n'est pas modifié. Toutes les additions sont dans un module nouveau, `formal/Ern/Concurrency/FullEncap/C17Check.lean`, importé dans `formal/Ern.lean`. Aucune définition existante n'est modifiée.

Commits : `4747540` (définitions et tâche 1), `75e035c` (tâche 2), `c697587` (tâche 3), `7452e6d` (tâche 4), puis ce rapport.

### Définitions ajoutées

| Nom (`C17Check`) | Ligne | Contenu |
|---|---|---|
| `prospUnlock st c g` | 37 | État prospectif : `(st.1.set (releaseEff (st.1.view c) g), st.2)` |
| `KeptRight L st c n` | 46 | Droit conservé : `CtrlRight5 L (prospUnlock st c g) e c`, où `e` est l'entrée `n` et `g` son grant |
| `UnlockKept L st lbl` | 56 | `KeptRight` pour un `unlock`, `True` pour les autres genres |
| `KeptAll L σ lbls` | 66 | Chaque pas de la trace satisfait `UnlockKept` |
| `RunC17 k L σ lbls` | 76 | Exécution corrigée : `RunFull k L σ lbls ∧ KeptAll L σ lbls` |
| `unlockCount` (`C17Check.NonReg`) | 168 | Nombre de pas `unlock` d'une trace, pour la table |

**Obtention de l'état prospectif.** Le grant enregistré `g` est libéré selon O3 :

- la composante noyau est `releaseEff` sur la vue du contexte agissant, réécrite par `SC.set` ;
- c'est exactement la composante noyau que `UnlockOk` produit ;
- le registre de synchronisation est inchangé : l'entrée enregistre toujours `grant = some g`, et l'état logique du contrôleur n'est donc pas modifié.

`controlOf_prospUnlock` (107) prouve que `ControlOf` est le même dans l'état prospectif : la libération garde les détenteurs (`prospUnlock_holder`, 89) et les places.

**Lecture du droit.** `KeptRight` lit le droit dans l'état prospectif, comme le demande le brief, et non dans l'état résultant. La preuve de coïncidence demandée pour l'autre lecture n'est donc pas requise. La tâche 3 utilise seulement l'inégalité `cap5_same` entre les deux registres, qui ne diffèrent que par le champ `grant`.

**Forme du droit.** `CtrlRight5` est la forme que `PremG` lit dans l'état d'avant le pas : `Exer5`, sans `guarded` vivant dans la chaîne. `NotGuarded` ne lit que les identités `guarded` des entrées vivantes, pas le champ `grant`.

**Inclusion.** `runC17_runFull` (81) : une exécution corrigée est une `RunFull`, par projection.

**Choix d'encodage.** Quand l'entrée n'existe pas ou n'enregistre aucun grant, le point 1 de C17 échoue et l'état prospectif est sans objet ; `KeptRight` vaut alors `False`. Aucun pas `unlock` d'une `RunFull` n'est dans ce cas, puisque `UnlockOk` exige `grant = some g`.

### Statuts des tâches 1 à 3

| Tâche | Énoncé | Statut | Théorème (`C17Check`) | Hypothèses |
|---|---|---|---|---|
| 1 | trace `unlock_r_eq_i_no_hb` : le préfixe jusqu'à l'indice 6 est une exécution corrigée | vérifié | `ul_kept` (123) | trace |
| 1 | idem : l'`unlock` de l'indice 7 ne satisfait pas le droit conservé | vérifié, conforme à l'attendu | `ul_kept` (123) | trace |
| 1 | jumeau sans `resetLock` : les deux mêmes faits | vérifié, conforme à l'attendu | `ulj_kept` (137) | trace |
| 2 | les 57 autres traces sont des exécutions corrigées | vérifié, conforme à l'attendu | `nonreg_1` (176), `nonreg_2` (212), `nonreg_3` (264) | traces |
| 3 | sur une exécution corrigée depuis l'état initial, toute paire exclusive étendue `(i, j, l)` dont le pas `i` est un `unlock` a sa frontière `r > i` | **prouvé** | `frontier_gt_unlock` (356) | `DDSound`, `StaticsOK`, état initial, `RunC17` |

**Le fait d'état de la tâche 1.** Dans les deux traces, `ul_kept` et `ulj_kept` établissent les faits suivants :

- l'`unlock` de l'indice 7 est `ok` selon C17 adopté (`UnlockOk`) et admis par `PremG` ;
- il échoue au seul droit conservé ;
- dans l'état prospectif, le grant 5 est inactif ;
- `o1′` (autorité 4) est active et tenue par `T` (place 3) ;
- `cap5` de `c1` sur `lock` (place 2) vaut `none`.

`c1` n'atteignait `T` que par le grant 5. Le préfixe ne contient aucun `unlock` : il est corrigé dès qu'il est une `RunFull`, et il l'est par `Replay.RunFull.take`.

**La preuve de la tâche 3** suit la piste du brief, mais lit le droit dans l'état prospectif.

1. `unlock_touchL_ctl` (305) : la feuille touchée est le contrôleur de l'entrée, car `unlock` ne crée aucune place (`unlock_P`, 295). « `l` son contrôleur » n'est donc pas une hypothèse : la paire l'impose.
2. `unlock_cap_after` (319) : le droit conservé, transporté au registre résultant par `cap5_same`, donne à `c` une capacité au moins `Observe` sur `l` après le pas.
3. Le toucher de l'`unlock` exige `Observe`. Il n'est pas mourant (`extPair_first_not_dying`) et ne crée rien, donc il n'est pas exclusif.
4. Le toucher de `j` est donc de classe D ou de classe E avec `Modify` (le cas C est exclu par `extPair_second_not_created`). Il est incompatible avec toute capacité présente (`touchCompat_excl_none`, `touchCompat_not_modify`).

Conséquence, dans le périmètre de la tranche 4 : sur une exécution corrigée, le couple `(unlock, E)` ne donne plus `r = i`. Les autres couples `r = i` de l'inventaire sont inchangés et ne sont pas traités ici.

### Table de non-régression

Les 57 traces `RunFull` du dépôt autres que la trace `(unlock, E)` et son jumeau sont celles du balayage de la tranche 4. Chaque ligne est établie par `decide` : verdict par `nonreg_1` à `nonreg_3`, nombre de pas `unlock` par `nonreg_1_count` (198), `nonreg_2_count` (246) et la dernière conjonction de `nonreg_3`. La `RunFull` de chaque trace vient du théorème existant cité dans la preuve.

| Trace | Pas `unlock` | Verdict |
|---|---|---|
| W-HO | 0 | corrigée |
| W-HO′ | 0 | corrigée |
| W-HO″ | 0 | corrigée |
| W-HO-J | 0 | corrigée |
| W-HO″-J | 0 | corrigée |
| `lc_trace` | 1 | corrigée |
| W-RL₀ | 1 | corrigée |
| W-RL | 1 | corrigée |
| W-RL-J | 1 | corrigée |
| W-TR | 1 | corrigée |
| W-TR-J | 1 | corrigée |
| S11 | 0 | corrigée |
| `cv` | 0 | corrigée |
| `ce` | 0 | corrigée |
| `cr` | 0 | corrigée |
| jumeau de W-GS | 1 | corrigée |
| S3 (jusqu'à l'étape 3) | 0 | corrigée |
| S10 | 0 | corrigée |
| `ts` | 0 | corrigée |
| `ti` | 0 | corrigée |
| `ta` | 0 | corrigée |
| `tdt` | 0 | corrigée |
| `am` | 0 | corrigée |
| `td` | 0 | corrigée |
| `lv` | 0 | corrigée |
| W-GI jumeau (`gt`) | 1 | corrigée |
| W-RX B | 0 | corrigée |
| `fr` | 0 | corrigée |
| `ex` | 0 | corrigée |
| témoin `terminate` (`tm`) | 0 | corrigée |
| W-AG | 0 | corrigée |
| W-AG-J | 0 | corrigée |
| W-AG′ | 0 | corrigée |
| W-GR suite | 0 | corrigée |
| W-GC suite | 0 | corrigée |
| S3 en entier | 1 | corrigée |
| S4 | 0 | corrigée |
| S9 | 0 | corrigée |
| `mt` (`mutex_trace`) | 1 | corrigée |
| `dt` | 0 | corrigée |
| `tA` | 0 | corrigée |
| `tB` | 0 | corrigée |
| `km` | 0 | corrigée |
| `ks` | 0 | corrigée |
| `tb` | 0 | corrigée |
| `sa` | 0 | corrigée |
| `Protected.ab` | 0 | corrigée |
| W-HT | 0 | corrigée |
| W-HT-J | 0 | corrigée |
| W-HS | 0 | corrigée |
| W-HS-J | 0 | corrigée |
| W-HX | 0 | corrigée |
| W-HX-J | 0 | corrigée |
| W-SV | 0 | corrigée |
| jumeau de W-CR | 0 | corrigée |
| témoin `(spawnVal, N)` | 0 | corrigée |
| préfixe de la construction du brief | 0 | corrigée |

**Bilan.** Aucun `unlock` admis jusqu'ici n'est exclu. La base est étroite : 10 traces seulement contiennent un `unlock`, un chacune, soit 10 pas `unlock` contrôlés. Dans chacun, le contexte qui déverrouille garde un droit sur le contrôleur par une autorité indépendante du grant.

### Tâche 4 — Observation

Les deux suites partent de l'état d'avant l'indice 7 : `(ul6, [⟨3, some 5⟩], [])`, égal à `ulσ 7`. `c1` y détient le grant 5, et `o1′` est tenue par `T`. Les pas sont enchaînés, chacun depuis l'état produit par le précédent.

Les théorèmes `obsA` (434) et `obsB` (474) du namespace `C17Check.Observe` établissent :

- le pas `ok` de chaque étape (`TermStep`, `ResetLockOk`, `AcquireOk`, `opStepC`, `UnlockOk`) ;
- `RunC17` sur chaque suite, c'est-à-dire l'encapsulation complète (`EncapFull`) de chaque pas et le droit conservé de chaque `unlock`.

**Suite A**

| Pas | Noyau | Encapsulation complète | Droit conservé | Clause défaillante |
|---|---|---|---|---|
| `c1 : terminate` | `ok` (C7) | admis | — | aucune |
| `c0 : resetLock(e)` | `ok` (C18) | admis | — | aucune |
| `c0 : acquire(e)` | `ok` (C16), grant 6 | admis | — | aucune |
| `c0 : release(o1′)` | `ok` (O3) | admis | — | aucune |
| `c0 : unlock(e)` | `ok` (C17) | admis | oui | aucune |

Après `terminate`, le grant 5 est inactif et `o1′` est toujours active, tenue par `T`. L'entrée enregistre encore `grant = some 5`.

**Suite B**

| Pas | Noyau | Encapsulation complète | Droit conservé | Clause défaillante |
|---|---|---|---|---|
| `c1 : o2 := derive(o1′, Observe, {lock})` | `ok` (O1), autorité 6 tenue par la frame 1 | admis | — | aucune |
| `c1 : unlock(e)` | `ok` (C17) | admis | oui | aucune |

Après l'`unlock`, `cap5` de `c1` sur `lock` vaut `Observe`.

Aucun pas n'est refusé dans les deux suites. La question de l'état après un refus ne s'est donc pas posée.

### Écarts au brief

- **Aucune hypothèse ajoutée.** La tâche 3 n'utilise que `DDSound`, `StaticsOK`, l'état initial et `RunC17`.
- **Tâche 3.** « `l` son contrôleur » n'est pas pris en hypothèse : `unlock_touchL_ctl` le déduit de la paire. L'énoncé prouvé vaut donc pour toute paire exclusive étendue dont le premier membre est un `unlock`.
- **`KeptRight` hors des points 1 à 3.** Il vaut `False` quand l'entrée n'a pas de grant (voir « Choix d'encodage »). C'est sans effet sur les énoncés, tous portés par des `unlock` `ok`.
- **Tâche 4.** Le brief ne dit pas comment enchaîner après un refus. Aucun refus n'ayant eu lieu, aucune convention n'a été nécessaire.

### Audit des axiomes

Même procédure que pour la tranche 4 : tous les théorèmes du préfixe `Ern.Concurrency`, internes compris, avec `collectAxioms`, et comparaison de la liste des noms avec celle de `212a0e6`.

- Total : 3030 + 24 = 3054 théorèmes, dont 2010 + 16 = 2026 non internes.
- Aucun ne dépend d'un axiome hors de `{propext, Quot.sound}`. Aucun nom n'a été retiré.
- Les 24 ajouts sont tous dans `C17Check`.
- **16 théorèmes écrits** :
  - définitions et lien avec `RunFull` : `runC17_runFull`, `prospUnlock_holder`, `controlOf_prospUnlock` ;
  - tâche 1 : `ul_kept`, `ulj_kept` ;
  - tâche 2 : `nonreg_1`, `nonreg_1_count`, `nonreg_2`, `nonreg_2_count`, `nonreg_3` ;
  - tâche 3 : `unlock_P`, `unlock_touchL_ctl`, `unlock_cap_after`, `frontier_gt_unlock` ;
  - tâche 4 : `obsA`, `obsB`.

  Soit 3 + 2 + 5 + 4 + 2 = 16.
- **8 lemmes internes générés** :
  - équations de `match` de `UnlockKept` : 2, et `_sparseCasesOn` : 1 ;
  - preuves de l'instance de décidabilité de `UnlockKept` : 2 ;
  - équations de `match` de `releaseEff`, générées par `unfold` : 2 ;
  - lemme auxiliaire `_proof` de `unlock_touchL_ctl` : 1.

  Soit 3 + 2 + 2 + 1 = 8, et 16 + 8 = 24.
- `lake build` passe (143 jobs, aucun avertissement) et le `grep` d'`AGENTS.md` ne renvoie rien.

### Fichiers protégés

Base : `main` = `d0c2d87`. Commandes lancées à HEAD = `7452e6d`.

```
$ git diff --stat main...HEAD -- specs AGENTS.md CLAUDE.md formal/DESIGN.md formal/Ern/MemoryModel
$ git status --short
```

Les deux sorties sont vides.

### Ce qui reste ouvert

- La correction n'est contrôlée que sur les traces du dépôt (10 pas `unlock` hors trace `(unlock, E)`) et par l'énoncé de la tâche 3. Aucune propriété générale de non-régression n'est prouvée.
- Les autres couples `r = i` de la tranche 4 (`spawn`, le `spawn` par valeur, et les couples limites) ne sont pas concernés par cette correction et restent tels qu'écrits.
