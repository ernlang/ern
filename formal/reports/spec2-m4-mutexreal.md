# Spec 2, jalon 4, tranche 2 — couche R, réalisation du mutex de référence

Formalisation exploratoire, branche `formal/spec2-m4`, jamais mergée.

**Sources lues** :
- le brief « couche R, réalisation du mutex de référence » ;
- `ERN_WC5_1_FINAL.md`, appelé ici « WC5.1 corrigé » : clauses C12 à C18, C21, C22, C26 à C34, C38 à C40, C47 à C49 ;
- `corpus-spec2-m3.md` v10, § 0, § 1 (S2, S7, S11, S17), § 2 octies et § 2 nonies.

**Modules** :
- `formal/Ern/Concurrency/EventModel/Complements.lean` (tâche 0) ;
- `formal/Ern/Concurrency/Corpus/ResetLockRight.lean` (tâche 1) ;
- `formal/Ern/Concurrency/MutexReal/` (tâches 2 à 6).

Les numéros de ligne sont ceux du commit `3764070`. Aucune définition existante n'est modifiée : ni la machine d'autorités, ni le graphe de la tranche 1, ni `EventModel`.

## Hypothèses de la réalisation

1. **Réalisation de référence** (corpus § 2 nonies) :
   - `newMutex(e)` donne l'écriture initiale non atomique de `0` ;
   - `acquire(e)` donne un RMW réussi qui lit `0` et écrit `1` ;
   - `unlock(e)` et `resetLock(e)` donnent une écriture atomique de `0`.

   Les trois ordres sont des paramètres (`Ords`) ; la référence est `acquire`, `release`, `relaxed` (`refOrds`). C'est une hypothèse de formalisation, pas une règle.
2. **Linéarisation.** `mo` est l'ordre des pas du protocole dans la trace, et chaque RMW lit la modification qui le précède. Ce n'est pas une propriété démontrée des exécutions physiques.
3. **Contrôleur fixe.** `ControlOf(e)` désigne la même feuille depuis la création de `e` (`CtlFixed`, `Bridge.lean:255`). Le déplacement du mutex (W-TR) est hors de cette passe.
4. **Début du graphe.** L'histoire du contrôleur commence à `newMutex(e)`, dont l'écriture tient lieu de l'écriture initiale `init` du fragment.
   - Dans le fragment, `init` est hors contexte et `hb`-avant tout, par convention de la couche E.
   - Le fragment n'établit donc pas l'ordre entre cette écriture et les accès des autres contextes.
   - Cet ordre n'est vérifié que sur les témoins, par l'arête de `spawn` du graphe strict de la tranche 1.
5. **Tentatives échouées.** Elles ne sont pas des pas de la trace (C16 point 2) et ne sont pas représentées. Sous une comparaison-échange, ce sont des lectures (C39).
6. **Un événement par pas.** Il n'y a aucun marqueur interne de gain ou de perte (C28).
7. **Arêtes de cycle de vie.** `spawn` et `join` appartiennent au graphe de la tranche 1. Aucune n'est attribuée à `EventModel`.

**Portée.** Le résultat principal (tâche 5) est un théorème conditionnel, sous la réalisation déclarée :
- il ne prouve pas qu'une réalisation physique respecte ces contraintes ;
- il ne décharge pas `OB-C05`.

## Résultats

| Tâche | Obtenu |
|---|---|
| 0, compléments de la couche E | les quatre énoncés prouvés |
| 1, W-RC | tous les verdicts du corpus obtenus ; le pas 4 est `ok` (question ouverte, voir § Problèmes de spécification) |
| 2, construction | graphe du contrôleur défini ; il ne contient que des événements sur l'unité atomique |
| 3, invariant et cohérence | prouvés, sans `Encap5R` |
| 4, classification | 28 genres classés ; **trois contre-exemples** (`store`, `alloc`, `issue`) là où le brief attendait aucun ; complétude prouvée pour les genres `protocole`, `exclu` et `fin de vie` |
| 5, correspondance | pont, synchronisation et réciproque prouvés ; réciproque réfutée sans l'hypothèse 3 (W-TR) |
| 6, témoins | tous les faits attendus du corpus obtenus |

| Commit | Tâche |
|---|---|
| `4b719a3` | 0 : `EventModel/Complements.lean` |
| `c87fc17` | 1 : `Corpus/ResetLockRight.lean` |
| `541099c` | 2 : `MutexReal/Graph.lean` |
| `ba27543` | 3 : `MutexReal/Coherence.lean` |
| `683606b` | 4 : `MutexReal/Classify.lean`, `MutexReal/ClassifyWitness.lean` |
| `3005d40` | 5 : `MutexReal/Bridge.lean` |
| `3764070` | 6 : `MutexReal/Witness.lean` |

## Tâche 0 — compléments de la couche E (`EventModel/Complements.lean`)

| Énoncé | Statut | Théorème | Hypothèses exactes |
|---|---|---|---|
| G1 avec les événements de `c1` avant ceux de `c0` | prouvé, conforme à l'attendu | `G1_back` `:33` | `rf` et `sw` vont de l'événement 4 à l'événement 1. Le graphe est bien typé et cohérent ; on a `sw(b, e)` et `hb(a, g)`, sans course. |
| `HB` est transitif | prouvé | `hb_trans` `:65` | aucune |
| `HB a b`, `a ≠ init` ⇒ `(po ∪ sw)⁺ a b` | prouvé | `hb_closure` `:76` | aucune |
| `ECO` irréflexif | prouvé | `eco_irrefl` `:179` | seulement `RfWF`, `MoTotal`, `RmwAtomic` |

**Clé de `hb_trans`.** Aucune arête de `po ∪ sw` n'aboutit à l'écriture initiale (`poSw_ne_zero`, `:45`) : `po` part après elle, et elle n'est pas capable d'acquisition.

**Preuve de `eco_irrefl`.** Un rang croît strictement le long de `rf`, `mo` et `rb` (`ecoRank`, `:94`).
- Une modification a pour rang deux fois le nombre de ses prédécesseurs dans `mo`.
- Une autre lecture a ce rang pour sa source `rf`, plus un.
- Le cas d'un RMW lu par `rb` utilise la totalité de `mo` et l'atomicité des RMW.

## Tâche 1 — témoin W-RC (`Corpus/ResetLockRight.lean`)

| Pas | Attendu (corpus) | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| 1. `c0 : s := derive(root_M, Modify, {slot})` | `ok` | `ok` ; ensuite `root_M` n'a plus de mode effectif sur `slot` et garde `Modify` sur `lock` | O1, §43.3 | `W_RC_1_ok` `:29` |
| 2. `c0 : enterFrame f1` cédant `s` | `ok` | `ok`, la frame courante est `f1` | O6 | `W_RC_2_ok` `:36` |
| avant le pas 4 | aucune autorité exerçable depuis `f1` n'a de mode effectif présent sur `lock` | obtenu, pour les deux modes | §43 | `W_RC_no_ctl_mode` `:41` |
| 3. `c0 (f1) : acquire(e)` | aucune issue `ok`, clause C14.3 | aucune issue `ok` ; C14.1 et C14.2 tiennent, C14.3 échoue | C14.3, §68.2 | `W_RC_3_reject` `:48` |
| 4. `c0 (f1) : resetLock(e)` | `ok` | **`ok`** | C18.1 (troisième clause de §43, par `s`), C18.2, C18.3 | `W_RC_4_ok` `:63` |
| jumeau : `c0 (f0) : resetLock(e)` depuis `MX₃` | `ok` | `ok` | C18 | `W_RC_twin_ok` `:68` |
| trace des pas `ok` | `Run5R` depuis l'état initial | obtenu ; `Encap5R` admet chaque pas, `resetLock` compris | C22 | `W_RC_run` `:84` |

Aucun pas attendu `ok` n'est refusé, ni par le modèle ni par `Encap5R`.

## Tâche 2 — construction (`MutexReal/Graph.lean`)

### Définitions

- `Ords` (`:34`), `refOrds` (`:40`) : les trois ordres, de l'`acquire`, de l'`unlock` et du `resetLock`.
- `CtlOp` (`:44`) et `CtlOp.kind` (`:51`) : `acquire` donne `rmw o.acq 0 1` ; `unlock` donne `wsh o.rel 0` ; `resetLock` donne `wsh o.reset 0`.
- `ctlOp e` (`:57`) : le pas comme pas du protocole sur l'entrée `e`, avec son contexte.
- `ctlOps` (`:64`), `ctlEvs` (`:68`) : la liste de ces pas, puis des événements, dans l'ordre de la trace.
- `NewMutexAt σ lbls e i` (`:73`) : le pas `i` est un `newMutex` qui ajoute l'indice `e` au registre.
- `mkGraph` (`:95`) :
  - l'écriture initiale de `0` est l'événement `0` ;
  - `mo` relie toutes les paires `a < b` (`allPairs`, `:84`) ;
  - `rf` va de `j` à `j + 1` pour chaque RMW `j + 1` (`rfPairs`, `:89`).
- `ctlGraph o e lbls` (`:99`) : `mkGraph (ctlEvs o e lbls)`.
- `ctlIdx e lbls i` (`:104`) : l'événement du pas `i`, soit le nombre de pas du protocole sur `e` avant `i`, plus un. `ctlEvs_at` (`:158`) prouve que cet événement est bien celui du pas.

### Choix de représentation (écarts au brief)

1. **Désignation de l'entrée.** L'entrée est l'indice dans le registre, comme dans les étiquettes `acquire`, `unlock` et `resetLock`. `newMutex(e)` est le pas qui ajoute l'indice `e` (`NewMutexAt`), puisque l'étiquette `newMutex c g` nomme `guarded` et non un indice.
2. **`init` ne dépend pas de la trace.** Le graphe ne dépend que des étiquettes. `init` tient lieu de `newMutex(e)` par l'hypothèse 4, sans lire l'état.
3. **Valeur lue par le RMW.** Elle est fixée à `0` par l'hypothèse 1. La cohérence exige alors que la modification précédente ait écrit `0` ; c'est l'invariant (tâche 3) qui le garantit, pas la construction.
4. **Contexte d'un événement** : celui de l'étiquette (`Label.ctx`).

## Tâche 3 — invariant et cohérence (`MutexReal/Coherence.lean`)

| Énoncé | Statut | Théorème | Restriction de trace |
|---|---|---|---|
| Invariant | prouvé | `ctl_invariant` `:332` | les pas `ok` de la trace (`LStep`) ; aucun grant pris pour `e` dans le premier état. Ni `Encap5R` ni l'état initial de §47. |
| Cohérence : bien typé et `EventConsistent` | prouvé | `ctlGraph_coherent` `:402` | les mêmes. `EventConsistent` vaut pour tout triplet ; le typage, pour tout triplet bien typé (`Ords.WellTyped`, `:203`). |
| Cohérence sur un `Run5R` partant d'un registre vide | prouvé | `ctlGraph_coherent_run` `:414` | `Run5R`, registre vide au départ |
| Non-vacuité | obtenue | `lc_graph`, `rl0_graph`, `rl_graph`, `rlj_graph` (tâche 6) | — |

**L'invariant.** À tout état `n`, il établit trois choses :
1. si l'entrée `e` existe, son grant enregistré vaut `none` si et seulement si `lastW` (`:223`) vaut `some 0` — c'est-à-dire si le dernier événement du graphe des pas avant `n`, dans `mo`, a écrit `0` ;
2. si l'entrée n'existe pas, aucun pas du protocole sur `e` n'a eu lieu ;
3. chaque RMW lit `0`.

L'énoncé ne lit que le registre, pas l'activité du grant : il couvre donc le grant abandonné. `s11_abandoned` (`Witness.lean:143`) l'instancie sur S11 après `exitFrameC(f1′)` : le grant `6` est enregistré et inactif, le dernier événement est le RMW, et `lastW` vaut `some 1`.

**Structure de la preuve de cohérence.**
1. Un lemme sur les listes : des événements de la forme déclarée, dont chaque RMW lit `0`, donnent un graphe `EventConsistent` (`mkGraph_consistent`, `:140`). `po`, `sw`, `rf`, `mo` et `rb` y croissent tous selon l'indice, ce qui donne la cohérence.
2. L'invariant fournit cette condition sur une trace.

## Tâche 4 — classification (`MutexReal/Classify.lean`, `MutexReal/ClassifyWitness.lean`)

### Empreinte : décision

`Touches L st lbl l` (`Classify.lean:40`) est une définition nouvelle, à valider.

**Notions que le modèle possède déjà :**
- `Label.Access` (`CapPreserve.lean`) : les accès de `read3`, `write3` et `writeShared` ;
- `KernelOp.Writes` (Spec 1 §59) : les feuilles écrites par `write3`, `writeShared`, `store` (sa cible) et `transfer` (sa destination) ;
- la réalisation du jalon 2, `realize` (`Realize.lean`) : des opérations sur des octets, sous une disposition mémoire.

**Notion retenue** : celle du brief, au niveau des feuilles. C'est l'union de `Label.Access`, de `KernelOp.Writes` et des places source et destination des pas qui changent un état d'initialisation ou un détenteur :

| Pas | Feuilles de l'empreinte |
|---|---|
| `transfer` | source et destination |
| `store` | cible |
| `endUse` | la place |
| `alloc` | fournisseur, propriétaire et places neuves |
| `enterFrame`, `spawn` | places neuves |
| `spawn` par valeur | places neuves et sources des transferts |
| `issue` | destination |
| `newMutex`, `acquire`, `unlock`, `resetLock` | le contrôleur de leur entrée (réalisation déclarée) |
| tous les autres pas | aucune |

`realize` n'est pas retenue, pour deux raisons. Elle est au niveau des octets, et elle n'a aucune opération pour les pas du protocole (`realize_sync`). Ni l'une ni l'autre notion ne contient l'autre :
- `realize` désalloue pour `free` et `exitFrame`, ce que la notion retenue ne compte pas ;
- `realize` n'écrit ni le fournisseur ni le propriétaire d'un `alloc`.

### Règle d'attribution du statut

Un seul statut par genre, par priorité décroissante :
1. `contre-exemple` : une trace `Run5R` le montre ;
2. `déplacement` : une trace montre `ControlOf(e)` changer ;
3. `fin de vie` : une trace montre un pas admis qui rend l'entrée morte ;
4. `exclu` : prouvé.

Pour les genres `fin de vie`, la propriété `exclu` est aussi prouvée : tant que l'entrée reste vivante, le pas ne la touche pas.

`classified_sound` (`:145`) prouve les statuts `exclu` et `fin de vie`, sous ces hypothèses :
- le pas est `ok` et admis par `Encap5R` ;
- l'état satisfait `KInvCA` et `AdminSep`, qui valent le long de toute trace encapsulée depuis l'état initial (`trace_inv`) ;
- l'entrée est enregistrée, et vivante avant et après le pas.

Sa conclusion : la feuille `ControlOf(e)` n'est pas dans l'empreinte, et `ControlOf(e)` ne change pas.

### Table

| # | Genre | Statut | Fondement |
|---|---|---|---|
| 1 | `derive` | exclu | `classified_sound` ; empreinte vide ; `ControlOf` gardé (`opStep_facts`, `ctl_same_eq`) |
| 2 | `split` | exclu | idem |
| 3 | `release` | fin de vie | `release_ends` (`ClassifyWitness.lean:238`) : depuis `MX₃`, `release(guarded)` est admis et tue l'entrée ; C22.1 n'exclut que `derive` et `split` de source `guarded` |
| 4 | `transfer` | déplacement | `transfer_moves` (`:165`) : W-TR, `ControlOf(e)` passe de `lock` à `lock′` (S7) |
| 5 | `depend` | exclu | empreinte vide |
| 6 | `enterFrame` | exclu | l'empreinte ne contient que des places neuves (`ctl_lt`) ; fin de vie non testée |
| 7 | `exitFrame` | exclu | empreinte vide ; fin de vie possible (mutex local d'une frame qui sort), non testée |
| 8 | `read3` | exclu | `CtlExcl` (C22 point 4) |
| 9 | `write3` | exclu | `CtlExcl` |
| 10 | `writeShared` | exclu | `CtlExcl` |
| 11 | `pin` | exclu | empreinte vide |
| 12 | `unpin` | exclu | empreinte vide |
| 13 | `endUse` | fin de vie | `endUse_ends` (`:213`) : `endUse(M)` touche `lock` et tue l'entrée ; vivante après, aucune feuille touchée (`endUse_ctl_not_touched`, `Classify.lean:113`, par C22 point 5) |
| 14 | `free` | exclu | empreinte vide ; la désallocation n'est pas dans la notion retenue ; fin de vie non testée |
| 15 | `alloc` | **contre-exemple** | `alloc_cex` (`:93`) |
| 16 | `store` | **contre-exemple** | `store_cex` (`:59`) |
| 17 | `spawn` | exclu | places neuves seulement |
| 18 | `terminate` | exclu | empreinte vide (`term_facts`) ; fin de vie non testée |
| 19 | `join` | exclu | état inchangé |
| 20 | `deriveSync` | exclu | `Encap` n'en admet aucun quand une entrée est vivante (`deriveSync_excluded`) |
| 21 | `newMutex` | protocole | sur une autre entrée, touche un autre contrôleur (C13.8 ; `proto_touch`, `Classify.lean:235`) |
| 22 | `acquire` | protocole | sur une autre entrée, un autre contrôleur (C21.4) |
| 23 | `unlock` | protocole | idem |
| 24 | `resetLock` | protocole | idem ; l'entrée réinitialisée est vivante (C18.1 exige `guarded` actif) |
| 25 | `spawn` par valeur (`spawnVal`) | déplacement | `spawnVal_moves` (`:188`) : depuis `MX₃`, transfert de `M` entier dans un local du fils ; admis, `ControlOf(e)` passe de `lock` (2) à la place 9 |
| 26 | `newArena` | exclu | état noyau inchangé |
| 27 | `issue` | **contre-exemple** | `issue_cex` (`:136`) |
| 28 | `reset` (arena) | exclu | `derive` puis `release` ; utilise `AdminSep` |

Bilan : 17 genres `exclu`, 2 `fin de vie`, 4 `protocole`, 2 `déplacement`, 3 `contre-exemple`.

**Écart à l'attendu du brief** (« aucun contre-exemple ») : il y en a trois. Les deux autres attendus sont obtenus : `transfer` est en déplacement (S7), `endUse` de `M` en fin de vie.

### Contre-exemples

Chacun est une trace `Run5R` depuis l'état initial, minimale, sans correction ni hypothèse ajoutée. L'entrée est vivante avant et après le pas, son contrôleur est inchangé, et le pas n'est pas un pas du protocole : il n'est donc pas un événement du graphe construit.

- **`store`** (`store_cex`). Depuis `MX₃` :
  1. `c0 : z := derive(root_M′, Observe, {slot′})` ;
  2. `c0 : store(z, lock)`.
  - Le `store` écrit `lock` (§59, `KernelOp.Writes`) et en fait le détenteur de `z`.
  - La réalisation du jalon 2 (`storeOps`) écrit aussi les octets de `lock`.
  - `Encap5R` l'admet. Ses seules prémisses sur ce pas sont les droits de `PlaceExcl` sur la cible, que `root_M` satisfait.
- **`alloc`** (`alloc_cex`). Depuis `MX₃`, `c0 : alloc(provider = slot, owner = lock)`.
  - `lock` devient détenteur de la nouvelle autorité racine (§71, effet).
  - C'est un changement de détenteur, donc dans l'empreinte retenue. La réalisation du jalon 2 n'écrit aucun octet de `lock` pour ce pas.
- **`issue`** (`issue_cex`). Bloc AR avant le partage de `M2` :
  1. `c0 : acquire(e2)` ;
  2. `c0 : issue(arena, R1, lock2)`.
  - Le bloc est stocké dans `lock2` (§77, §65), sous le grant : `MetaRight` passe par le grant.
  - La réalisation du jalon 2 (`realize_issue`) écrit les octets de `lock2`.

### Complétude

| Énoncé | Statut | Théorème | Hypothèses exactes |
|---|---|---|---|
| Un pas qui touche le contrôleur de `e` est un événement du graphe | prouvé, pour les genres `protocole`, `exclu` et `fin de vie` | `completeness` (`:277`) | Le pas `i` est `ok` et admis par `Encap5R`, depuis un état qui satisfait `KInvCA`, `SyncInv` et `AdminSep`. L'entrée `e` est vivante avant et après le pas `i`. Conclusion : le pas est l'événement `ctlIdx e lbls i`. |
| La même chose sur un `Run5R` depuis l'état initial | prouvé | `completeness_run` (`:311`) | Les invariants viennent de `trace_inv`, sous `DDSound` et des statiques bien formées. |
| La forme sans restriction de genre | réfutée | `store_cex`, `alloc_cex`, `issue_cex` | — |

La restriction « vivante avant et après » est nécessaire. Un pas `fin de vie` touche le contrôleur au moment où l'entrée meurt ; après cela, un autre `newMutex` peut réutiliser la feuille.

L'hypothèse 3 n'est pas utilisée : les genres `déplacement` sont hors de l'énoncé. Montrer que, sous l'hypothèse 3, un `transfer` ou un `spawn` par valeur ne touche jamais le contrôleur reste à faire.

### Ce dont dépend encore la lecture du graphe comme histoire complète du contrôleur

Aucun genre n'est `non classé` : la notion retenue donne une empreinte à chacun. La lecture complète dépend pourtant de quatre points :
1. **Les trois genres contre-exemples** (`store`, `alloc`, `issue`). Ils touchent le contrôleur hors protocole.
2. **Les deux genres `déplacement`.** Sous l'hypothèse 3, ils ne sont pas couverts par une preuve.
3. **Ce que la notion ne représente pas** (`OB-C20`) :
   - la mise à jour des métadonnées du fournisseur d'un `alloc` (§71.2), sans effet dans le modèle ni dans `allocOps` ;
   - la désallocation de `free` et des locaux d'`exitFrame` et de `terminate` ;
   - les accès internes des réalisations composées.
4. **Les tentatives échouées et les marqueurs internes** (hypothèses 5 et 6).

## Tâche 5 — correspondance (`MutexReal/Bridge.lean`)

| Énoncé | Statut | Théorème | Hypothèses exactes |
|---|---|---|---|
| Pont : `SWS(u, a)` avec `unlock(e)` en `u` ⇒ `rf(ctlIdx u, ctlIdx a)` | prouvé | `bridge` `:123` | les pas `ok` (`LStep`) ; aucun grant pris pour `e` dans le premier état. Ni l'hypothèse 3, ni `Encap5R`. |
| Synchronisation : `sw` ⇔ (`o.rel` ∈ {`release`, `seq_cst`}) ∧ (`o.acq` ∈ {`acquire`, `acq_rel`, `seq_cst`}) | prouvé | `bridge_sw` `:217` | celles du pont |
| `sw` pour la réalisation de référence | prouvé | `bridge_sw_ref` `:244` | celles du pont |
| Réciproque : `rf` de l'écriture d'un `unlock(e)` vers le RMW d'un `acquire(e)` ⇒ `SWS` | prouvé sous l'hypothèse 3 | `bridge_converse` `:264` | celles du pont et `CtlFixed` |
| Réciproque sans l'hypothèse 3 | réfutée | `converse_needs_fixed` `:331` | voir ci-dessous |

**Preuve du pont.** Entre `u` et `a`, il n'y a :
- aucun `acquire(e)`, par `SWS` ;
- aucun `resetLock(e)`, par `MutexGap` ;
- aucun `unlock(e)` : l'invariant rend le grant `none` après `u`, et `unlock` exige un grant enregistré (`unlock_grant`).

Les deux événements sont donc adjacents, et le RMW lit l'écriture de l'`unlock`. Les clauses `ctlAt` de `MutexGap` ne sont pas utilisées.

**Preuve de la réciproque.** L'arête `rf` rend les deux événements adjacents ; aucun pas du protocole sur `e` n'est donc entre `u` et `a`. L'hypothèse 3 fournit les clauses `ctlAt` de `MutexGap`.

**Réfutation sans l'hypothèse 3 : W-TR**, un `Run5R`. `rf` relie l'écriture de l'`unlock(e)` (pas 7) au RMW de l'`acquire(e)` (pas 10), mais `SWS` ne les relie pas : le contrôleur passe de `lock` (2) à `lock′` (6) au pas 9, qui n'est pas un pas du protocole.

## Tâche 6 — témoins (`MutexReal/Witness.lean`)

Tous les témoins sont des `Run5R` depuis l'état initial, sous la réalisation de référence.

| Trace | Attendu (corpus § 2 nonies) | Obtenu | Théorème |
|---|---|---|---|
| `lc_trace` | événements `init`, `A1`, `U1`, `A0` ; `rf` : `init → A1`, `U1 → A0` ; cohérent ; `sw(U1, A0)` et aucune autre ; `newMutex(e)` avant les pas de `c1` | tout obtenu. `newMutex(e)` est le pas 4, et les événements 1 à 3 sont les pas 7, 9 et 10. Le graphe est bien typé, et `newMutex(e)` précède les pas de `c1` dans `HBS`. | `lc_graph` `:62` |
| variantes de `lc_trace` | `unlock` en `relaxed`, ou `acquire` en `relaxed` : `rf(U1, A0)`, aucune arête `sw` | obtenu pour les deux ; cohérentes | `lc_variants` `:74` |
| W-RL₀ | comme `lc_trace` | obtenu | `rl0_graph` `:89` |
| W-RL | `init`, `A1`, `U1`, `R0`, `A0` ; `rf` : `init → A1`, `R0 → A0` ; cohérent ; aucune arête `sw` | obtenu | `rl_graph` `:101` |
| W-RL-J | comme W-RL ; les écritures de `T` sont ordonnées par le `join` dans le graphe strict | obtenu, avec `HBS(6, 13)` | `rlj_graph` `:114` |
| S11 (en plus) | l'invariant couvre le grant abandonné | grant enregistré et inactif ; `lastW = some 1` | `s11_abandoned` `:143` |

## Pas attendus `ok` refusés

Aucun. Ni le modèle ni `Encap5R` ne refusent un pas attendu `ok` : W-RC, les quatre traces de la tâche 6, S11 et les traces de la classification sont toutes admises.

## Problèmes de spécification

Ils sont rapportés avec le passage exact. Aucune interprétation n'a été choisie.

1. **C22 point 4 ne couvre pas `store` ni `issue` vers le contrôleur.**
   - Le passage : « does not expose ordinary `read3` of `ControlOf(entry)` … It also does not expose ordinary `write3` or out-of-protocol `writeShared` mutations of that controller ».
   - `store(z, lock)` et `issue(arena, R1, lock2)` écrivent la feuille du contrôleur (§59, §65 ; C27 : « `store` … may write or copy bytes »). C22 point 6 ne les exclut pas : le droit sur `lock` passe par `root_M`, ou par le grant pour `issue`, jamais par un `guarded` vivant.
   - C21.7 reste vrai : `lock` reste `Init`.
   - Exemple concret : `store_cex`, `issue_cex`. `alloc(owner = lock)` (`alloc_cex`) en est la variante par changement de détenteur.
   - À arbitrer : étendre C22 point 4 à toute opération dont l'empreinte contient le contrôleur, ou admettre ces pas.
2. **W-RC : `resetLock` sans droit sur le contrôleur** (corpus § 2 nonies, déjà signalé).
   - Le pas 4 est `ok` : la frame `f1`, sans autorité sur `lock`, déclenche l'écriture du contrôleur (C18, effet ; réalisation déclarée).
   - C29 exige une justification d'autorité pour chaque accès physique, et C17 point 4 en donne une à `unlock`. C18 n'a pas de clause équivalente.
   - À arbitrer, comme l'annonce le corpus.
3. **Observation, pas un problème : `release(guarded)`.** Il est admis et met fin à l'entrée (`release_ends`). C12 (« An entry is live exactly while `guarded` is active ») l'autorise, et C22.1 n'exclut que `derive` et `split` de source `guarded`.

## Non couvert

- Conformité d'une réalisation physique à la réalisation déclarée (`OB-C05`).
- W-TR, sinon comme réfutation de la réciproque.
- Les genres `déplacement` sous l'hypothèse 3 : leur absence de contact avec le contrôleur n'est pas prouvée.
- `OB-C20` : accès physiques hors de la notion d'empreinte retenue (métadonnées du fournisseur d'`alloc`, désallocations, accès internes des pas composés).
- Les genres `exitFrame`, `terminate` et `free`, qui peuvent rendre l'entrée morte : aucun témoin n'est construit.
- Tentatives échouées de comparaison-échange (hypothèse 5) ; marqueurs internes de gain ou de perte (hypothèse 6).
- Séquences de libération ; `seq_cst` global ; no-thin-air (`NoThinAir_RC11`, C34).
- L'ordre entre l'écriture initiale et les accès des autres contextes, hors des témoins (hypothèse 4).

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat.** 2283 théorèmes, dont 1515 non internes, contre 1956 (1348) avant cette passe. Aucun axiome hors `{propext, Quot.sound}`.
- **Modules nouveaux**, théorèmes (non internes) :

  | Module | Théorèmes (non internes) |
  |---|---|
  | `EventModel.Complements` | 18 (15) |
  | `Corpus.ResetLockRight` | 8 (8) |
  | `MutexReal.Graph` | 28 (21) |
  | `MutexReal.Coherence` | 63 (36) |
  | `MutexReal.Classify` | 120 (53) |
  | `MutexReal.ClassifyWitness` | 8 (8) |
  | `MutexReal.Bridge` | 79 (22) |
  | `MutexReal.Witness` | 6 (6) |

- **Build.** `lake build` réussit (105 jobs), sans avertissement.
- **Contrôles.** Le `grep` d'`AGENTS.md` est vide, et aucun `noncomputable` n'est utilisé.
