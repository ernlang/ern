# Spec 2, jalon 4, tranche 2 — couche R, réalisation du mutex de référence

Formalisation exploratoire, branche `formal/spec2-m4`, jamais mergée.

**Sources lues** :
- le brief « couche R, réalisation du mutex de référence » ;
- `ERN_WC5_1_FINAL.md`, appelé ici « WC5.1 corrigé » : clauses C12 à C18, C21, C22, C26 à C34, C38 à C40, C47 à C49 ;
- `corpus-spec2-m3.md` v10, § 0, § 1 (S2, S7, S11, S17), § 2 octies et § 2 nonies ;
- la Spec 1 (`specs/ERN_Memory_Model_Specification_v0.1.md`), §58, §59, §62, §65, §69, §70, §71, §73 et §77, pour les effets des pas classés en tâche 4.

**Modules** :
- `formal/Ern/Concurrency/EventModel/Complements.lean` (tâche 0) ;
- `formal/Ern/Concurrency/Corpus/ResetLockRight.lean` (tâche 1) ;
- `formal/Ern/Concurrency/MutexReal/` (tâches 2 à 6).

Les numéros de ligne sont ceux du commit `3cca039`. Aucune définition existante n'est modifiée : ni la machine d'autorités, ni le graphe de la tranche 1, ni `EventModel`.

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
| 4, classification | 28 genres classés ; **trois contre-exemples** (`store`, `alloc`, `issue`) là où le brief attendait aucun ; complétude prouvée pour les genres `protocole`, `exclu` et `fin de vie`, et pour `transfer` sous l'hypothèse 3 ; inachevée pour le `spawn` par valeur |
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
| `3cca039` | corrections après revue : feuilles qui meurent dans l'empreinte, `transfer` sous l'hypothèse 3, instances du pont et de `CtlFixed` |

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

L'énoncé ne lit que le registre, pas l'activité du grant : il couvre donc le grant abandonné. `s11_abandoned` (`Witness.lean:165`) l'instancie sur S11 après `exitFrameC(f1′)` : le grant `6` est enregistré et inactif, le dernier événement est le RMW, et `lastW` vaut `some 1`.

**Structure de la preuve de cohérence.**
1. Un lemme sur les listes : des événements de la forme déclarée, dont chaque RMW lit `0`, donnent un graphe `EventConsistent` (`mkGraph_consistent`, `:140`). `po`, `sw`, `rf`, `mo` et `rb` y croissent tous selon l'indice, ce qui donne la cohérence.
2. L'invariant fournit cette condition sur une trace.

## Tâche 4 — classification (`MutexReal/Classify.lean`, `MutexReal/ClassifyWitness.lean`)

### Définitions ajoutées

- `Dying` (`:32`), `Touches` (`:52`) : l'empreinte, décrite ci-dessous.
- `ExclKind` (`:82`), `FinKind` (`:91`), `ProtoKind` (`:96`) : les genres de statut `exclu`, `fin de vie` et `protocole`.
- Tâche 3 (`Coherence.lean`) : `CtlShape` (`:30`, les genres d'événements de la réalisation), `PredZero` (`:34`, chaque RMW lit `0`), `Ords.WellTyped` (`:203`), `lastW` (`:223`), `EntryStep` (`:228`, l'effet d'un pas sur l'entrée `e` du registre).
- Tâche 5 (`Bridge.lean`) : `CtlFixed` (`:255`, l'hypothèse 3).
- Tâche 6 (`Witness.lean`) : `SwExactly` (`:30`), `AfterNewMutex` (`:39`).

### Empreinte : décision

`Touches L st lbl l` (`Classify.lean:52`) est une définition nouvelle, à valider.

**Notions que le modèle possède déjà :**
- `Label.Access` (`CapPreserve.lean`) : les accès de `read3`, `write3` et `writeShared` ;
- `KernelOp.Writes` (Spec 1 §59) : les feuilles écrites par `write3`, `writeShared`, `store` (sa cible) et `transfer` (sa destination) ;
- la réalisation du jalon 2, `realize` (`Realize.lean`) : des opérations sur des octets, sous une disposition mémoire.

**Notion retenue** : celle du brief, au niveau des feuilles, élargie aux feuilles qui meurent. C'est l'union de `Label.Access`, de `KernelOp.Writes`, des places source et destination des pas qui changent un état d'initialisation ou un détenteur, et des feuilles utilisables qui cessent de l'être (`Dying`, `Classify.lean:32`), notion que le modèle possède déjà sous la forme de `FreedLeaf` et `EndingLeaf` :

| Pas | Feuilles de l'empreinte |
|---|---|
| `transfer` | source et destination |
| `store` | cible |
| `endUse` | la place (ses feuilles deviennent `Uninit`, §69) et les feuilles qui meurent avec elle |
| `free`, `exitFrame`, `terminate` | les feuilles qui meurent (§70, §73, effets) |
| `alloc` | fournisseur (§71.2 : ses métadonnées sont mises à jour), propriétaire (détenteur de la nouvelle racine, §71) et places neuves |
| `enterFrame`, `spawn` | places neuves |
| `spawn` par valeur | places neuves et sources des transferts |
| `issue` | destination (§77 : « an explicit write to that destination », qui détient le bloc) |
| `newMutex`, `acquire`, `unlock`, `resetLock` | le contrôleur de leur entrée (réalisation déclarée) |
| `derive`, `split`, `release`, `depend`, `pin`, `unpin`, `join`, `deriveSync`, `newArena`, `reset` | aucune : leur effet abstrait ne crée aucun accès physique (C27) et ne change ni un état d'initialisation, ni un détenteur, ni la vie d'une place |

`realize` n'est pas retenue, pour deux raisons. Elle est au niveau des octets, et elle n'a aucune opération pour les pas du protocole (`realize_sync`). Elle n'écrit ni le fournisseur ni le propriétaire d'un `alloc`, que la notion retenue compte.

### Règle d'attribution du statut

Un seul statut par genre, par priorité décroissante :
1. `contre-exemple` : une trace `Run5R` le montre ;
2. `déplacement` : une trace montre `ControlOf(e)` changer ;
3. `fin de vie` : une trace montre un pas admis qui rend l'entrée morte ;
4. `exclu` : prouvé.

Pour les genres `fin de vie`, la propriété `exclu` est aussi prouvée : tant que l'entrée reste vivante, le pas ne la touche pas.

`classified_sound` (`:163`) prouve les statuts `exclu` et `fin de vie`, sous ces hypothèses :
- le pas est `ok` et admis par `Encap5R` ;
- l'état de départ satisfait `KInvCA`, `SyncState` et `AdminSep`, et l'état d'arrivée `WF3` ; tous valent le long de toute trace encapsulée depuis l'état initial (`trace_inv`) ;
- l'entrée est enregistrée, et vivante avant et après le pas.

Pour les feuilles qui meurent, la preuve n'est pas vide par définition : `SyncInv` est préservé (`lstep_preserves`), et C21 point 3 rend le contrôleur d'une entrée vivante utilisable après le pas.

Sa conclusion : la feuille `ControlOf(e)` n'est pas dans l'empreinte, et `ControlOf(e)` ne change pas.

### Table

| # | Genre | Statut | Fondement |
|---|---|---|---|
| 1 | `derive` | exclu | `classified_sound` ; empreinte vide ; `ControlOf` gardé (`opStep_facts`, `ctl_same_eq`) |
| 2 | `split` | exclu | idem |
| 3 | `release` | fin de vie | `release_ends` (`ClassifyWitness.lean:238`) : depuis `MX₃`, `release(guarded)` est admis et tue l'entrée ; C22.1 n'exclut que `derive` et `split` de source `guarded` |
| 4 | `transfer` | déplacement | `transfer_moves` (`:165`) : W-TR, `ControlOf(e)` passe de `lock` à `lock′` (S7) ; sous l'hypothèse 3, il ne touche pas le contrôleur (`transfer_fixed_sound`, `Classify.lean:280`) |
| 5 | `depend` | exclu | empreinte vide |
| 6 | `enterFrame` | exclu | l'empreinte ne contient que des places neuves (`ctl_lt`) |
| 7 | `exitFrame` | exclu | feuilles qui meurent : le contrôleur d'une entrée vivante après le pas reste utilisable (C21.3) ; fin de vie possible (mutex local d'une frame qui sort), non testée |
| 8 | `read3` | exclu | `CtlExcl` (C22 point 4) |
| 9 | `write3` | exclu | `CtlExcl` |
| 10 | `writeShared` | exclu | `CtlExcl` |
| 11 | `pin` | exclu | empreinte vide |
| 12 | `unpin` | exclu | empreinte vide |
| 13 | `endUse` | fin de vie | `endUse_ends` (`:213`) : `endUse(M)` touche `lock` et tue l'entrée ; vivante après, le contrôleur n'est ni une feuille de la place (`endUse_ctl_not_touched`, `Classify.lean:129`, par C22 point 5) ni une feuille qui meurt (C21.3) |
| 14 | `free` | exclu | feuilles qui meurent, comme `exitFrame` ; fin de vie non testée |
| 15 | `alloc` | **contre-exemple** | `alloc_cex` (`:93`) |
| 16 | `store` | **contre-exemple** | `store_cex` (`:59`) |
| 17 | `spawn` | exclu | places neuves seulement |
| 18 | `terminate` | exclu | feuilles qui meurent, comme `exitFrame` (`term_facts`) ; fin de vie non testée |
| 19 | `join` | exclu | état inchangé |
| 20 | `deriveSync` | exclu | `Encap` n'en admet aucun quand une entrée est vivante (`deriveSync_excluded`) |
| 21 | `newMutex` | protocole | sur une autre entrée, touche un autre contrôleur (C13.8 ; `proto_touch`, `Classify.lean:316`) |
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

- **`store`** (`store_cex`). Spec 1 §65 : la cible peut déjà être `Init` ; l'effet en fait le détenteur de l'autorité et la rend `Init` ; §59 compte `store` parmi les écritures. Depuis `MX₃` :
  1. `c0 : z := derive(root_M′, Observe, {slot′})` ;
  2. `c0 : store(z, lock)`.
  - Le `store` écrit `lock` (§59, §65 ; `KernelOp.Writes`) et en fait le détenteur de `z`.
  - La réalisation du jalon 2 (`storeOps`) écrit aussi les octets de `lock`.
  - `Encap5R` l'admet. Ses seules prémisses sur ce pas sont les droits de `PlaceExcl` sur la cible, que `root_M` satisfait.
- **`alloc`** (`alloc_cex`). Depuis `MX₃`, `c0 : alloc(provider = slot, owner = lock)`.
  - `lock` devient détenteur de la nouvelle autorité racine (§71, effet).
  - C'est un changement de détenteur, donc dans l'empreinte retenue. La réalisation du jalon 2 n'écrit aucun octet de `lock` pour ce pas.
- **`issue`** (`issue_cex`). Bloc AR avant le partage de `M2` :
  1. `c0 : acquire(e2)` ;
  2. `c0 : issue(arena, R1, lock2)`.
  - Le bloc est stocké dans `lock2`, une écriture explicite de la destination (§77). Le grant justifie `MetaRight` ; le droit noyau sur `lock2` vient de `root_M2`. `PlaceExcl` ne vérifie aucun droit sur la destination d'un `issue`.
  - La réalisation du jalon 2 (`realize_issue`) écrit les octets de `lock2`.

### Complétude

| Énoncé | Statut | Théorème | Hypothèses exactes |
|---|---|---|---|
| Un pas qui touche le contrôleur de `e` est un événement du graphe | prouvé, pour les genres `protocole`, `exclu` et `fin de vie` | `completeness` (`:359`) | Le pas `i` est `ok` et admis par `Encap5R`, depuis un état qui satisfait `KInvCA`, `SyncState` et `AdminSep`, vers un état qui satisfait `WF3`. L'entrée `e` existe avant le pas `i` et elle est vivante avant et après. Conclusion : le pas est l'événement `ctlIdx e lbls i`. |
| La même chose sur un `Run5R` depuis l'état initial | prouvé | `completeness_run` (`:394`) | Les invariants viennent de `trace_inv`, sous `DDSound` et des statiques bien formées. |
| `transfer` sous l'hypothèse 3 : s'il laisse inchangé le contrôleur d'une entrée vivante, il ne le touche pas | prouvé | `transfer_fixed_sound` (`:280`) | `ok`, admis par `Encap5R`, `KInvCA` et `SyncState` au départ |
| `spawn` par valeur sous l'hypothèse 3 | inachevé | — | énoncé ouvert : un `spawnVal` `ok`, admis par `Encap5R`, depuis un état qui satisfait `KInvCA` et `SyncState`, après lequel le contrôleur d'une entrée vivante est inchangé, n'a pas ce contrôleur dans les sources de ses transferts. La preuve demande `transfer_ctl_cases` sur chaque phase de transfert, sur l'état produit par les phases précédentes ; elle n'est pas tentée. |
| La forme sans restriction de genre | réfutée | `store_cex`, `alloc_cex`, `issue_cex` | — |

La restriction « vivante avant et après » est nécessaire : un pas `fin de vie` touche le contrôleur au moment où l'entrée meurt (`endUse_ends`).

`completeness` ne couvre pas `newMutex(e)` lui-même : l'entrée `e` n'existe pas avant ce pas. Sa correspondance avec `init` est l'hypothèse 4, et `NewMutexAt` la vérifie sur chaque témoin.

`completeness` n'utilise pas l'hypothèse 3 ; les genres `déplacement` sont traités à part, ci-dessus.

### Ce dont dépend encore la lecture du graphe comme histoire complète du contrôleur

Aucun genre n'est `non classé` : la notion retenue donne une empreinte à chacun. La lecture complète dépend pourtant de quatre points :
1. **Les trois genres contre-exemples** (`store`, `alloc`, `issue`). Ils touchent le contrôleur hors protocole.
2. **Le `spawn` par valeur sous l'hypothèse 3** (inachevé ; `transfer` est prouvé).
3. **Ce que le modèle ne représente pas** (`OB-C20`) :
   - la mise à jour des métadonnées du fournisseur d'un `alloc` (§71), comptée dans l'empreinte mais sans effet dans le modèle (`allocEff`) ni dans la réalisation (`allocOps`) ;
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

**Non-vacuité.** Sur `lc_trace`, l'hypothèse 3 tient, et l'arête stricte du pas 9 au pas 10 (`lc_strict`) donne par `bridge` l'arête `rf` de l'événement 2 à l'événement 3, par `bridge_sw_ref` une arête `sw`, et `bridge_converse` rend l'arête stricte (`lc_bridge`, `Witness.lean:89`). L'hypothèse 3 tient aussi sur W-RL₀ (`rl0_fixed`, `:103`).

**Réfutation sans l'hypothèse 3 : W-TR**, un `Run5R`. `rf` relie l'écriture de l'`unlock(e)` (pas 7) au RMW de l'`acquire(e)` (pas 10), mais `SWS` ne les relie pas : le contrôleur passe de `lock` (2) à `lock′` (6) au pas 9, qui n'est pas un pas du protocole.

## Tâche 6 — témoins (`MutexReal/Witness.lean`)

Tous les témoins sont des `Run5R` depuis l'état initial, sous la réalisation de référence.

| Trace | Attendu (corpus § 2 nonies) | Obtenu | Théorème |
|---|---|---|---|
| `lc_trace` | événements `init`, `A1`, `U1`, `A0` ; `rf` : `init → A1`, `U1 → A0` ; cohérent ; `sw(U1, A0)` et aucune autre ; `newMutex(e)` avant les pas de `c1` | tout obtenu. `newMutex(e)` est le pas 4, et les événements 1 à 3 sont les pas 7, 9 et 10. Le graphe est bien typé, et `newMutex(e)` précède les pas de `c1` dans `HBS`. | `lc_graph` `:63` |
| variantes de `lc_trace` | `unlock` en `relaxed`, ou `acquire` en `relaxed` : `rf(U1, A0)`, aucune arête `sw` | obtenu pour les deux ; cohérentes | `lc_variants` `:76` |
| W-RL₀ | comme `lc_trace` | obtenu | `rl0_graph` `:111` |
| W-RL | `init`, `A1`, `U1`, `R0`, `A0` ; `rf` : `init → A1`, `R0 → A0` ; cohérent ; aucune arête `sw` | obtenu | `rl_graph` `:123` |
| W-RL-J | comme W-RL ; les écritures de `T` sont ordonnées par le `join` dans le graphe strict | obtenu, avec `HBS(6, 13)` | `rlj_graph` `:136` |
| S11 (en plus) | l'invariant couvre le grant abandonné | grant enregistré et inactif ; `lastW = some 1` | `s11_abandoned` `:165` |
| `lc_trace`, W-RL₀ (en plus) | instances de l'hypothèse 3 et du pont | obtenu | `lc_bridge` `:89`, `rl0_fixed` `:103` |

## Pas attendus `ok` refusés

Aucun. Ni le modèle ni `Encap5R` ne refusent un pas attendu `ok` : W-RC, les quatre traces de la tâche 6, S11 et les traces de la classification sont toutes admises.

## Problèmes de spécification

Ils sont rapportés avec le passage exact. Aucune interprétation n'a été choisie.

1. **C22 point 4 ne couvre pas `store` ni `issue` vers le contrôleur.**
   - Le passage : « does not expose ordinary `read3` of `ControlOf(entry)` … It also does not expose ordinary `write3` or out-of-protocol `writeShared` mutations of that controller ».
   - `store(z, lock)` et `issue(arena, R1, lock2)` écrivent la feuille du contrôleur (Spec 1 §59, §65, §77 ; C27 : « `store` … may write or copy bytes »). C22 point 6 ne les exclut pas : le droit sur `lock` ou `lock2` passe par `root_M` ou `root_M2`, jamais par un `guarded` vivant ; pour `issue`, `PlaceExcl` ne regarde que `MetaRight`, que le grant justifie.
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
- Le `spawn` par valeur sous l'hypothèse 3 : son absence de contact avec le contrôleur n'est pas prouvée (`transfer` l'est).
- `OB-C20` : accès physiques hors de la notion d'empreinte retenue (métadonnées du fournisseur d'`alloc`, désallocations, accès internes des pas composés).
- Les genres `exitFrame`, `terminate` et `free`, qui peuvent rendre l'entrée morte : aucun témoin n'est construit.
- Tentatives échouées de comparaison-échange (hypothèse 5) ; marqueurs internes de gain ou de perte (hypothèse 6).
- Séquences de libération ; `seq_cst` global ; no-thin-air (`NoThinAir_RC11`, C34).
- L'ordre entre l'écriture initiale et les accès des autres contextes, hors des témoins (hypothèse 4).

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat.** 2295 théorèmes, dont 1521 non internes, contre 1956 (1348) avant cette passe. Aucun axiome hors `{propext, Quot.sound}`.
- **Modules nouveaux**, théorèmes (non internes) :

  | Module | Théorèmes (non internes) |
  |---|---|
  | `EventModel.Complements` | 18 (15) |
  | `Corpus.ResetLockRight` | 8 (8) |
  | `MutexReal.Graph` | 28 (21) |
  | `MutexReal.Coherence` | 63 (36) |
  | `MutexReal.Classify` | 130 (57) |
  | `MutexReal.ClassifyWitness` | 8 (8) |
  | `MutexReal.Bridge` | 79 (22) |
  | `MutexReal.Witness` | 8 (8) |

- **Build.** `lake build` réussit (105 jobs), sans avertissement.
- **Contrôles.** Le `grep` d'`AGENTS.md` est vide, et aucun `noncomputable` n'est utilisé.

# Passe corrective

**Sources.**
- `ERN_WC5_2_amendements_proposes.md` : deux amendements **proposés, non validés** (remplacement de C22 point 4, ajout de C18 point 4). Cette passe les teste et ne les valide pas. Le fichier n'est pas commité.
- `corpus-spec2-m3.md` v11, § 2 decies.
- WC5.1 corrigé (inchangé), C13, C14, C17, C18, C22.
- Spec 1 §64 (`depend`) et §68.

**Décisions de l'arbitre prises en compte.** La définition `Touches` est acceptée, et l'observation sur `release(guarded)` est retenue telle quelle.

**Ce qui n'est pas touché.** Aucune définition existante n'est modifiée ni affaiblie : `Encap5R`, `Touches`, `ResetLockOk`, la relation de pas et tous les théorèmes antérieurs restent tels quels. Les trois contre-exemples et W-RC restent dans le dépôt.

**Modules nouveaux** :
- `MutexReal/Amend.lean` (tâche 1) ;
- `MutexReal/AmendWitness.lean` (tâche 2) ;
- `MutexReal/NonRegression.lean` (tâche 3) ;
- `MutexReal/Classify6.lean` et `MutexReal/Classify6Witness.lean` (tâche 4) ;
- `MutexReal/ResetAmend.lean` (tâche 5) ;
- `Corpus/NewMutexRight.lean` (tâche 6).

Les numéros de ligne de cette section sont ceux du commit `0b9d3b8`.

| Commit | Tâche |
|---|---|
| `866849f` | 1 : définitions et inclusions |
| `fadf981` | 2 : exclusions et jumeaux |
| `c7d497b` | 3 : non-régression |
| `54574d0` | 4 : classification rejouée |
| `df68726` | 5 : `resetLock` amendé |
| `0b9d3b8` | 6 : W-NC |

## Tâche 0 — décompte réconcilié

Le rapport précédent annonçait 1956 théorèmes avant la passe, 342 dans les modules nouveaux et 2295 au total ; or 1956 + 342 = 2298.

**Méthode.** La liste exacte des noms de théorèmes `Ern.Concurrency*` a été extraite à `956217e` (commit reconstruit dans un worktree temporaire) puis à `83b6adf`, et comparée.

**Résultat.**
- Aucun nom n'a disparu : 1956 noms avant, 2295 après. Aucun énoncé n'a été supprimé, renommé ni déplacé.
- Il y a 339 noms nouveaux, et non 342.
- Les trois noms en trop ont été comptés deux fois : ils existaient déjà, et le décompte par module les a attribués à un module nouveau.

| Nom | Interne | Module avant | Module après |
|---|---|---|---|
| `Ern.Concurrency.Label.termOf.eq_1` | non | `EventsProtocols` | `MutexReal.Bridge` |
| `Ern.Concurrency.Label.termOf.eq_2` | non | `EventsProtocols` | `MutexReal.Bridge` |
| `Ern.Concurrency.Label.termOf._sparseCasesOn_1.else_eq` | oui | `EventsProtocols` | `MutexReal.Bridge` |

**Raison.** Ce sont des lemmes d'équation de `Label.termOf`, générés à la demande par `simp [Label.termOf]`.
- `EventsProtocols` les génère (lignes 116 et 167), et `MutexReal.Bridge` aussi (lignes 129 et 225), car `Bridge` n'importe pas `EventsProtocols`.
- Avec un seul des deux modules importé, chacun les possède ; sous `import Ern`, `getModuleIdxFor?` les rattache à `Bridge`.

Le décompte par module de la passe précédente les comptait donc dans `Bridge` (79), alors qu'ils figuraient déjà dans les 1956.

Correction : les modules nouveaux de la couche R comptent 339 théorèmes, dont 173 non internes. 1956 + 339 = 2295, et 1348 + 173 = 1521.

## Définitions ajoutées (`MutexReal/Amend.lean`)

| Définition | Ligne | Contenu |
|---|---|---|
| `TouchesX` | `:34` | l'empreinte élargie : `Touches`, plus la place `result` d'un `depend` |
| `C223Move` | `:55` | un `transfer` dont la source satisfait `TransferExcl`, ou un `spawn` par valeur dont les phases satisfont `EncapVals` : l'exception de C22 point 3, écrite à la lettre et non par genre d'étiquette |
| `CtlRestr` | `:68` | la restriction du contrôleur, voir ci-dessous |
| `Encap6` | `:93` | `Encap5R` et `CtlRestr` |
| `Run6` | `:99` | exécution à états nommés dont chaque pas satisfait `Encap6` et est `ok` |
| `ResetLockAmOk` | `:126` | `ResetLockOk` et `CtrlRight L s e (s.view c).top` sur la même entrée, la forme qu'`UnlockOk` utilise pour C17 point 4 |
| `AmCond` | `:138` | la clause ajoutée par C18 point 4 à un pas `resetLock` ; rien sur les autres pas |
| `RunAm` | `:149` | une `Run6` dont chaque pas satisfait `AmCond` : l'« exécution amendée » |
| `CexKind` | `Classify6.lean:31` | les genres des trois anciens contre-exemples |

**`CtlRestr`** (`:68`). Pour toute entrée `i` vivante avant le pas : si l'empreinte élargie contient `ControlOf(i)`, alors le pas vérifie l'une de trois conditions :
1. c'est un pas du protocole de `i` (`ctlOp i lbl ≠ none`) ;
2. c'est un `C223Move` ;
3. l'entrée `i` est morte après le pas.

**Écarts et choix d'encodage :**
1. **`depend` touche la place `result` elle-même**, pas ses feuilles. `dependEff` ne change que `D result` (Spec 1 §64, effet), et l'amendement parle de l'état de dépendance « de la feuille du contrôleur ». Conséquence : `depend(M, a)`, avec `M` ancêtre de `lock`, n'est pas refusé. La lecture par les feuilles le refuserait ; aucune trace du dépôt ne contient un tel pas.
2. **L'encapsulation corrigée lit l'état d'arrivée.** L'exception « un pas après lequel l'entrée est morte » l'impose : `Encap6` n'est donc plus un prédicat sur l'état de départ seul, contrairement à `Encap5R`.
3. **Le pas amendé est un prédicat à côté de la relation de pas**, comme le demande le brief. Une `Run6` n'impose pas C18 point 4 ; seule une `RunAm` l'impose.

## Tâche 1 — inclusions

| Énoncé | Statut | Théorème | Hypothèses |
|---|---|---|---|
| toute `Run6` est une `Run5R` | prouvé | `run6_run5R`, `Amend.lean:105` | aucune |
| un `resetLock` amendé `ok` est un `resetLock` `ok` | prouvé | `ResetLockAmOk.ok`, `:132` | aucune |
| dans une exécution amendée, chaque pas `resetLock` est un `resetLock` amendé `ok` | prouvé | `RunAm.resetLock`, `:161` | aucune |

## Tâche 2 — exclusions et jumeaux (`MutexReal/AmendWitness.lean`)

| Cas | Attendu (corpus § 2 decies) | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| `store(z, lock)`, dernier pas de `store_cex` | refusé | refusé ; la trace n'est pas une `Run6` | C22 point 4 proposé (cible = contrôleur) | `store_refused` `:27` |
| `alloc(provider = slot, owner = lock)`, dernier pas d'`alloc_cex` | refusé | refusé ; pas une `Run6` | idem (propriétaire = contrôleur) | `alloc_refused` `:35` |
| `issue(arena, R1, lock2)`, dernier pas d'`issue_cex` | refusé | refusé ; pas une `Run6` | idem (destination = contrôleur) | `issue_refused` `:43` |
| jumeau `store(z, lock′)` | `ok`, admis | `ok` ; trace `Run6` depuis l'état initial | Spec 1 §65 | `store_twin` `:64` |
| jumeau `alloc(provider = slot, owner = lock′)` | `ok`, admis | `ok` ; `Run6` | §71.3 | `alloc_twin` `:86` |
| jumeau `issue(arena, R1, d0)` | `ok`, admis | `ok` ; `Run6` | §77 (comme S3, pas 3) | `issue_twin` `:108` |
| `depend(lock, a)` | noyau `ok`, refusé | noyau `ok` (§64.1, §64.3) et admis par `Encap5R` ; refusé par la restriction ; l'entrée reste vivante | C22 point 4 proposé (état de dépendance) | `depend_refused` `:156` |
| jumeau `depend(lock′, a)` | `ok`, admis | `ok` ; `Run6` | §64 | `depend_twin` `:169` |

Les refus sont énoncés sur les états existants (`csσ`, `caσ`, `ciσ`). Aucun pas attendu `ok` n'est rejeté par le noyau, et aucun jumeau n'est refusé.

## Tâche 3 — non-régression (`MutexReal/NonRegression.lean`)

| Trace | `Run6` | Théorème |
|---|---|---|
| W-HO | oui | `W_HO_run6` `:32` |
| W-HO′ | oui | `W_HO2_run6` `:34` |
| W-HO″ | oui | `W_HO3_run6` `:36` |
| W-HO-J | oui | `W_HOJ_run6` `:38` |
| W-HO″-J | oui | `W_HO3J_run6` `:40` |
| `lc_trace` | oui | `lc_run6` `:42` |
| W-RL₀ | oui | `W_RL0_run6` `:44` |
| W-RL | oui | `W_RL_run6` `:46` |
| W-RL-J | oui | `W_RLJ_run6` `:48` |
| W-TR (transfert du mutex entier, C22.3) | oui | `W_TR_run6` `:50` |
| W-TR-J | oui | `W_TRJ_run6` `:52` |
| W-RC | oui ; ce n'est pas une exécution amendée (tâche 5) | `W_RC_run6` `:54` |
| S11 (grant abandonné) | oui | `s11_run6` `:56` |
| `spawnVal_moves` (déplacement par valeur, C22.3) | oui | `spawnVal_moves_run6` `:59` |
| `endUse_ends` (fin de vie de S17) | oui | `endUse_ends_run6` `:62` |
| `release_ends` (`release(guarded)`) | oui | `release_ends_run6` `:64` |
| `store_cex` | **non** (attendu) | `store_refused` |
| `alloc_cex` | **non** (attendu) | `alloc_refused` |
| `issue_cex` | **non** (attendu) | `issue_refused` |
| jumeau de W-GS (§ 2 sexies), reformulé à états nommés | oui | `gs_twin_run6` `:85` |
| S3 jusqu'à `issue` (arena sous grant), reformulé | oui | `s3_run6` `:121` |
| S10 (transferts du mutex entier, grant actif), reformulé | oui | `s10_run6` `:158` |

Les trois dernières traces ne figuraient dans le dépôt que comme `EncapsulatedTrace5R`, sans états nommés ; elles sont reformulées ici. Les traces de cette passe (jumeaux, `depend_twin`, W-NC) sont des `Run6` par construction.

Traces encapsulées non vérifiées, faute d'états nommés :
- les traces `EncapsulatedTrace` de WC4 (`traceA`, `traceB` de S7, `endUse_mutex_kills_entry` de S17) ;
- `s4_trace5R`, sans entrée de mutex : la restriction y est vide ;
- `s2_trace5R`, dont les pas sont le préfixe de W-RL₀ ;
- `lc_trace5R`, qui est `lc_trace`.

## Tâche 4 — classification rejouée (`MutexReal/Classify6.lean`, `Classify6Witness.lean`)

### Table

| Genres | Statut précédent | Statut sous `Run6` | Fondement |
|---|---|---|---|
| `derive`, `split`, `depend`, `enterFrame`, `exitFrame`, `read3`, `write3`, `writeShared`, `pin`, `unpin`, `free`, `spawn`, `terminate`, `join`, `deriveSync`, `newArena`, `reset` (17) | exclu | exclu | `classified6_sound` `:100` |
| `store`, `alloc`, `issue` (3) | contre-exemple | **exclu** | `classified6_sound` ; `ControlOf` gardé par `cex_ctl_same` `:63` |
| `release`, `endUse` (2) | fin de vie | fin de vie | propriété `exclu` par `classified6_sound` ; témoins `Run6` : `ends_run6` (`Classify6Witness.lean:36`) |
| `newMutex`, `acquire`, `unlock`, `resetLock` (4) | protocole | protocole | `proto_touch` (inchangé) |
| `transfer`, `spawn` par valeur (2) | déplacement | déplacement | témoins `Run6` : `moves_run6` (`Classify6Witness.lean:27`) ; sous l'hypothèse 3, ne touchent pas le contrôleur (`transfer_fixed_sound`, `spawnVal_fixed_sound`) |

Bilan : 20 exclus, 2 en fin de vie, 4 de protocole, 2 en déplacement, **aucun contre-exemple**, conformément à l'attendu. 20 + 2 + 4 + 2 = 28.

**Ce qui est la restriction elle-même et ce qui est prouvé.** Sous `Run6`, « l'empreinte élargie ne contient pas le contrôleur » est la restriction elle-même (C22 point 4 proposé, `restr_not_touch` `:48`). C'est l'amendement, pas un résultat, pour tous les genres non-protocole et non-déplacement, et en particulier pour `store`, `alloc`, `issue` et `depend`. Ce qui est prouvé, c'est que `ControlOf` est gardé :
- `classified_sound` pour les 19 genres exclus ou en fin de vie de la passe précédente ;
- `cex_ctl_same` pour `store` et `alloc` (`kernel_ctl_same`) et pour `issue` (`split` puis `store`, avec `AdminSep` pour le `split`).

### Statut des énoncés

| Énoncé | Statut | Théorème | Hypothèses exactes |
|---|---|---|---|
| Classification : pas exclu, fin de vie ou ancien contre-exemple, sous `Encap6` | prouvé | `classified6_sound` `:100` | pas `ok`, `Encap6` ; départ `KInvCA`, `SyncState`, `AdminSep` ; arrivée `WF3` ; entrée enregistrée, vivante avant et après |
| `spawn` par valeur sous l'hypothèse 3 (l'énoncé laissé ouvert) | **prouvé** | `spawnVal_fixed_sound` `:157` | pas `ok`, admis par `Encap5R` (seul C22.3 sert) ; départ `KInvCA`, `SyncState` ; entrée enregistrée et vivante après ; `ControlOf` identique avant et après |
| Complétude sans restriction de genre | **prouvé** | `completeness6` `:218` | pas `ok`, `Encap6` ; entrée vivante avant et après ; `ControlOf` identique avant et après. `KInvCA` et `SyncState` au départ ne servent qu'aux déplacements. |
| La même chose sur une `Run6` depuis l'état initial, sous l'hypothèse 3 (`CtlFixed`) | **prouvé** | `completeness6_run` `:274` | `DDSound`, statiques bien formées ; les invariants viennent de `trace_inv` |
| Instance sur `lc_trace` | obtenue | `lc_complete6` (`Classify6Witness.lean:43`) | `lc_run6`, `CtlFixed` de `lc_bridge` |

**Preuve de `spawnVal_fixed_sound`, sans suivre le contrôleur à travers les phases.**
- Si le contrôleur était une feuille d'une source de transfert, il serait `Moved` à la fin (`transfers_moved` `:127`) :
  - chaque phase rend ses feuilles sources `Moved` et ses seules feuilles destinations `Init` (Spec 1 §63, effet) ;
  - toutes les destinations sont des locaux neufs du fils, d'indice au moins `|P|`, et ne contiennent donc pas le contrôleur.
- Or `spawnVal_syncState` donne `SyncInv` après le pas, et C21 point 7 rend `Init` le contrôleur d'une entrée vivante.
- Le transport des empreintes passe par `footprint_shapeP` pour la création des locaux et `footprint_transferEffC` (`:119`) pour chaque phase.

**Preuve de `completeness6`.** La restriction donne trois cas :
- un pas du protocole de `e` : c'est un événement ;
- un déplacement admis : exclu sous l'hypothèse 3 (`move_not_touch` `:192`) ;
- l'entrée morte après le pas : contradiction.

Un pas du protocole d'une autre entrée qui toucherait le contrôleur de `e` est refusé par la restriction elle-même : `SyncInv` n'y sert plus.

## Nécessité de la clause sur les dépendances

Aucune preuve de cette passe n'a besoin que `depend` vers le contrôleur soit exclu, sauf `completeness6`, et seulement parce que son empreinte (`TouchesX`) contient par définition la place `result` d'un `depend`.

Avec l'empreinte `Touches` de la passe précédente, `depend` est dans `ExclKind`, et `classified_sound` et `completeness` le couvrent sur `Run5R`, sans la clause. Le graphe du contrôleur, l'invariant, la cohérence et le pont ne lisent pas `D`. `depend(lock, a)` est un pas admis par `Encap5R` qui ne change aucun événement du graphe (`depend_refused`).

**Cette exclusion est donc sans témoin de nécessité**, comme le corpus l'annonçait : `depend` ne crée aucun accès physique (C27).

## Tâche 5 — `resetLock` amendé (`MutexReal/ResetAmend.lean`)

| Cas | Attendu (corpus § 2 decies) | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| W-RC, pas 4, `c0 (f1) : resetLock(e)` | aucune issue `ok` ; C18 point 4 proposé défaillant | aucune issue `ok` ; `ResetLockOk` (C18.1–C18.3) tient, `CtrlRight` échoue | C18 point 4 proposé | `W_RC_4_amended_reject` `:29` |
| jumeau de W-RC, `c0 (f0)` depuis `MX₃` | `ok` | `ok` | C18 amendé | `W_RC_twin_amended_ok` `:39` |
| W-RL, `resetLock(e)` | `ok`, inchangé | `ok` | idem | `W_RL_amended_ok` `:44` |
| W-RL-J, `resetLock(e)` | `ok`, inchangé | `ok` | idem | `W_RLJ_amended_ok` `:49` |
| jumeau positif de S11, `resetLock(e)` | `ok`, inchangé | `ok` | idem | `S11_4_amended_ok` `:54` |
| W-RL et W-RL-J sont des exécutions amendées ; W-RC est une `Run6` mais pas une exécution amendée | — | obtenu | — | `amended_runs` `:59` |

| Énoncé | Statut | Théorème | Hypothèses exactes |
|---|---|---|---|
| Un pas `acquire(i)`, `unlock(i)` ou `resetLock(i)` par `c`, `ok` et satisfaisant `AmCond`, est fait par une frame qui a, par une autorité exerçable en `Observe`, un mode effectif présent sur `ControlOf(i)` (`CtrlRight`) | prouvé | `protocol_authority` `:74` | `LStep` et `AmCond`. Pour `acquire` et `unlock`, `AmCond` est vide : C14.3 et C17.4 sont dans la relation de pas. Pour `resetLock`, c'est la clause amendée. |
| La même chose dans une exécution amendée | prouvé | `runAm_protocol_authority` `:93` | `RunAm` |

Sans l'amendement 2, l'énoncé est faux pour `resetLock` : W-RC est une `Run6` dont le pas 5 est fait depuis `f1`, sans droit sur `lock`.

## Tâche 6 — témoin W-NC (`Corpus/NewMutexRight.lean`)

| Pas | Attendu (corpus) | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| 1. `c0 : s := derive(root_M, Modify, {slot})` | `ok` | `ok` (états de W-RC, registre vide) | O1 | `W_NC_12_ok` `:26` |
| 2. `c0 : enterFrame f1` cédant `s` | `ok` ; aucune autorité exerçable depuis `f1` n'a de mode effectif présent sur `lock` | obtenu, pour les deux modes | O6 | `W_NC_12_ok` `:26` |
| 3. `c0 (f1) : newMutex(guarded)` | **`ok`** | **`ok`** ; `ExercisableAt(guarded, Modify)` depuis `f1` par la troisième clause de §43 | C13.1–C13.10 | `W_NC_3_ok` `:37` |
| jumeau : étape 3 du bloc MX depuis `f0` | `ok` | `ok` | C13 | `W_NC_twin_ok` `:43` |
| trace | — | `Run5R` et `Run6` depuis l'état initial | — | `W_NC_run` `:57` |

**Verdict.** La frame `f1`, sans aucune autorité sur `lock`, construit l'entrée dont `lock` est le contrôleur, et l'écriture initiale non atomique du contrôleur (C31, C48) lui est attribuée. C13 n'a pas de clause d'accès au contrôleur, contrairement à C14 point 3 et C17 point 4.

La question est à arbitrer, comme l'annonce le corpus. Aucun amendement de C13 n'est testé, et la variante à deux contextes du corpus n'est pas construite.

## Ce dont dépend encore la lecture du graphe comme histoire complète du contrôleur

Sous `Run6` et l'hypothèse 3, la complétude vaut sans restriction de genre (`completeness6_run`). Elle dépend encore de cinq points :
1. **L'amendement 1 lui-même**, proposé et non validé : sans lui, les trois contre-exemples restent (`store_cex`, `alloc_cex`, `issue_cex`).
2. **L'hypothèse 3**, pour les déplacements. Sans elle, W-TR est une `Run6` dont le contrôleur change de feuille.
3. **Les pas où l'entrée n'est pas vivante**, avant `newMutex(e)` ou après sa mort, qui sont hors de l'énoncé. Pour `newMutex(e)` lui-même, W-NC montre qu'il peut venir d'une frame sans droit sur le contrôleur (hypothèse 4).
4. **Ce que le modèle ne représente pas** (`OB-C20`) : les accès internes des réalisations composées, et la désallocation au niveau des octets au-delà des feuilles qui meurent. Les métadonnées du fournisseur d'un `alloc` sont dans l'empreinte (`Touches`) mais sans effet dans le modèle.
5. **Les tentatives échouées et les marqueurs internes** (hypothèses 5 et 6).

L'amendement 2 ne change pas le graphe : il ajoute seulement l'autorité des pas `resetLock`.

## Questions pour l'arbitre

1. **W-NC** : `newMutex` sans droit sur le contrôleur est `ok`. Faut-il une clause d'accès au contrôleur dans C13 ?
2. **Empreinte de `depend`** : la place `result` elle-même (choix retenu) ou ses feuilles ? Le cas concret est `depend(M, a)`.
3. **Clause sur les dépendances** : elle n'a pas de témoin de nécessité. Faut-il la garder dans l'amendement 1 ?

## Audit final des axiomes (après la passe corrective)

- **Méthode.** La liste des théorèmes `Ern.Concurrency*` et `_private.Ern.Concurrency*` est extraite après `import Ern` et comparée par différence d'ensembles à celle de `83b6adf`. `collectAxioms` est appliqué à chaque théorème.
- **Résultat.** 2395 théorèmes, dont 1590 non internes. Aucun axiome hors `{propext, Quot.sound}`. Aucun nom retiré et aucun nom réattribué à un autre module.

| Module nouveau | Théorèmes nouveaux | dont non internes |
|---|---|---|
| `MutexReal.Amend` | 28 | 7 |
| `MutexReal.AmendWitness` | 8 | 8 |
| `MutexReal.NonRegression` | 19 | 19 |
| `MutexReal.Classify6` | 30 | 20 |
| `MutexReal.Classify6Witness` | 3 | 3 |
| `MutexReal.ResetAmend` | 8 | 8 |
| `Corpus.NewMutexRight` | 4 | 4 |
| **Total** | **100** | **69** |

- **Somme.** 2295 + 100 = 2395, et 1521 + 69 = 1590.
- **Build.** `lake build` réussit (112 jobs), sans avertissement.
- **Contrôles.** Le `grep` d'`AGENTS.md` est vide, et aucun `noncomputable` n'est utilisé.
