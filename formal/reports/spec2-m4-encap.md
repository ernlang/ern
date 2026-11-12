# Spec 2, jalon 4, tranche 3 — encapsulation complète (C22 point 6)

Formalisation exploratoire, jamais mergée. Branche `formal/spec2-m4`, rien n'est poussé.

## Sources

- **WC5.2** (`ERN_Concurrency_Model_WC5.2.md`, version retouchée). Clauses lues pour cette passe :
  - C1 à C8, C12 à C18 et C21 à C25 ;
  - C43 à C46, `OB-C28`, choix de rédaction 10.
- **Spec 1** (`specs/ERN_Memory_Model_Specification_v0.1.md`). Paragraphes lus :
  - §36, §43 ;
  - §60 à §65, §69 à §78 (§73 en entier).
- **Corpus** : `corpus-spec2-m3.md` v13, § 2 duodecies.
- **Rapports précédents** : `spec2-m4-handoff.md` (§ Extension aux droits sur les places), `spec2-m4-mutexreal.md`.

Code : `formal/Ern/Concurrency/FullEncap/`, sept modules, tous importés dans `formal/Ern.lean`. Aucune définition ni aucun théorème existant n'est modifié. Rien n'est changé dans `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md` ni `formal/Ern/MemoryModel/`.

## Résumé

| Tâche | Résultat |
|---|---|
| 1 | Inventaire des prémisses de droit des 28 genres (`Prem`) et de leurs formes sans `guarded` (`PremG`). Chaque forme entraîne sa prémisse ; chaque prémisse est lue par la relation de pas ; toute `RunFull` est une exécution amendée finale. Exhaustivité établie par un parcours mécanique des définitions et par relecture. |
| 2 | Tous les faits attendus de W-GI et W-RX sont obtenus. Aucun pas attendu `ok` n'est refusé par le noyau. |
| 3 | Les 24 exécutions amendées finales du dépôt sont des `RunFull`. Les 22 genres qui ont une prémisse de droit admettent un pas `ok` sous une entrée vivante ; `deriveSync` brut n'est jamais admis. |
| 4 | Prouvé pour 11 genres, et pour `endUse` et `free` sur la place nommée. Sans objet pour 12 genres. Une seule exception, les feuilles qui meurent (`endUse`, `free`, `exitFrame`, `terminate`), avec un témoin par genre. Pour `spawnVal`, prouvé dans l'état de chaque phase, inachevé dans l'état d'avant le pas. Aucun contre-exemple. |
| 5 | **Réfuté**, aussi sur `RunFull` : un grant abandonné par sortie de frame, dont un dérivé survit dans un contexte enfant. Sur `Run7`, W-GI et W-RX A le réfutent. Il tient à chaque pas des 30 autres traces `RunFull` du dépôt. |
| 6 | Prouvé. La condition de chaîne est posée par la forme sans `guarded` ; le droit sur le `slot` découle de `SyncInv`. |

## Commits

| Commit | Tâche | Contenu |
|---|---|---|
| `67d4a3b` | 1 | `Inventory.lean` : `Prem`, `PremG`, `EncapFull`, `RunFull`, implications |
| `d1dc18c` | 2 | `Witness.lean` : W-GI, W-RX, `resetLock(e)` de W-RL |
| `ca574e0` | 3 | `NonRegression.lean` : 24 traces, usages sous entrée vivante, `deriveSync` |
| `6352245` | 4 | `Capacity.lean`, `CapacityWitness.lean` |
| `1563e4d` | 5 | `Protected.lean` : réfutations |
| `3175c17` | 6 | `ResetException.lean` |
| `4446f59` | 5 | `Protected.lean` : balayage des traces `RunFull`, W-RX A |
| `197f5bc`, `81e53eb` | 5 | docstring de `protected_runFull_refuted` (une affirmation non vérifiée retirée ; ligne rewrappée) |

Les numéros de ligne ci-dessous sont ceux de `81e53eb`.

## Définitions ajoutées

Toutes sont dans `Ern.Concurrency.FullEncap`. La forme sans `guarded` remplace `ExercisableAt` par `Exer5` (`Encap5C`), lu depuis la frame courante du contexte, avec le registre du pas, dans l'état où la précondition lit la prémisse.

| Nom (module:ligne) | Rôle |
|---|---|
| `Prem` (`Inventory:262`) | l'inventaire : pour chaque genre, la conjonction de ses prémisses de droit, sous leur forme d'origine |
| `PremG` (`Inventory:314`) | les mêmes prémisses sous leur forme sans `guarded` |
| `GroundsG` (`:53`), `OutsideG` (`:160`), `EndAccessG` (`:170`), `FreeAccessG` (`:179`) | clauses `Grounds` (§63.4, §69.2, §70.3) |
| `HolderRightG` (`:69`) | §62.2 ; cas frame : la frame courante, comme `HolderRight` |
| `MetaRightG` (`:106`) | §36 ; `False` si la valeur d'arena n'existe pas, comme `MetaRight` |
| `NewMutexRightG` (`:124`) | C13 point 11 |
| `ResetExerG` (`:149`) | C18 point 1 avec l'exception de C22 point 6 |
| `AuthG` (`:190`) | `SyncAuthorized` (C14 points 1 à 3, C15 point 3) |
| `ValRightsG` (`:200`) | phases de transfert du `spawn` par valeur (C5.2) |
| `issueMid` (`:217`), `resetMid` (`:222`) | états intermédiaires d'`issue` et de `reset` |
| `EncapFull` (`:364`) | `Encap7 ∧ PremG` |
| `RunFull` (`:370`) | exécution dont chaque pas satisfait `EncapFull` et est un pas `ok` |
| `CapReq` (`Capacity:40`) | mode exigé sur une feuille touchée (tâche 4) |
| `VoidKind` (`Capacity:195`) | genres sans objet (tâche 4) |
| `PhaseCap` (`Capacity:216`) | capacité sur les sources, phase par phase (tâche 4) |
| `CapFromGrant` (`Protected:37`) | capacité issue du sous-arbre du grant (tâche 5) |
| `ProtectedOK` (`Protected:51`), `ProtectedRun` (`:134`) | le corollaire de la tâche 5, pour un pas et pour une trace |
| `ResetRights` (`ResetException:42`) | les droits de la tâche 6 |

### Choix d'encodage et écarts au brief

1. **Lectures négatives.** `ParamOriginHidden` (§72.3, C4 point 5) lit `ExercisableAt` sous une négation : l'origine ne doit être exerçable dans aucun mode. Ce n'est pas un droit sur lequel repose le pas. La relire avec `Exer5` affaiblirait la prémisse, et la forme n'entraînerait plus l'original, ce que la tâche 1 exige. Ces champs (`enterFrame`, `spawn`, `spawnVal`) figurent dans la table, non substitués. `¬ ExercisableAt` entraîne `¬ Exer5` : la forme substituée est donc impliquée par la précondition du noyau, et `RunFull` est la même avec ou sans elle. Aucun programme accepté ne change.
2. **Formes miroirs.** `HolderRightG` et `MetaRightG` reprennent exactement `HolderRight` et `MetaRight`. Elles diffèrent donc de `HolderRight5` (cas frame `True`) et de `MetaRight5` (`True` si la valeur est absente), pour que chaque forme entraîne sans condition sa prémisse.
3. **Exception de `resetLock`.** C18 point 1 est relu comme `Exer5` sur le registre privé de l'entrée réinitialisée (`reg.eraseIdx i`).
   - Le sujet `guarded` et toute la chaîne de détenteurs sont testés contre les autres entrées vivantes.
   - Le `guarded` de l'entrée elle-même reste permis dans la chaîne du `slot`, selon la lettre de C22 point 6 (« no other live entry's `guarded` »).
   - L'exclusion se fait par position dans le registre : une autre entrée de même identité `guarded` exclurait encore. Cela n'arrive que sur des états où C21 point 4 (`SyncInv.unique`) est faux.
   - C18 point 4 garde le registre entier, l'exception ne visant que le contrôle de C18 point 1.
4. **Clauses amendées.** `RunFull` est définie pas à pas, sans `AmCondF` explicite. Les formes sans `guarded` de C13 point 11 et de C18 point 4 entraînent les clauses amendées : `runFull_runAmF` prouve l'inclusion.
5. **`acquire`.** L'autorisation de `deriveSync` interne (C15 point 3) est un existentiel sur les entrées du registre, distinct de C14 point 3 sur l'entrée `i`. Les deux sont inventoriés.
6. **`reset`.** Le pas du modèle (`ResetD`) ne lit pas `MetaRight` (§78.1). Il exerce `internal` par le `derive` interne (écart 12 du rapport `spec2-m4-handoff.md`). §78.1 n'est donc pas dans `Prem` ; `Encap7` garde `MetaRight5` par `PlaceExcl`.
7. **`issue`.** §77.6 (`IssueArrival.keepsDst`) n'est pas lu par `IssueStepC`. Son équivalent dans le modèle est §65.5 du `store` interne, inventorié.
8. **Registre des états intermédiaires.** C'est celui du pas ; la vivacité des entrées est lue dans l'état intermédiaire.

## Tâche 1 — Inventaire et inclusions

### Table de l'inventaire

L'état de lecture d'une prémisse est l'un des suivants :

- « avant » : l'état du pas ;
- « intermédiaire » : l'état produit par la phase précédente d'un pas composé ;
- « résultant » : l'état produit par l'effet ;
- « phase » : l'état au début de la phase de transfert, C5.2.

La dernière colonne indique si la prémisse était déjà couverte par `ChainExcl` ou par `PlaceExcl`.

| Genre | Clause | Champ du modèle | État | Déjà couvert |
|---|---|---|---|---|
| `derive` | §60.1 | `DerivePre.exercisable` | avant | `ChainExcl` |
| `split` | §61.1 | `SplitPre.exercisable` | avant | `ChainExcl` |
| `release` | §62.2 | `ReleasePre.holderRight` | avant | `PlaceExcl` (`HolderRight5`, cas frame `True`) |
| `transfer` | §63.1 | `TransferPreC.srcRight`, `.dstRight` | avant | `PlaceExcl` |
| `transfer` | §63.4 | `TransferPreC.noOutsideDerived` (`Grounds`) | avant | non |
| `depend` | §64.1 | `DependPreC.right` | avant | `PlaceExcl` |
| `enterFrame` | §72.3 | `EnterPreC.originHidden` (négatif) | résultant | non substitué |
| `exitFrame` | — | aucune | — | — |
| `read3` | §66.2 | `Read3Pre.exercisable` | avant | `ChainExcl` |
| `write3` | §67.1 | `Write3Pre.exercisable` | avant | `ChainExcl` |
| `writeShared` | §68.2 | `WriteSharedPre.exercisable` | avant | `ChainExcl` |
| `pin` | §74 | `PinPre.right` | avant | `PlaceExcl` |
| `unpin` | §75 | `UnpinPre.right` | avant | `PlaceExcl` (`True` si l'obligation est absente) |
| `endUse` | §69.1 | `EndUsePre.right` | avant | `PlaceExcl` |
| `endUse` | §69.2 | `EndUsePre.access` (`Grounds`) | avant | non |
| `free` | §70.3 | `FreePre.right` | avant | `PlaceExcl` |
| `free` | §70.3 | `FreePre.access` (`Grounds`) | avant | non |
| `alloc` | §71.2 | `AllocStatic.providerRight`, y compris l'exercice de la branche §68 | avant | `PlaceExcl` |
| `alloc` | §71.3 | `AllocStatic.ownerRight` | avant | `PlaceExcl` |
| `store` | §65.2 | `StorePreC.right` | avant | `PlaceExcl` |
| `store` | §65.5 | `StorePreC.keepsTarget` | résultant | `PlaceExcl` |
| `spawn` | C4 point 5, §72.3 | `SpawnPre.originHidden` (négatif) | final | non substitué |
| `terminate` | — | aucune | — | — |
| `join` | — | aucune | — | — |
| `deriveSync` brut | C15 point 3, C14 points 1 à 3 | `DeriveSyncPre.authorized` (`LibSyncAuthorized`, `EntryAuth`, `CtrlRight`) | avant | non |
| `newMutex` | C13 point 2 | `NewMutexPre.exercisable` | avant | non |
| `newMutex` | C13 point 11 | `NewMutexRight` (clause amendée, `AmCondF`) | avant | non |
| `acquire` | C14 point 3 | `AcquireOk`, `EntryAuth`, `CtrlRight` | avant | `PlaceExcl` (`CtrlRight5`) |
| `acquire` | C15 point 3 | `DeriveSyncPre.authorized` de `deriveSync` interne | avant | non |
| `unlock` | C17 point 2 (§62.2) | `UnlockOk`, `ReleasePre.holderRight` du grant | avant | non |
| `unlock` | C17 point 4 | `UnlockOk`, `CtrlRight` | avant | non |
| `resetLock` | C18 point 1 | `ResetLockOk`, `ExercisableAt(guarded)` | avant | non (exception de C22 point 6) |
| `resetLock` | C18 point 4 | `CtrlRight` (clause amendée, `AmCondF`) | avant | non |
| `spawnVal` | C5.2, §63.1 | `ValTransferPre.srcRight` | phase | `PlaceExcl` (`ValRights5`) |
| `spawnVal` | C5 point 4, §63.4 | `ValTransferPre.noOutsideDerived` (`Grounds`) | phase | non |
| `spawnVal` | C4 point 5, §72.3 | `SpawnValPre.originHidden` (négatif) | final | non substitué |
| `newArena` | §76.1 | `NewArenaPreC.storageRight` | avant | non |
| `newArena` | §76.2 | `NewArenaPreC.exercisable` | avant | non |
| `issue` | §77.1 | `IssueStatic.metaRight` | avant | `PlaceExcl` (`True` si la valeur est absente) |
| `issue` | §77.2 | `IssueStatic.dstRight` | avant | non |
| `issue` | §61.1 | `SplitPre.exercisable` du `split` interne | avant | non |
| `issue` | §65.2 | `StorePreC.right` du `store` interne | intermédiaire (`issueMid`) | non |
| `issue` | §65.5 | `StorePreC.keepsTarget` du `store` interne | résultant du `store` | non |
| `reset` | §60.1 | `DerivePre.exercisable` du `derive` interne | avant | non |
| `reset` | §62.2 | `ReleasePre.holderRight` du `release` interne | intermédiaire (`resetMid`) | non |

### Énoncés

| Énoncé | Théorème | Statut | Hypothèses |
|---|---|---|---|
| chaque forme sans `guarded` entraîne la prémisse d'origine | `premG_prem` (`Inventory:403`) | prouvé | aucune |
| chaque prémisse de l'inventaire est lue par la relation de pas | `prem_of_step` (`Inventory:568`) | prouvé | `LStep` et `AmCondF` (les deux clauses amendées ne sont pas dans `LStep`) |
| les formes sans `guarded` contiennent les clauses amendées | `amCondF_of_premG` (`:508`) | prouvé | aucune |
| toute `RunFull` est une exécution amendée finale | `runFull_runAmF` (`:528`) | prouvé | aucune |
| toute `RunFull` est une `Run7` | `runFull_run7` (`:522`) | prouvé | aucune |

### Exhaustivité de l'inventaire

- **Mécanique.** Un méta-programme Lean (scratchpad, `ScanRights.lean`, texte en annexe) parcourt, depuis chaque constructeur de `LStep`, toutes les constantes atteintes à travers les définitions, les inductifs et les champs des structures. Il signale chaque champ dont le type atteint `ExercisableAt`, `HasRight`, `HolderRight`, `CtrlRight`, `MetaRight`, `Grounds` ou `NewMutexRight`.
  - Résultat : toute occurrence atteinte est un champ de la table, ou `ParamOriginHidden`.
  - `exitFrame`, `terminate` et `join` n'atteignent aucune de ces constantes.
- **Relecture des définitions.** Le parcours n'établit pas, et la relecture établit, que :
  1. `ParamOriginHidden` est une lecture négative ;
  2. dans `IssueStepC`, `opStepC` n'est appelé que pour `split` et `store` (le parcours sur-approxime en suivant toutes les opérations) ;
  3. les prémisses de `AcquireOk`, `UnlockOk` et `ResetLockOk` sont bien celles de la table (ce sont des définitions, pas des structures ; le parcours n'en isole pas les champs) ;
  4. aucune autre définition ne réimplante ces lectures sous un autre nom.
- **Clauses amendées.** C13 point 11 et C18 point 4 sont dans `AmCondF`, hors de `LStep` : le parcours ne les atteint pas. Elles sont ajoutées par lecture de `AmCondF`.
- **États de lecture.** Ils sont vérifiés par `prem_of_step` : chaque prémisse de `Prem`, dans l'état où `Prem` la place, est déduite de la relation de pas.

## Tâche 2 — Témoins (corpus § 2 duodecies)

### W-GI

**Mise en place.** Statiques `gist` : bloc MX sans `M′`, `T` (place 3) feuille `t` possédée par `M`. Une arena libre de `f0` : `ST0` (4), de feuilles `R1` (5) et `R2` (6), et la valeur d'arena `AV0` (7). Contrat `KM`, layout `L0`. Les étapes :

1. `internal0 := derive(root_ST0)`, puis `store(internal0, AV0)` et `newArena` ;
2. `guarded := derive(root_T)`, puis `store(guarded, slot)` et `newMutex` ;
3. `o := derive(root_M, Observe, {lock})`, puis `spawn c1` cédant `o`.

| Fait | Attendu | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| pas 1, `c0 : issue(arena0, R1, t)` sans grant | `ok` noyau | `ok` | §77.1 par `root_AV0` ; §77.2 et §77.6 par `guarded` sous `root_M` | `W_GI_1_ok` (`Witness:112`) |
| pas 2, `c1 : acquire(e)` | `ok` | `ok` | C14 points 1 à 3 par `o` ; C15 | `W_GI_2_ok` (`:118`) |
| pas 3, `c1 : read3(t)` via `g₁` | `ok` | `ok` | O9 | `W_GI_3_ok` (`:123`) |
| pas 1 sous l'encapsulation actuelle | admis | la trace est une `RunAmF` depuis l'état initial | `Encap7` ne lit pas le droit sur la destination | `W_GI_current` (`:146`) |
| pas 1 sous l'encapsulation complète | exclu | `¬ PremG` | voir ci-dessous | `W_GI_1_excluded` (`:153`) |
| jumeau : `acquire(e)`, `issue(arena0, R1, t)`, `unlock(e)` par `c0` | `ok` et admis | `RunFull` depuis l'état initial | le droit sur `t` repose sur `g₀` | `W_GI_twin` (`:189`) |

Détail de l'exclusion du pas 1 :

- tiennent sans `guarded` vivant :
  - `MetaRightG` sur `AV0` ;
  - l'exercice d'`internal0` ;
- échouent, car elles ne passent que par `guarded` :
  - `HasRight5(t)` avant le pas (§77.2) ;
  - `HasRight5(t)` dans l'état intermédiaire (§65.2) ;
  - `HasRight5(t)` dans l'état résultant du `store` (§65.5) ;
- `HasRight(t)`, lu sur la vue du noyau, tient.

La trace n'est pas une `RunFull`.

### W-RX

**Encodage.** Statiques `rxst` :

- `M` (0) = {`slot` (1), `lock` (2)} ;
- `T` (3), possédée par `M`, n'est pas une feuille : sa partie `N` (4) = {`slot_n` (5), `lock_n` (6)} ;
- `U` (7), possédée par `N`, est la donnée de l'entrée `e_n`.

« `T` contient `N` » est encodé par `N` partie de `T`. Contrat `KX = KC [2, 6]`, les deux contrôleurs étant `SharedMutable` (C13 point 6).

**Mise en place.** `guarded_n := derive(root_U)`, `store(guarded_n, slot_n)`, `newMutex` (entrée `e_n`, indice 0), puis `guarded := derive(root_T)`, `store(guarded, slot)`, `newMutex` (entrée `e`, indice 1). Aucun grant.

| Fait | Attendu | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| mise en place emboîtée | acceptée | acceptée ; `ControlOf(e_n) = lock_n`, `ControlOf(e) = lock` ; deux entrées vivantes | C13 | `W_RX_setup` (`Witness:274`) |
| A, `c0 : resetLock(e_n)` sans le grant de `e` | `ok` noyau | `ok` ; C18 point 4 (`AmCondF`) tient par `guarded` | C18 points 1 à 4 ; troisième clause de §43, deux fois | `W_RX_A_ok` (`:284`) |
| A sous l'encapsulation actuelle | non dit par le corpus | **obtenu** : la trace est une `RunAmF` depuis l'état initial | rien dans `Encap7` ne lit le droit de C18 point 1 | `W_RX_A_current` (`:291`) |
| A sous l'encapsulation complète | exclu | `¬ ResetExerG` et `¬ CtrlRight5` : les deux formes échouent | C22 point 6 : la chaîne du droit sur `slot_n`, et celle de l'accès à `lock_n`, contiennent `guarded`, le `guarded` vivant de `e` | `W_RX_A_excluded` (`:300`) |
| B, `c0 : acquire(e)` puis `c0 : resetLock(e_n)` | `ok` et admis | `RunFull` depuis l'état initial | les droits sur `slot_n` et `lock_n` reposent sur `g` ; seul `guarded_n` est exempté | `W_RX_B` (`:319`) |
| `resetLock(e)` de W-RL | admis | `PremG` au pas 9 ; la trace est une `RunFull` | droit sur `slot` par `root_M` | `W_RL_full` (`:331`) |

## Tâche 3 — Non-régression et usages légitimes

### Exécutions amendées finales du dépôt

Liste établie par un grep complet des énoncés `Run7` et `RunAmF` de `formal/Ern/Concurrency`. Les 24 sont des `RunFull`, les formes sans `guarded` étant vérifiées par `decide` à chaque pas (`runAmF_traces_full`, `NonRegression:30`) :

- W-HO, W-HO′, W-HO″, W-HO-J, W-HO″-J ;
- `lc_trace`, W-RL₀, W-RL, W-RL-J, W-TR, W-TR-J, S11 ;
- le déplacement par valeur (`cv`), la fin d'usage (`ce`), le `release` (`cr`) ;
- le jumeau de W-GS, S3, S10 ;
- les jumeaux `store`, `issue`, `alloc` et `depend` de la passe corrective ;
- `alloc(owner = M)` et `depend(lock, a)` de la passe finale.

Hors liste, et ce n'est pas une régression :

- W-RC et W-NC ne sont pas des exécutions amendées finales ;
- les contre-exemples `store`, `issue`, `alloc` (dont le fournisseur `M`) ne sont pas des `Run7` ;
- W-GI (`W_GI_current`) et W-RX A (`W_RX_A_current`) sont des `RunAmF` qui ne sont pas des `RunFull`, comme l'attend le corpus.

Aucune trace existante n'est refusée.

### Usages légitimes sous une entrée vivante

Une nouvelle trace, `lvσ` (`NonRegression:132`), est une `RunFull` depuis l'état initial, l'entrée `e` étant vivante avant chaque pas à partir de l'indice 3 (`lv_full`, `NonRegression:169`).

- **Statiques et contrat.** Statiques de W-GI, plus `Y` (8) et `P` (9). Contrat `KC [2, 8]`.
- **Droits.** Ils reposent sur des racines de `f0` ou sur le bloc issu du `split` ; aucun ne passe par `guarded`.

| Genre | Pas | Trace (indice) | Théorème |
|---|---|---|---|
| `derive` | `derive(root_ST0)` | `lvσ` (3) | `lv_full` |
| `store` | `store(internal0, AV0)` | `lvσ` (4) | `lv_full` |
| `newArena` | `newArena(ST0, internal0)` | `lvσ` (5) | `lv_full` |
| `reset` | `reset(arena0)` | `lvσ` (6) | `lv_full` |
| `split` | `split(root_Y, [[Y]])` | `lvσ` (7) | `lv_full` |
| `read3` | `read3(Y)` via le bloc | `lvσ` (8) | `lv_full` |
| `writeShared` | `writeShared(Y)` via le bloc | `lvσ` (9) | `lv_full` |
| `release` | `release(bloc)` | `lvσ` (10) | `lv_full` |
| `pin` | `pin(Y)` | `lvσ` (11) | `lv_full` |
| `unpin` | `unpin(0)` | `lvσ` (12) | `lv_full` |
| `alloc` | `alloc(P, Y)` | `lvσ` (13) | `lv_full` |
| `free` | `free` de la racine allouée | `lvσ` (14) | `lv_full` |
| `endUse` | `endUse(Y)` | `lvσ` (15) | `lv_full` |
| `transfer` | `transfer(M, M′)` sous le grant | S10 (6) | `live_uses` (`NonRegression:179`) |
| `depend` | `depend(lock′, a)` | jumeau `depend` (4) | `live_uses` |
| `spawnVal` | déplacement de `M` | `cv` (3) | `live_uses` |
| `issue` | `issue(arena, R1, d1)` sous `g2` | S3 (9) | `live_uses` |
| `acquire`, `write3`, `unlock`, `resetLock` | pas de W-RL | W-RL (5, 6, 7, 9) | `live_uses` |
| `newMutex` | `newMutex(guarded)` avec `e_n` vivante | W-RX B (5) | `live_uses` |
| `deriveSync` brut | sans objet | — | `deriveSync_never_admitted` (`NonRegression:196`) |

Aucun `deriveSync` brut `ok` n'est admis par `Encap` : son autorisation nomme le `guarded` d'une entrée vivante (C14 point 1), que C22 point 2 exclut.

## Tâche 4 — Capacité exigée par l'empreinte

**Énoncé prouvé.** `capacity_run` (`Capacity:181`) : sur une `RunFull` depuis l'état initial, tout pas d'indice `i` et toute feuille `l` de `(σ i)` (une feuille existante, `l < |P|`) dans `TouchesF` satisfont `CapReq`. Hypothèses :

- `DDSound k`, `StaticsOK statics`, `σ 0` initial ;
- `RunFull k L σ lbls` ;
- `i < |lbls|`, `isLeaf (σ i).P l`, `l < |(σ i).P|`, `TouchesF L (σ i) lbls[i] l`.

`capacity_step` (`:97`) en est la forme par pas, sous `FramesC`. Le mode exigé est lu sur la clause du genre (`CapReq`, `:40`). C'est la généralisation de `cap5_sound_C`, réutilisé pour `read3`, `write3` et `writeShared`.

**Lecture de l'énoncé.** « Feuille » est pris au sens du brief : pour `alloc`, le propriétaire `ow`, compté comme place (`l = ow`), n'entre dans l'énoncé que s'il est une feuille.

| # | Genre | Feuilles existantes touchées | Mode exigé (clause) | Statut |
|---|---|---|---|---|
| 1 | `derive` | aucune | — | sans objet (`touchesF_void`, `:204`) |
| 2 | `split` | aucune | — | sans objet |
| 3 | `release` | aucune | — | sans objet |
| 4 | `transfer` | source et destination | `Modify` (§63.1) | prouvé |
| 5 | `depend` | aucune (`result` hors de `TouchesF`) | — | sans objet |
| 6 | `enterFrame` | places neuves seulement | — | sans objet |
| 7 | `exitFrame` | feuilles qui meurent | aucun (§73) | exception : feuilles qui meurent (`exc_exit`) |
| 8 | `read3` | ses feuilles | `Observe` (§66.2) | prouvé |
| 9 | `write3` | ses feuilles | `Modify` (§67.1) | prouvé |
| 10 | `writeShared` | ses feuilles | `Observe` (§68.2) | prouvé |
| 11 | `pin` | aucune | — | sans objet |
| 12 | `unpin` | aucune | — | sans objet |
| 13 | `endUse` | feuilles de la place, et feuilles qui meurent | `Modify` sur la place (§69.1) ; aucun sur les autres | prouvé sur la place ; exception : feuilles qui meurent (`exc_endUse`) |
| 14 | `free` | feuilles qui meurent | `Modify` sur la place (§70.3) ; aucun sur les autres | prouvé sur la place ; exception : feuilles qui meurent (`exc_free`) |
| 15 | `alloc` | fournisseur ; propriétaire s'il est une feuille | fournisseur : `Modify`, ou `Observe` et `SharedMutable` (branche §68) ; propriétaire : `Modify` (§71.3) | prouvé |
| 16 | `store` | cible | `Modify` (§65.2) | prouvé |
| 17 | `spawn` | places neuves seulement | — | sans objet |
| 18 | `terminate` | feuilles qui meurent | aucun (C7, §73) | exception : feuilles qui meurent (`exc_terminate`) |
| 19 | `join` | aucune | — | sans objet |
| 20 | `deriveSync` brut | aucune | — | sans objet ; jamais admis |
| 21 | `newMutex` | contrôleur | `Modify` (C13 point 11) | prouvé |
| 22 | `acquire` | contrôleur | `Observe` (C14 point 3, §68.2) | prouvé |
| 23 | `unlock` | contrôleur | `Observe` (C17 point 4) | prouvé |
| 24 | `resetLock` | contrôleur | `Observe` (C18 point 4) | prouvé |
| 25 | `spawnVal` | sources | `Modify` (C5.2, §63.1) | prouvé dans l'état de chaque phase ; inachevé dans l'état d'avant le pas |
| 26 | `newArena` | aucune | — | sans objet |
| 27 | `issue` | destination | `Modify` (§77.2) | prouvé |
| 28 | `reset` | aucune | — | sans objet |

Décompte des 28 genres :

| Statut | Genres | Nombre |
|---|---|---|
| prouvé | `transfer`, `read3`, `write3`, `writeShared`, `alloc`, `store`, `newMutex`, `acquire`, `unlock`, `resetLock`, `issue` | 11 |
| prouvé sur la place, exception ailleurs | `endUse`, `free` | 2 |
| prouvé par phase, inachevé avant le pas | `spawnVal` | 1 |
| exception | `exitFrame`, `terminate` | 2 |
| sans objet | les 12 autres | 12 |
| contre-exemple | — | 0 |

Les pas du protocole ne sont pas des exceptions : `CtrlRight5` et la forme de C13 point 11 donnent directement `cap5`.

### L'exception : les feuilles qui meurent

Les clauses de §69.1 et §70.3 n'exigent de droit que sur `place` ; §73 et C7 n'en exigent aucun. Une feuille possédée qui meurt avec le pas peut donc être touchée sans capacité. Ce n'est pas une hypothèse ajoutée : `CapReq` n'impose rien sur ces feuilles, et chaque genre a un témoin `RunFull` depuis l'état initial où le pas touche une telle feuille, protégée par une entrée vivante avant le pas et morte après, avec `cap5 = none`. Le `guarded` vivant n'est attribuable à aucun contexte (C43), et son origine n'a plus de mode effectif.

| Genre | Témoin | Feuille | Théorème |
|---|---|---|---|
| `endUse` | `endUse(M)` depuis `MX₃` | `t` de `T`, possédée par `M`, hors de `footprint(M)` | `exc_endUse` (`CapacityWitness:30`) |
| `free` | mutex dans un stockage alloué `R`, dont la donnée `T_r` est possédée par `R` ; `free(R)` | `T_r` | `exc_free` (`:82`) |
| `exitFrame` | mutex dans les locaux d'une frame appelée, donnée `X1` locale séparée ; `exitFrame` | `X1` | `exc_exit` (`:142`) |
| `terminate` | même mutex construit par un contexte enfant ; `terminate` | `X1` | `exc_terminate` (`:184`) |

### `spawnVal`

- **Prouvé.** `capacity_spawnVal` (`Capacity:252`) : au début de chaque phase de transfert, dans l'état de phase `t`, le contexte créateur a `cap5 = Modify` sur toute feuille de la source de la phase (`PhaseCap`, lu sur `t.P`).
- **Inachevé : la forme dans l'état d'avant le pas.** But restant : `Allows (cap5 (σ i).1 (σ i).2.1 c l) .modify`, pour `l ∈ footprint (σ i).1.P v.1`, à partir de `HasRight5 (t, reg) c .modify v.1` dans l'état de phase `t`.
  - Phase 1 : `t = spawnCreate (σ i).1 c ls`.
  - Phases suivantes : `t = transferEffC` des phases précédentes.
  - Il faudrait prouver que la chaîne `Exer5` du contexte créateur dans `t` n'utilise ni les racines des locaux de l'enfant, ni les autorités déplacées vers eux. On pourrait alors la relire dans l'état d'avant le pas. Ce lemme de transport n'est pas écrit.

## Tâche 5 — Donnée protégée

**Énoncé formalisé.** `ProtectedOK L st lbl st'` (`Protected:51`) dit : pour toute entrée du registre de `st` vivante dans `st` et dans `st'`, et toute feuille `l` de `footprint(guarded)` dans `TouchesF L st lbl`, `CapFromGrant` tient.

`CapFromGrant` (`:37`) lit « la capacité vient du sous-arbre du grant enregistré » ainsi :

- `cap5(c, l)` est présente ;
- elle est atteinte par une autorité attribuable à `c` sans `guarded` vivant, qui est le grant enregistré ou un de ses descendants ;
- « descendant » se lit sur la chaîne d'origine **courante** (`ancs`) ;
- `CapFromGrant` est faux si aucun grant n'est enregistré.

**Statut : réfuté**, sur `Run7` comme sur `RunFull`.

| Exécution | Contre-exemple | Théorème |
|---|---|---|
| `Run7` | W-GI, pas 1 : `issue` vers `t` sans grant ; `cap5(c0, t) = none` | `protected_run7_refuted` (`Protected:67`), le jumeau satisfaisant l'énoncé |
| `Run7` | W-RX A : `resetLock(e_n)` touche `lock_n`, feuille de `footprint(guarded)` de `e` vivante, sans grant enregistré | `protected_run7_refuted_rx` (`:146`) |
| `RunFull` | grant abandonné, voir ci-dessous | `protected_runFull_refuted` (`:112`) |

**La trace du grant abandonné** (`abσ`, `:99`), depuis `MX₃` :

1. `c0` dérive `o` (Observe sur `lock`) ;
2. `c0` entre dans une frame `f1` qui détient `o` ;
3. `c0 : acquire(e)` : le grant `g` est détenu par `f1` ;
4. `c0` dérive `x := derive(g, Modify, {T})` ;
5. `c0 : spawn` cède `x` à `c1` ;
6. `c0 : exitFrame`, sans `unlock` ;
7. `c1 : write3(T)` via `x`.

À la sortie de frame (Spec 1 §73.4 et effet `ok`, WC5.2 C6), `g` et `o` sont relâchées. `x` survit dans `c1`, et son origine est réancrée sur la première origine active survivante, `guarded`. Au pas 7 :

- l'entrée `e` est vivante avant et après le pas ;
- le grant enregistré `g` est inactif ;
- `ancs(x) = [guarded, root_T]` ;
- `cap5(c1, T) = Modify`, mais par `x`, hors du sous-arbre de `g`.

Chaque pas est admis par l'encapsulation complète.

Ce n'est pas un défaut d'encodage :

- C18 prévoit qu'un grant devienne inactif « through … frame exit without a corresponding `unlock` » ;
- §73 réancre explicitement les dérivés survivants, précise « Reanchoring may change the current `origin` relation », et renvoie la protection de la lignée historique d'un emprunt à une question différée ;
- C21 point 5 (`GrantSubtree`) ne parle que d'un grant actif.

**Balayage.** `ProtectedOK` tient à chaque pas de toutes les autres traces `RunFull` du dépôt : les 24 exécutions amendées finales, `lvσ`, le jumeau de W-GI, W-RX B et les quatre témoins de la tâche 4 (`protected_sweep`, `:161`). Dans ces témoins, l'entrée meurt avec le pas ; ils sortent donc de l'énoncé « avant et après ».

**Invariants en jeu.** Avec un grant actif, l'argument serait le suivant ; il n'est **pas formalisé** :

1. `x` est attribuable sans `guarded` vivant (`Attr5`, `NotGuarded`), donc `x` est distinct de `guarded` ;
2. I1 : `x` et `guarded` couvrent `l`, et `guarded` est de mode `Modify` (C21 point 1). `x` est donc un ancêtre ou un descendant de `guarded` ;
3. si `x` est un ancêtre, son mode effectif sur `l` est absent (§43.3), par le descendant actif `guarded` ;
4. si `x` est un descendant couvrant, `GrantSubtree` (C21 point 5) en fait `g` ou un descendant de `g` ;
5. avec `grant = none`, `GrantDiscipline` (C22) exclut tout descendant couvrant : un tel pas n'existerait pas.

Le contre-exemple montre que l'étape 4 manque quand le grant enregistré est inactif.

**Énoncé de remplacement, proposé et non prouvé.** Le choix revient au propriétaire, AGENTS.md interdisant d'ajouter une hypothèse pour obtenir une preuve. Trois candidats :

- (a) le même énoncé, sous l'hypothèse « grant absent ou actif » ;
- (b) « sous-arbre » lu sur la lignée historique (§73, question différée), ce qui demanderait de garder l'origine d'avant la réancre ;
- (c) un C21 point 5 amendé pour un grant inactif.

## Tâche 6 — Exception de `resetLock`

**Énoncé prouvé.** `resetLock_rights` (`ResetException:96`) : sur une `RunFull` depuis l'état initial, tout pas `resetLock(i)` par `c` satisfait `ResetRights`. Ce prédicat exige :

- un droit `Modify` sur le `slot` de l'entrée `i` ;
- un accès présent sur son contrôleur ;
- chacun par une chaîne de détenteurs qui ne contient le `guarded` d'aucune entrée vivante autre que `i`.

Hypothèses : `DDSound`, `StaticsOK`, `σ 0` initial, `RunFull`, `j < |lbls|`, `lbls[j] = .resetLock c i`.

**Posé et prouvé.**

- La condition de chaîne est posée par `ResetExerG` (C18 point 1).
- Ce qui est prouvé (`resetRights_of_premG`, `:56`) : l'exercice de `guarded` passe par la troisième clause de §43, donc par un droit sur le `slot`, parce que le `guarded` d'une entrée vivante est détenu par une place utilisable (C21 point 1, `SyncInv`, vrai sur les états atteints par `runFull_inv`).
- Le droit sur le contrôleur vient de `CtrlRight5` (C18 point 4), sans aucun `guarded` vivant, donc a fortiori sans celui d'une autre entrée (`exer5_of_sub`).

**Contrôle par `decide`** (`resetRights_witnesses`, `:109`) :

- W-RX B satisfait `ResetRights` ;
- W-RX A ne la satisfait pas ;
- le `resetLock(e)` de W-RL la satisfait.

## Ce qui est posé par définition et ce qui est prouvé

- **Posé par définition** (`PremG`) :
  - toutes les exclusions de la tâche 2 : W-GI pas 1, W-RX A ;
  - la condition de chaîne de la tâche 6 ;
  - le choix des états de lecture, contrôlé par `prem_of_step`.
- **Prouvé** :
  - l'implication des formes (`premG_prem`) ;
  - la lecture de l'inventaire par le pas (`prem_of_step`) ;
  - l'inclusion `RunFull ⊆ RunAmF` ;
  - la capacité de la tâche 4, à partir des formes sans `guarded`, de `FramesC` et des modes effectifs lus dans les préconditions (`effectivePresent`, `effectiveModify`, `WriteSharedPre.shared`) ;
  - l'existence du droit sur le `slot` (tâche 6, par `SyncInv`) ;
  - les réfutations de la tâche 5, et tous les verdicts des témoins, par `decide`.

## Pas attendus `ok` refusés, contre-exemples trouvés

- **Aucun pas attendu `ok` n'est refusé** par le noyau. Aucune trace existante n'est refusée par l'encapsulation complète.
- **Contre-exemple à l'énoncé de la tâche 5 sur `RunFull`** : le grant abandonné, ci-dessus.
- **Fait du corpus en conflit selon sa lecture.** Le corpus (§ 2 duodecies, « Donnée protégée ») dit « Aucun pas admis ne touche une feuille protégée par une entrée vivante sans que son contexte tienne une capacité sur cette feuille hors de toute chaîne passant par un `guarded` vivant ».
  - **Lecture littérale** (entrée vivante avant le pas) : les quatre témoins `exc_*` le contredisent.
  - **Lecture du brief** (vivante avant et après) : ils sortent du champ. Pour tous les genres autres que les quatre genres à feuilles qui meurent et `spawnVal`, le fait découle directement de `capacity_run`, qui donne `cap5` au moins `Observe` sur toute feuille existante touchée ; ce corollaire n'est pas énoncé comme théorème séparé. Il reste non prouvé pour ces cinq genres : aucun lemme général ne montre que l'entrée meurt quand une feuille protégée meurt.
  - Je ne tranche pas entre les deux lectures.

## Ce que `OB-C28` laisse ouvert après cette passe

1. L'application de la restriction dans l'interface sûre (Specs 4 et 10).
2. La bonne forme du corollaire de la donnée protégée (tâche 5) quand le grant enregistré est inactif ; décision du propriétaire.
3. La capacité de `spawnVal` dans l'état d'avant le pas (lemme de transport).
4. Le fait « Donnée protégée » du corpus pour les feuilles qui meurent, selon sa lecture.
5. §78.1 (`MetaRight` de `reset`), que le pas du modèle ne lit pas ; seul `PlaceExcl` le lit, sous la forme `MetaRight5`, `True` si la valeur d'arena est absente.
6. Les parties de l'exhaustivité établies seulement par relecture : la polarité de `ParamOriginHidden`, les appels de `opStepC` dans `IssueStepC`, l'absence de réimplantation.
7. Les accès physiques (`OB-C20`), dont les métadonnées du fournisseur d'`alloc`.

La préservation sous la nouvelle restriction ne demande rien de plus : `RunFull ⊆ Run5R`, et `trace_inv` s'applique (`runFull_inv`, `Capacity:168`).

## Audit final

- `lake build` (dans `formal/`) réussit : 126 jobs. Aucun avertissement, ni dans la construction complète, ni module par module (`lake env lean`).
- Le `grep` d'`AGENTS.md` est vide ; aucun `noncomputable` dans `FullEncap`.
- Les théorèmes de `Ern.Concurrency` sont recomptés, avec leurs axiomes collectés (`collectAxioms`) :

| | Avant (passe finale) | Ajoutés | Total |
|---|---|---|---|
| Théorèmes | 2462 | 204 | 2666 |
| Non internes | 1642 | 125 | 1767 |
| Hors `{propext, Quot.sound}` | — | — | 0 |

Aucun nom n'est retiré ni rattaché à un autre module (`comm` sur nom et module contre la liste de la passe finale).

Répartition par module des 204 ajouts, chaque case donnant « total (non internes) » :

| Module | Total (non internes) |
|---|---|
| `FullEncap.Inventory` | 134 (73) |
| `FullEncap.Witness` | 33 (17) |
| `FullEncap.Capacity` | 16 (14) |
| `FullEncap.NonRegression` | 6 (6) |
| `FullEncap.CapacityWitness` | 6 (6) |
| `FullEncap.ResetException` | 5 (5) |
| `FullEncap.Protected` | 4 (4) |
| **Somme** | **204 (125)** |

Nature des 204 ajouts :

| Nature | Nombre | Statut |
|---|---|---|
| théorèmes écrits | 72 | non internes |
| lemmes d'équation générés (`eq_N`, `else_eq`), surtout ceux des définitions par cas `Prem`, `PremG`, `CapReq` | 53 | non internes |
| noms générés (`_proof_N`, `match_N`) | 79 | internes |

72 + 53 + 79 = 204, et 72 + 53 = 125.

## Annexe — parcours des prémisses (`ScanRights.lean`, scratchpad)

```lean
import Lean
import Ern
open Lean Meta Elab Command

def prims : List Name :=
  [``Ern.MemoryModel.Access.S3.ExercisableAt, ``Ern.MemoryModel.Access.HasRight,
   ``Ern.MemoryModel.Access.HolderRight, ``Ern.Concurrency.CtrlRight,
   ``Ern.MemoryModel.Arena.MetaRight, ``Ern.MemoryModel.Access.Grounds,
   ``Ern.Concurrency.MutexReal.NewMutexRight]

-- Constants in a definition's value, an inductive's constructors, a constructor's type
-- (minus its own inductive); theorems and recursors are not unfolded.
def deps (env : Environment) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return {}
  let mut s : NameSet := {}
  match ci with
  | .defnInfo d => s := d.value.getUsedConstantsAsSet
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then s := s.append cc.type.getUsedConstantsAsSet
  | .ctorInfo c => s := c.type.getUsedConstantsAsSet.erase c.induct
  | _ => pure ()
  return s.erase n

-- `reach` (memoized): the primitives reachable from a constant. `tree`: from each constructor of
-- `LStep`, print every node reaching a primitive; for a structure, print each field whose
-- projection type reaches one. Full text in the scratchpad.
```

Sortie résumée : `LStep.terminate` et `LStep.join` n'atteignent rien. `LStep.spawn` n'atteint que `ParamOriginHidden`. Les autres constructeurs atteignent exactement les champs de la table de la tâche 1, ainsi que `EnterPreC.originHidden` et `SpawnValPre.originHidden`.
