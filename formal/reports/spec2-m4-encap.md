# Spec 2, jalon 4, tranche 3 — encapsulation complète (C22 point 6)

Formalisation exploratoire, jamais mergée. Branche `formal/spec2-m4`, rien n'est poussé.

La section « Complément » rend compte du complément de cette tranche (corpus v14, § 2 terdecies).

## Sources

- **WC5.2** (`ERN_Concurrency_Model_WC5.2.md`, version retouchée). Clauses lues pour cette passe :
  - C1 à C8, C12 à C18 et C21 à C25 ;
  - C43 à C46, `OB-C28`, choix de rédaction 10.
- **Spec 1** (`specs/ERN_Memory_Model_Specification_v0.1.md`). Paragraphes lus :
  - §36, §42, §43, §46, §47, §50, §80 ;
  - §60 à §78 (§73 en entier).
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
| 5 | **Réfuté**, aussi sur `RunFull` : un grant abandonné par sortie de frame, dont un dérivé survit dans un contexte enfant. Sur `Run7`, W-GI et W-RX A le réfutent. Il tient à chaque pas des 30 autres traces `RunFull` du dépôt (les 24 exécutions amendées finales, `lvσ`, le jumeau de W-GI, W-RX B et trois nouveaux témoins de la tâche 4). |
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
| `0cbe567`, `318197e` + ce commit | — | ce rapport |

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
- W-GI (`W_GI_current`) et W-RX A (`W_RX_A_current`) sont des `RunAmF` qui ne sont pas des `RunFull`, comme l'attend le corpus ;
- les traces qui n'existent que comme `EncapsulatedTrace`, `EncapsulatedTrace5C` ou `EncapsulatedTrace5R` (traces de WC4, S4, S9, W-GS, W-GC) ne sont pas des exécutions amendées finales et ne sont pas rejouées sous `RunFull` ; elles restent non vérifiées, comme à la passe précédente.

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

- **Prouvé.** `capacity_spawnVal` (`Capacity:252`) : au début de chaque phase de transfert, dans l'état de phase `t`, le contexte créateur a `cap5 = Modify` sur toute feuille de la source de la phase (`PhaseCap`, lu sur `t.P`). Hypothèses : `DDSound k`, `StaticsOK statics`, `σ 0` initial, `RunFull k L σ lbls`, `i < |lbls|`, `lbls[i] = .spawnVal c ps ls vs`.
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

**Balayage.** `ProtectedOK` tient à chaque pas des 30 autres traces `RunFull` du dépôt (`protected_sweep`, `:161`) :

- les 24 exécutions amendées finales, dont `ce`, la trace d'`exc_endUse` ;
- `lvσ`, le jumeau de W-GI, W-RX B ;
- les trois nouveaux témoins de la tâche 4 (`free`, `exitFrame`, `terminate`).

Dans les quatre témoins de la tâche 4, l'entrée meurt avec le pas ; ils sortent donc de l'énoncé « avant et après ».

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

## Problèmes de spécification

**C22 point 1 et la réancre.** C22 point 1 se termine par « No independent ordinary derivative may be issued directly from `guarded` while the entry is live ». Dans la trace du grant abandonné, après la sortie de frame (pas 6), `x` est un descendant actif direct de `guarded` (`ancs 6 = [3, 1]`, prouvé dans `protected_runFull_refuted`), alors que l'entrée `e` est vivante. Aucun pas n'a dérivé `x` de `guarded` : la réancre de §73 a changé son origine. Savoir si cela relève de « issued » est une lecture qui revient au propriétaire ; je ne tranche pas.

**Lecture de « sous-arbre du grant ».** Voir la tâche 5 : chaîne d'origine courante (réfutée) ou lignée historique (différée par §73).

**Lecture de « entrée vivante »** dans le fait « Donnée protégée » du corpus : voir la section suivante.

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

## Complément

Cette section rend compte du complément de la tranche 3 : brief « tranche 3 : encapsulation complète, complément », corpus `corpus-spec2-m3.md` v14 (§ 2 terdecies), WC5.2 inchangé. Les sections précédentes restent telles quelles ; celle-ci les complète et, pour la tâche 5, les remplace.

### Sources

- **WC5.2** : C4 à C8, C12 à C18, C21, C22, C32, C43, C45, C46, C49 ; `OB-C28` ; § V (S18).
- **Spec 1** : §40, §43, §47, §50, §54, §60 à §65, §69, §70, §73, §80.
- **Corpus** v14 : § 2 terdecies en entier ; § 2 duodecies, fait « Donnée protégée » (rédaction v14).
- **Décisions du propriétaire** appliquées :
  - la tâche 5 est énoncée en trois cas ;
  - la réancre de §73 n'est pas une émission au sens de C22 point 1 ;
  - « entrée vivante » se lit vivante avant et après le pas.

### Commits

| Commit | Tâche | Contenu |
|---|---|---|
| `857972e` | 1 | `AbandonedGrant.lean` : W-AG, W-AG-J, W-AG′, graphe strict |
| `cca140c` | 2 | `Closure.lean` : fermeture de la descendance |
| `2a92c48` | 3 | `Dying.lean` : forme des pas, feuille protégée qui ne meurt pas |
| `88f099c` | 4 | `SpawnValCap.lean` : capacité de `spawnVal` avant le pas |
| `28312c0` | 5 | `LastAcquire.lean`, `ComplementSweep.lean` : dernière prise, trois cas, fait du corpus, balayage |
| `7384238` | 6 | `Replay.lean` : traces rejouées |
| `012921f` | 3 | `DyingCap.lean` : aucun autre contexte n'a de capacité sur une feuille qui meurt |
| `3477c4c` | 3, 6 | genres qui tuent (`KillOK`) ; traces positives restantes ; balayage des traces rejouées |
| `2774cfe`, `8ae69ee` | 6 | W-GS pas 2 et 3 en vérification locale ; états de départ des pas exclus atteints par les suites admises |

Les numéros de ligne ci-dessous sont ceux de `8ae69ee`. Huit modules s'ajoutent aux sept de la tranche 3, tous importés dans `formal/Ern.lean`. Aucune définition ni aucun théorème existant n'est modifié, `protected_runFull_refuted` compris.

### Définitions ajoutées et écarts au brief

| Notion du brief | Encodage (module:ligne) | Écart |
|---|---|---|
| Descendants couvrants de `e` | `CoveringDesc s e.guarded j` (`SyncLib:158`), existant ; `covSet` (`AbandonedGrant:32`) les liste | aucun : `g ∈ ancs j` (descendant strict, chaîne courante lue transitivement), `j` active, `afp j ∩ afp g ≠ ∅` |
| Lien d'origine direct | `S3.org j` (champ `origin` courant) | aucun |
| Feuille qui meurt | `Dying s s' l` (`Classify:32`), définition de la tranche 3 | exige en plus que `l` soit une feuille avant le pas ; gardée comme le brief le permet |
| Capacité de provenance `S` | `ProvCap st S c l m` (`LastAcquire:84`) : une autorité `x ∈ S`, attribuable à `c` en mode `m` sans `guarded` vivant (`Attr5`, C43), de mode effectif au moins `m` sur `l` | équivaut à « `cap5(c, l) ≥ m`, atteinte par `x ∈ S` » (`cap5_attained`, `:64`) |
| `CapReq` avec provenance | `CapFrom k st S` (`LastAcquire:90`) | même clause par genre que `CapReq` ; pour `spawnVal`, `Modify` sur les feuilles des sources, lues avant le pas (tâche 4) |
| Cas 3 de la fermeture | `GrantOf st e j lbl` (`Closure:178`) | l'entrée acquise est identifiée par son `guarded` (`e'.guarded = e.guarded`), pas par sa position ; deux entrées vivantes de même `guarded` sont la même par C21 point 4 (`SyncInv.unique`) |
| Fermeture pour un pas | `ClosureStep` (`Closure:192`), décidable | `e` parcourt le registre d'avant le pas |
| Second fait de la tâche 3, pour un pas | `OtherCapFree` (`Dying:190`), décidable | bornes `c' < |C|`, `l < |P|` pour la décidabilité ; le théorème `other_cap_dying_run` n'a pas ces bornes |
| Genres qui tuent | `killKind`, `KillOK` (`ComplementSweep:87`, `:92`), décidables | contrôle sur les traces, pas de théorème général (voir tâche 3) |
| Contrôle des trois cas | `ThreeOK` (`ComplementSweep:37`), `SweepOK` (`:50`) | `ThreeOK` vérifie la provenance au mode `Observe`, plus faible que `CapFrom` ; le théorème `three_cases` donne le mode exigé |
| Phases de `spawnVal` | `PhaseRel s c t` (`SpawnValCap:72`) | structure auxiliaire de preuve |

Aucune hypothèse n'est ajoutée : chaque énoncé `_run` a pour seules hypothèses `DDSound k`, `StaticsOK statics`, `σ 0` initial et `RunFull k L σ lbls`, plus les données quantifiées de l'énoncé (indice, entrée, feuille).

### Tâche 1 — Témoins (corpus § 2 terdecies)

Contrat `KM`, disposition `L0`, depuis `MX₃`. Le pas `k` du corpus est le label d'indice `k + 2`. Identités : `root_M` = 0, `guarded` = 3, `g` = 5, `x` = 6, `g′` = 7 (W-AG), `y` = 7 (W-AG′) ; places `slot` = 1, `lock` = 2, `T` = 3.

| Témoin | Attendu (corpus) | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| W-AG, pas 1 à 11 | `ok` au noyau et admis | `RunFull` depuis l'état initial | O1, O6, C14 à C16, O1, C4, C6, O10, O3, C18, C16, O10 | `W_AG_run` (`AbandonedGrant:81`) |
| W-AG, pas 6 | aucune création ; `origin(x)` : `g` → `guarded`, empreinte et mode inchangés ; ensemble `{g, x}` → `{x}` ; `e` vivante, `g` inactive, `root_M` à `Modify` effectif sur `slot` et `lock` | tous : `|A|` inchangé ; `org 6` : 5 → 3 ; `covSet` `[5, 6]` → `[6]` ; `effective 0 1 = effective 0 2 = Modify` | §73.4, C6, C12, §43.2 | `W_AG_6_facts` (`:93`) |
| refus a, `c0 : acquire(e)` | sans issue `ok` ; C14.2 échoue ; C14.1 et C14.3 tiennent ; C15.4, C15.5 échouent | idem | C14.2, C15.4 (§60.2), C15.5 (§60.3) | `W_AG_a` (`:106`) |
| refus b, `c0 : unlock(e)` | `reject`, C17.2 | aucune issue `ok` ; `g` inactive | C17.2 (§62.1) | `W_AG_b` (`:118`) |
| refus c, `c0 : resetLock(e)` | `reject`, C18.2 | aucune issue `ok` ; `x` couvre `T` ; C18.1 tient par `root_M` | C18.2 | `W_AG_c` (`:126`) |
| refus d, `c0 : read3(T)` via `guarded` | `reject`, O9.2 | `reject` au noyau ; mode effectif de `guarded` sur `T` absent | O9.2, §43.3 | `W_AG_d` (`:135`) |
| W-AG-J | `ok` et admise | `RunFull` depuis l'état initial | C7, C8 | `W_AGJ_run` (`:161`) |
| graphe strict, W-AG | aucun chemin `hb` entre les écritures de `T` ; C46 violé | `ExclPair 9 13 3`, `¬ HBS`, `¬ HandoffOrderedAtS`, `¬ HandoffOrderedS`, `RaceS` | C46 | `W_AG_strict` (`:194`) |
| graphe strict, W-AG-J | écriture de `c1` →`po` `terminate` →`sw` `join` →`po` écriture de `c0` | `PO 9 11`, `SWS 11 12`, `PO 12 15`, `HBS 9 15`, `HandoffOrderedS`, `¬ RaceS` | C32, C46 | `W_AGJ_strict` (`:208`) |
| W-AG′, A1 à A4 | `ok` et admis | `RunFull` depuis l'état initial | O1, C4, C7, O10 | `W_AGp_run` (`:249`) |
| W-AG′, colonne | `{x}` ; A1 `{x, y}`, `y` d'origine `x` ; A2 inchangé ; A3 `{y}`, sans création, `origin(y)` : `x` → `guarded` ; A4 inchangé | `[6]`, `[6, 7]` (`org 7 = 6`), `[6, 7]`, `[7]` (`|A|` inchangé, `org 7` : 6 → 3), `[7]` | §60, §73.4, C7 | `W_AGp_run` (`:249`) |
| W-AG′, négatif après A3 | `reject`, C18.2 | aucune issue `ok` ; `y` couvre `T` | C18.2 | `W_AGp_neg` (`:278`) |
| W-AG, pas 7 | troisième cas | `e` vivante avant et après ; `g` inactive ; capacité `Modify` de `c1` par `x`, descendant couvrant | — | `W_AG_7_third` (`ComplementSweep:124`) |

**Écart de représentation (refus b et c).** Le corpus attend `reject`. Le modèle ne représente que les issues `ok` des pas de bibliothèque (`UnlockOk`, `ResetLockOk`) ; le refus s'y lit comme l'absence d'issue `ok`. Le classement entre `reject` et `non habilité` relève de D-C1, hors de portée.

### Tâche 2 — Fermeture de la descendance

**Énoncé prouvé.** `closure_run` (`Closure:401`) : pour tout `i < |lbls|`, `ClosureStep (σ i) lbls[i] (σ (i + 1))`. Hypothèses : `DDSound k`, `StaticsOK statics`, `σ 0` initial, `RunFull k L σ lbls`. Forme par pas : `closure_step` (`:282`), sous `KInvCA`, `AdminSep` et `Encap` (C22 points 1 à 3 et 5), tous vrais sur les états atteints (`runFull_inv`, `Capacity:168`).

**Méthode.** Chaque pas est lu par l'abstraction `Skel` de `SyncPreserve` :

- les autorités existantes gardent empreinte et mode ;
- elles ne sont jamais réactivées ;
- leur chaîne d'origine ne fait que perdre des éléments ;
- les autorités ajoutées sont des racines ou des dérivées d'une autorité existante active.

Une autorité existante n'entre donc jamais dans l'ensemble (cas 1, `cover_of_skel`, `:207`). Une autorité créée a pour origine soit `guarded` lui-même, soit une autorité de l'ensemble. Une origine `guarded` n'arrive que par `acquire` (cas 3) : `derive` et `split` de source `guarded` sont exclus par `Encap` (C22 point 1), et `deriveSync` brut est exclu (`deriveSync_excluded`, `SyncPreserve:1171`).

**Pas composés et forme (2′).** `issue`, `reset` et `spawnVal` sont lus phase par phase (`Skel.comp`, `:33`). Seule leur première phase crée des autorités :

- `issue` : le `split` de `internal`, puis le `store`, qui ne crée rien ;
- `reset` : le `derive` de `internal`, puis le `release` de l'autorité créée ;
- `spawnVal` : les racines des locaux, puis les transferts et la cession, qui ne créent rien.

L'origine immédiate d'une autorité créée existait donc avant le pas. Le cas (2) est prouvé tel qu'écrit, et la forme (2′) n'est pas nécessaire. La dernière prise se lit avec le cas (2).

**Acquire d'une autre entrée.** Si le `guarded` d'une entrée `e₀` est lui-même dans l'ensemble de `e`, le grant de `acquire(e₀)` a pour origine une autorité de l'ensemble : cas (2) pour `e`, cas (3) pour `e₀`. La preuve couvre ce cas ; aucun témoin ne le réalise.

**Table des 28 genres.** Les colonnes sont lues sur les effets du modèle ; le seul effet qui écrit `origin` est `exitG` (§73.4), utilisé par `exitFrame` et `terminate`.

| # | Genre | Crée une autorité | Change un lien d'origine direct | Peut faire entrer une autorité (cas) | Statut |
|---|---|---|---|---|---|
| 1 | `derive` | oui, d'origine la source (§60) | non | oui, cas 2, si la source est dans l'ensemble ; jamais depuis `guarded` (C22.1) | prouvé |
| 2 | `split` | oui, d'origine la source (§61) | non | oui, cas 2, même restriction | prouvé |
| 3 | `release` | non | non | non | prouvé |
| 4 | `transfer` | non (déplace des détenteurs) | non | non | prouvé |
| 5 | `depend` | non | non | non | prouvé |
| 6 | `enterFrame` | oui, racines des locaux (`origin = none`) | non | non | prouvé |
| 7 | `exitFrame` | non | oui (§73.4, réancre) | non : la chaîne ne fait que perdre des éléments | prouvé |
| 8 | `read3` | non | non | non | prouvé |
| 9 | `write3` | non | non | non | prouvé |
| 10 | `writeShared` | non | non | non | prouvé |
| 11 | `pin` | non | non | non | prouvé |
| 12 | `unpin` | non | non | non | prouvé |
| 13 | `endUse` | non | non | non | prouvé |
| 14 | `free` | non | non | non | prouvé |
| 15 | `alloc` | oui, racines (`origin = none`) | non | non | prouvé |
| 16 | `store` | non | non | non | prouvé |
| 17 | `spawn` | oui, racines des locaux de l'enfant | non | non | prouvé |
| 18 | `terminate` | non | oui (C7, §73.4, réancre) | non | prouvé |
| 19 | `join` | non | non | non | prouvé |
| 20 | `deriveSync` brut | oui, d'origine `guarded` | non | — | sans objet : exclu par `Encap` (C22.2) |
| 21 | `newMutex` | non | non | non | prouvé |
| 22 | `acquire` | oui, le grant, d'origine `guarded` (C15, C16) | non | oui : cas 3 pour l'entrée acquise ; cas 2 pour une entrée dont l'ensemble contient ce `guarded` | prouvé |
| 23 | `unlock` | non | non | non | prouvé |
| 24 | `resetLock` | non | non | non | prouvé |
| 25 | `spawnVal` | oui, racines des locaux (phase 1 seulement) | non | non | prouvé |
| 26 | `newArena` | non | non | non | prouvé |
| 27 | `issue` | oui, le bloc, d'origine `internal` (phase 1 seulement) | non | oui, cas 2, si `internal` est dans l'ensemble | prouvé |
| 28 | `reset` | oui, d'origine `internal` (phase 1), relâchée en phase 2 | non | non : l'autorité créée est inactive après le pas | prouvé |

Décompte : 27 prouvés, 1 sans objet (`deriveSync` brut), 0 contre-exemple.

**Contrôle par `decide`.** `ClosureStep` tient à chaque pas des 46 traces `RunFull` balayées (`sweep`, `ComplementSweep:62` ; `sweep_replay`, `Replay:438`).

### Tâche 3 — Feuilles qui meurent

| Énoncé | Théorème | Statut | Hypothèses en plus de `DDSound`, `StaticsOK`, `σ 0` initial, `RunFull` |
|---|---|---|---|
| une feuille de `footprint(e.guarded)` ne meurt pas si `e` est vivante avant et après | `protected_not_dying_run` (`Dying:174`) | prouvé | `i < |lbls|`, `e.Live (σ i)`, `e.Live (σ (i+1))`, `l ∈ afp(e.guarded)` dans `σ i` |
| avant un pas de `c`, aucun autre contexte n'a de `cap5` sur une feuille qui meurt | `other_cap_dying_run` (`DyingCap:55`) ; forme décidable `otherCapFree_run` (`:84`) | prouvé | `i < |lbls|`, `c' ≠ lbls[i].ctx`, `Dying (σ i) (σ (i+1)) l` |
| seuls `endUse`, `free`, `exitFrame`, `terminate` font mourir des feuilles | `sweep_kill` (`ComplementSweep:102`), `sweep_replay` (`Replay:438`) | vérifié sur les 46 traces ; établi par relecture ; **pas de théorème général** | — |

**Premier fait.** Le `guarded` de `e` est actif après le pas (C12) et couvre la feuille, dont l'empreinte est conservée (`Skel`). Le pas garde les feuilles feuilles (`PSkel`). `NoDangling` après le pas (§54) interdit alors que la place devienne inutilisable. Les lemmes utilisés sont `shape_step` (`Dying:53`), pour `Skel` et `PSkel` de chacun des 28 genres, et `protected_not_dying` (`:158`).

**Second fait.** C'est un corollaire de L1 :

1. Après le pas, aucun contexte n'a de `cap5` sur une feuille qui est morte (`cap5_none_after`, `DyingCap:26`). Une autorité qui l'atteindrait serait active et couvrirait une feuille d'une place inutilisable, contre `NoDangling`.
2. Une capacité d'un contexte `c' ≠ c` avant le pas serait donc perdue dans un pas de `c`.
3. L1 l'interdit (`cap5_drop_own`, `CapDrop:1332`, WC5.2 C45).

La passerelle : un préfixe de `RunFull` est une `Run5R` (`run5R_take`, `:43`), donc une `EncapsulatedTrace5` (`run5R_trace`, `encapsulatedTrace5R_imp`, `encapsulatedTrace5C_imp`).

**Invariants qui servent.** `NoDangling` (§54) et C12 servent directement. Les préconditions §69.2, §70.3, §73.2, §73.4 et C7 ne sont pas invoquées dans ces preuves : le second fait passe par L1, dont la preuve par genre est celle du jalon 4, réutilisée sans être relue ici.

**Genres qui tuent, par relecture.** Une place devient inutilisable si elle est marquée morte, si sa frame terminale disparaît, ou si sa chaîne de propriétaires change :

- `dead` n'est changé que par `endUse` (§69, `OwnedIn`) et `free` (§70, `FreedPlace`) ;
- les frames ne sont retirées que par `exitFrame` et `terminate` (`exitEff`) ;
- les propriétaires ne changent que par `transfer` et les phases de `spawnVal`, vers `corr(r)`, partie de la destination, utilisable par §63.

Ce dernier point n'est pas prouvé en général. Le contrôle `KillOK` le confirme sur les 46 traces.

**Les quatre témoins `exc_*`** (`exc_dying_facts`, `Dying:205`). Dans chacun, l'entrée meurt avec le pas, donc le premier fait ne s'applique pas, et `OtherCapFree` tient.

### Tâche 4 — `spawnVal` dans l'état d'avant le pas

**Prouvé.** `spawnVal_cap_pre` (`SpawnValCap:342`) : pour un pas `lbls[i] = .spawnVal c ps ls vs`, toute source `v ∈ vs` et toute feuille `l ∈ footprint (σ i).P v.1`, il existe une autorité attribuable à `c` sans `guarded` vivant (`Attr5`), de mode effectif `Modify` sur `l` dans l'état d'avant le pas, donc `cap5(c, l) = Modify`. Hypothèses : `DDSound`, `StaticsOK`, `σ 0` initial, `RunFull`, `i < |lbls|`, `lbls[i] = .spawnVal c ps ls vs`.

**Argument.** `PhaseRel` (`:72`) relie l'état d'avant le pas à chaque état de phase. Les états de phase n'ajoutent que :

- les racines des locaux de l'enfant, tenues par sa nouvelle frame (`phaseRel_create`, `:196`) ;
- les détenteurs déplacés vers ces locaux par les transferts précédents (`phaseRel_transfer`, `:232`).

Une chaîne `Exer5` du créateur dans un état de phase n'utilise ni l'un ni l'autre, avec les mêmes modes effectifs sur les feuilles existantes (`exer5_back`, `:107`). La conclusion se transporte phase par phase (`phases_cap`, `:304`).

**Aucun contre-exemple.** Aucun transfert d'une phase ne donne au créateur une capacité qu'il n'avait pas avant le pas.

### Table de capacité de la tranche 3, mise à jour

Seules ces lignes changent ; les autres sont celles de la tâche 4 ci-dessus.

| # | Genre | Avant ce complément | Après |
|---|---|---|---|
| 7 | `exitFrame` | exception : feuilles qui meurent | exception, bornée : une feuille protégée par une entrée vivante avant et après ne meurt pas (`protected_not_dying_run`) ; aucun autre contexte n'a de `cap5` sur une feuille qui meurt (`other_cap_dying_run`) |
| 13 | `endUse` | prouvé sur la place ; exception ailleurs | prouvé sur la place ; exception bornée comme pour `exitFrame` |
| 14 | `free` | prouvé sur la place ; exception ailleurs | prouvé sur la place ; exception bornée comme pour `exitFrame` |
| 18 | `terminate` | exception : feuilles qui meurent | exception bornée comme pour `exitFrame` |
| 25 | `spawnVal` | prouvé par phase ; inachevé avant le pas | prouvé par phase et avant le pas (`spawnVal_cap_pre`) |

Décompte mis à jour des 28 genres :

| Statut | Genres | Nombre |
|---|---|---|
| prouvé | les 11 de la tranche 3 et `spawnVal` | 12 |
| prouvé sur la place, exception bornée ailleurs | `endUse`, `free` | 2 |
| exception bornée | `exitFrame`, `terminate` | 2 |
| sans objet | les mêmes 12 | 12 |
| contre-exemple | — | 0 |

`CapReq` reste inchangé : le contexte qui agit n'a toujours besoin d'aucune capacité sur les feuilles qui meurent. Le second fait de la tâche 3 en tient lieu, comme le dit le corpus.

### Tâche 5 — Dernière prise et donnée protégée

| Énoncé | Théorème | Statut | Hypothèses en plus de `DDSound`, `StaticsOK`, `σ 0` initial, `RunFull` |
|---|---|---|---|
| ensemble vide sans grant | `empty_without_grant` (`LastAcquire:295`) | prouvé | `n ≤ |lbls|`, `e ∈ (σ n).reg`, `e.Live (σ n)`, `e.grant = none` |
| dernière prise | `last_acquire` (`:371`) | prouvé | aucune : énoncé pour tout `n ≤ |lbls|`, tout indice `i` du registre, toute entrée vivante de grant `some g` |
| trois cas | `three_cases` (`:236`) | prouvé | `i < |lbls|`, `e ∈ (σ i).reg`, `e.Live (σ i)`, `e.Live (σ (i+1))`, `l ∈ afp(e.guarded)`, `TouchesF L (σ i) lbls[i] l` |
| fait « Donnée protégée » du § 2 duodecies (v14), 28 genres | `protected_cap_run` (`:275`) | prouvé | `i < |lbls|`, `e.Live (σ i)`, `e.Live (σ (i+1))`, `l ∈ afp(e.guarded)`, `TouchesF` ; `e ∈ reg` n'est pas requis |

**`GrantDiscipline` sur `RunFull`.** C'est déjà établi sur les états atteints par `runFull_inv` (`Capacity:168`), sous `DDSound`, `StaticsOK`, `σ 0` initial et `RunFull`, avec `i ≤ |lbls|` : `RunFull ⊆ Run7 ⊆ Run5R`, puis `trace_inv` (`Reachable:87`). Les frontières sont les préconditions des pas qui posent `grant = none` :

- C13.9 (champ `available`, `SyncLib:277`) ;
- C17.2 et C17.3, préconditions de O3 dans `unlock` ;
- C18.2 dans `resetLock`.

Rien ne manque.

**Dernière prise.** La récurrence porte sur les indices de la `RunFull` ; aucun historique n'est ajouté à l'état. L'entrée est identifiée par sa position `i` dans le registre, stable par `reg_step` (`:308`) ; le dernier `acquire(i)` réussi est à l'indice `kk`, avec `g = |A(σ kk)|`. Tout descendant couvrant est `g`, ou a été créé à un pas `k'`, avec `kk < k' < n`, du cas (2) de la fermeture. Servent :

- la fermeture (tâche 2) ;
- `shape_step` ;
- `SyncInv` : `regBound`, et `unique` pour écarter le cas 3 d'un autre indice.

**Trois cas.** Le grant est lu dans l'état d'avant le pas. Avec `x` l'autorité qui atteint la capacité :

1. `grant = none` : un tel pas n'existe pas. `x` serait un descendant couvrant, contre `GrantDiscipline`.
2. `grant = some g`, `g` active : `CapFrom` de provenance « `x = g` ou `g ∈ ancs x` », par `GrantSubtree` (C21 point 5).
3. `grant = some g`, `g` inactive : `CapFrom` de provenance `CoveringDesc (σ i) e.guarded`.

Le lemme commun est `cov_of_attr` (`:201`) : par I1 (§50) et C21 point 1, une autorité qui n'est pas un `guarded` vivant et a un mode effectif présent sur une feuille de `footprint(guarded)` est un descendant couvrant. Un ancêtre de `guarded` n'a pas de mode effectif sur la feuille (§43.3), et une autorité sans lien contredirait I1.

| Cas | Invariants | Tâches |
|---|---|---|
| tous | I1, C21.1, WF3 (empreintes) | capacité de la tranche 3 (`capacity_run`), tâche 3 premier fait (la feuille ne meurt pas, donc `CapReq` exige une capacité), tâche 4 (`spawnVal`) |
| `grant = none` | `GrantDiscipline` (C22) | — |
| `g` active | `GrantSubtree` (C21.5) | — |
| `g` inactive | — | — |

La fermeture (tâche 2) ne sert pas aux trois cas ; elle sert à la dernière prise.

**Contrôle par `decide`.** Les trois cas, au mode `Observe` (`ThreeOK`), tiennent à chaque pas des 46 traces `RunFull`. Ces traces sont :

- les 24 exécutions amendées finales ;
- `lvσ`, le jumeau de W-GI, W-RX B et les trois témoins `free`, `exitFrame`, `terminate` ;
- W-AG, W-AG-J et W-AG′ ;
- les 13 traces rejouées de la tâche 6.

Le pas 7 de W-AG tombe dans le troisième cas (`W_AG_7_third`).

**Ce que la tâche 5 établit.** C'est la provenance des capacités. Toute capacité sur une feuille protégée par une entrée vivante avant et après le pas vient de la dernière prise du verrou :

- du grant enregistré ou d'un de ses descendants s'il est actif ;
- sinon, d'un descendant couvrant, créé après le dernier `acquire(e)` à partir d'un autre descendant couvrant.

Aucune autorité existante n'entre dans l'ensemble. La réancre change le lien direct sans changer l'appartenance.

**Ce qu'elle n'établit pas.** Elle ne dit rien de l'ordre entre les accès (C46) :

- dans W-AG, le survivant `x` écrit `T` au pas 7 et `c0` l'écrit au pas 11 sans chemin `hb` (`W_AG_strict` : `RaceS`, pas de `HandoffOrderedS`) ;
- W-AG-J ordonne la paire par `terminate` et `join` (`W_AGJ_strict`).

L'exclusivité tient pendant que le survivant vit ; l'ordre reste une obligation distincte (C46). Aucune preuve générale d'absence de course n'est tentée (hors de portée).

### Tâche 6 — Traces rejouées

**Verdicts locaux.** Le pas est `ok` au noyau et exclu par l'encapsulation complète (`¬ PremG`, donc `¬ EncapFull`). Son état de départ est atteint depuis l'état initial par une suite admise. Une trace qui contient ce pas n'est pas une `RunFull`.

| Trace | Pas | État de départ | Théorème |
|---|---|---|---|
| W-GR | 1, `c1 : read3(T)` via `guarded` | `MX₄` = `wrσ 5` | `W_GR_full` (`Replay:72`) |
| W-GC | 1, `c1 : read3(Y)` via `z` | `gc6` = `cgσ 7` | `W_GC_full` (`:117`) |
| W-GS | 1, `c0 : store(z2, T)` sans grant | `gs5` = `gsTwinσ 6` | `W_GS_full` (`:145`) |
| W-GS | 2 et 3, après le pas exclu : `c1 : acquire(e)` depuis `gs6`, `c1 : read3(T)` depuis `gs7` | états produits par le pas exclu | `W_GS_2_3_local` (`:158`), vérification locale : `EncapFull` et `LStep` |

**Exécutions `RunFull` depuis l'état initial.**

| Trace | Contenu | Théorème |
|---|---|---|
| W-GR, suite | `MX₄`, puis les pas 2 et 3 ; le pas 1 ne change pas l'état (`gr1 = x4`) | `W_GR_full` |
| W-GC, suite | la mise en place, puis les pas 2 à 4 ; le pas 1 ne change pas l'état (`gc7 = gc6`) | `W_GC_full` |
| W-GS, jumeau | `acquire(e)`, `store(z2, T)` sous le grant, `unlock(e)` | `W_GS_full` |
| S2 | préfixe de W-RL₀ | `S2_full` (`:174`) |
| S10 | préfixe de S10 rejouée | `S10_full` (`:180`) |
| S3 en entier | arena, deux `issue`, reprise | `S3_full` (`:196`) |
| S4 | enfant détaché qui survit à son créateur | `S4_full` (`:232`) |
| S9 | deux mutex pris par `c0` ; attendu admise | `S9_full` (`:254`) |
| `mutex_trace` | `newMutex`, `acquire`, `unlock` | `mutex_full` (`:281`) |
| `distinct_controllers_trace` | deux `newMutex` | `distinct_full` (`:300`) |
| `traceA`, `traceB`, `traceMutex` | S18 positif, transfert du mutex entier | `wc4_full` (`:324`) |
| `endUse_mutex_kills_entry` | `endUse(M)` tue l'entrée | `endUseM_full` (`:362`) |
| `endUse_slot_kills_entry` | `endUse(slot)` tue l'entrée | `endUseSlot_full` (`:380`) |
| jumeau de W-C22.3 (b) | `newMutex`, puis `transfer(M, M′)` | `W_C22_3b_twin_full` (`:400`) |
| jumeau de S17a | `MX₃`, `endUse(slot)`, `endUse(lock)` | `S17a_twin_full` (`:423`) |

**Aucune trace positive n'est refusée.** Recensement des traces du dépôt par leur type (`EncapsulatedTrace*`, `Run5`, `Run5C`, `Run5R`, `Run6`, `Run7`, `LRun`) :

- **Positives** : chacune est une `RunFull` ou un préfixe d'une `RunFull` ci-dessus, ou des 24 exécutions amendées finales. Préfixes : `mx3_trace`, `mx4_trace`, `ar_trace` et l'état `a8` de `ARRealize`, `gs_setup`, `gc_setup`, `traceMutex`. Formes plus anciennes des mêmes traces : `cycle_trace5`, `s2_trace5R`, `s3_trace5R`, `s4_trace5R`, `s10_trace5R`, `w_ho*_trace`, `lc_trace`.
- **Contenant un pas exclu, comme attendu** : `w_gr_trace` et `cap_L1_counterexample` (pas 1 de W-GR), `gc_trace`, `W_GS_encap`.
- **Négatifs ou contre-exemples, comme attendu** : `endUse_ctl_excluded`, `endUse_slotPart_excluded`, `W_C22_3b_encap`, `endUse_then_transfer_merges` (`LRun`), W-RC, W-NC, `store_cex`, `alloc_cex`, `issue_cex` (`ClassifyWitness`), `alloc_provider_M_refused` (`FinalWitness`). Leur prémisse en cause est celle de leur rapport d'origine.

### Pas attendus `ok` refusés, contre-exemples trouvés

- Aucun pas attendu `ok` n'est refusé, ni par le noyau ni par l'encapsulation complète.
- Aucune trace positive n'est refusée.
- Aucun contre-exemple aux énoncés des tâches 2 à 5.
- Seul écart aux attendus : les refus b et c de W-AG (et le négatif de W-AG′) sont obtenus comme « aucune issue `ok` », non comme `reject` (voir la tâche 1).

### Problèmes de spécification

Aucun nouveau. La lecture retenue de C22 point 1 (décision 2) est appliquée : la réancre de §73 entre dans le cas (1) de la fermeture.

### Ce que `OB-C28` laisse ouvert après ce complément

Fermés par ce complément :

- la forme de l'énoncé sur la donnée protégée (trois cas, prouvés) ;
- la capacité de `spawnVal` avant le pas ;
- le fait « Donnée protégée » du corpus pour les cinq genres restants.

Restent ouverts :

1. L'application de la restriction dans l'interface sûre (Specs 4 et 10).
2. §78.1 (`MetaRight` de `reset`), que le pas du modèle ne lit pas.
3. Les parties de l'exhaustivité de l'inventaire établies seulement par relecture.
4. La liste des genres qui tuent des feuilles : relecture et contrôle sur les traces, sans théorème général.
5. L'ordre entre les accès du survivant d'un grant abandonné et ceux du contexte qui reprend le mutex (C46).
6. Les accès physiques (`OB-C20`).

### Audit du complément

- `lake build` (dans `formal/`) réussit : 134 jobs, sans avertissement. Chacun des huit nouveaux modules, passé par `lake env lean`, ne produit aucun avertissement.
- Le `grep` d'`AGENTS.md` est vide. Aucun `noncomputable` dans `FullEncap`. Aucune ligne de plus de 100 caractères.
- Les théorèmes de `Ern.Concurrency` sont recomptés, avec leurs axiomes collectés (`collectAxioms`) :

| | Fin de la tranche 3 | Ajoutés | Total |
|---|---|---|---|
| Théorèmes | 2666 | 130 | 2796 |
| Non internes | 1767 | 94 | 1861 |
| Hors `{propext, Quot.sound}` | 0 | 0 | 0 |

Aucun nom n'est retiré ni rattaché à un autre module : `comm` sur nom et module, contre la liste de la fin de la tranche 3, donne 0 ligne.

Répartition par module des 130 ajouts, « total (non internes) » :

| Module | Total (non internes) |
|---|---|
| `FullEncap.AbandonedGrant` | 12 (12) |
| `FullEncap.Closure` | 28 (14) |
| `FullEncap.Dying` | 9 (7) |
| `FullEncap.DyingCap` | 6 (4) |
| `FullEncap.SpawnValCap` | 34 (23) |
| `FullEncap.LastAcquire` | 19 (13) |
| `FullEncap.ComplementSweep` | 3 (3) |
| `FullEncap.Replay` | 19 (18) |
| **Somme** | **130 (94)** |

Nature des 130 ajouts :

| Nature | Nombre | Statut |
|---|---|---|
| théorèmes écrits | 84 | non internes |
| projections des champs de la structure `PhaseRel` | 10 | non internes |
| noms générés `_proof_N` | 23 | internes |
| noms générés `match_N` | 12 | internes |
| `_sparseCasesOn` (`GrantOf`) | 1 | internes |

84 + 10 = 94 ; 23 + 12 + 1 = 36 ; 94 + 36 = 130.

## Annexe — parcours des prémisses (`ScanRights.lean`, scratchpad)

Texte complet. La version d'abord utilisée mettait en cache des résultats partiels pendant les cycles de dépendances, ce qui pouvait sous-approximer l'atteignabilité. Celle-ci fait un parcours complet par requête et ne met en cache qu'un parcours terminé. Les deux versions donnent les mêmes nœuds et les mêmes ensembles de primitives. La limite de profondeur (12) ne porte que sur l'affichage, pas sur `reach`.

```lean
import Lean
import Ern
open Lean Meta Elab Command

/-- The right-reading primitives of the brief of slice 3, task 1. -/
def prims : List Name :=
  [``Ern.MemoryModel.Access.S3.ExercisableAt, ``Ern.MemoryModel.Access.HasRight,
   ``Ern.MemoryModel.Access.HolderRight, ``Ern.Concurrency.CtrlRight,
   ``Ern.MemoryModel.Arena.MetaRight, ``Ern.MemoryModel.Access.Grounds,
   ``Ern.Concurrency.MutexReal.NewMutexRight]

/-- Constants occurring in a constant's type, its value (definitions) or its constructors'
types (inductives); theorems and recursors are not unfolded. -/
def deps (env : Environment) (n : Name) : NameSet := Id.run do
  let some ci := env.find? n | return {}
  let mut s : NameSet := {}
  match ci with
  | .defnInfo d => s := d.value.getUsedConstantsAsSet
  | .inductInfo i =>
    for c in i.ctors do
      if let some cc := env.find? c then
        s := s.append cc.type.getUsedConstantsAsSet
  | .ctorInfo c => s := c.type.getUsedConstantsAsSet.erase c.induct
  | _ => pure ()
  return s.erase n

/-- The primitives reachable from `n`, by a complete depth-first search over `deps`; only a
finished search is cached, so no partial result of a cycle is reused. -/
def reach (env : Environment) (n : Name) : StateM (Std.HashMap Name (List Name)) (List Name) := do
  if prims.contains n then return [n]
  if let some r := (← get)[n]? then return r
  let mut visited : NameSet := {}
  let mut stack : List Name := [n]
  let mut out : List Name := []
  let mut fuel := 1000000
  while fuel > 0 do
    fuel := fuel - 1
    match stack with
    | [] => break
    | m :: rest =>
      stack := rest
      if visited.contains m then continue
      visited := visited.insert m
      if prims.contains m then
        if !out.contains m then out := m :: out
        continue
      for d in (deps env m).toList do
        if !visited.contains d then stack := d :: stack
  if fuel = 0 then panic! "fuel"
  modify (·.insert n out)
  return out

partial def tree (env : Environment) (n : Name) (ind : String) (depth : Nat) :
    StateT NameSet (StateM (Std.HashMap Name (List Name))) Unit := do
  let r ← liftM (reach env n)
  if r.isEmpty then return
  if prims.contains n then return
  let seen := (← get).contains n
  let short := n.toString.replace "Ern.MemoryModel.Access." "" |>.replace "Ern.Concurrency." ""
  dbg_trace s!"{ind}{short}  → {r.map (fun x => x.components.getLast!.toString)}{if seen then " (vu)" else ""}"
  if seen || depth = 0 then return
  modify (·.insert n)
  -- Structures: list fields through projections.
  if isStructure env n then
    for f in getStructureFields env n do
      let proj := n ++ f
      let some pc := env.find? proj | continue
      let cs := pc.type.getUsedConstantsAsSet.erase n
      let mut rr : List Name := []
      for d in cs.toList do
        for p in (← liftM (reach env d)) do
          if !rr.contains p then rr := p :: rr
      if !rr.isEmpty then
        dbg_trace s!"{ind}  .{f}  → {rr.map (fun x => x.components.getLast!.toString)}"
        for d in cs.toList do
          if !prims.contains d then tree env d (ind ++ "      ") (depth - 1)
    return
  for d in (deps env n).toList do
    tree env d (ind ++ "  ") (depth - 1)

elab "#scan" : command => do
  let env ← getEnv
  let some (.inductInfo i) := env.find? ``Ern.Concurrency.LStep | throwError "no LStep"
  let mut memo : Std.HashMap Name (List Name) := {}
  for c in i.ctors do
    let ((_, _), memo') := ((tree env c "" 12).run {}).run memo
    memo := memo'
    dbg_trace "----"

#scan
```

Sortie résumée : `LStep.terminate` et `LStep.join` n'atteignent rien. `LStep.spawn` n'atteint que `ParamOriginHidden`. Les autres constructeurs atteignent exactement les champs de la table de la tâche 1, ainsi que `EnterPreC.originHidden` et `SpawnValPre.originHidden`. Commande : `lake env lean ScanRights.lean`, depuis `formal/`.
