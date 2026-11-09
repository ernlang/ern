# Spec 2, jalon 1 — passe corrective WC3

Branche `formal/spec2-m1`, formalisation exploratoire. Candidate : `ERN_Concurrency_Model_WC3_corrige.md` (WC3, non commitée), qui remplace WC2. Spec 1 : `specs/ERN_Memory_Model_Specification_v0.1.md`.

Commits de la passe :

| Commit | Contenu |
|---|---|
| `c4c6e4d` | Définitions alignées sur WC3 (`Sync`, `SyncLib`, `Frames`, `Transfer`) et adaptation des modules dépendants |
| `e1e3a84` | Trace S4 |
| `b0af112` | Références WC2 → WC3 dans les docstrings ; P1 sur `SC.view` |
| `5b66e86` | `TransferPreserve.lean` : `spawnVal_preservesC` |
| `11baa0d` | `deriveSync_breaks_i2_false` |

Écart de méthode : la consigne « commit à chaque module compilant » n'a pas pu être suivie pour les quatre modules de définitions. Le changement de signature de `KC`, `NewMutexOk`, `ResetLockOk` et `DeriveSyncPre` casse les modules qui les utilisent. Le premier commit regroupe donc les quatre modules et leurs adaptations. C'est le premier état où `lake build` passe.

## 1. Passages lus

- **WC3** : lu en entier.
- **Spec 1** : §43, §44, §45, §46, §51, §55, §56, §57, §60, §61, §62, §63, §64, §65, §68, §72, §73, §78.

## 2. Définitions modifiées

| Définition | Avant (WC2) | Après (WC3) | Clause |
|---|---|---|---|
| `KC` (`Sync.lean:23`) | `structure KC extends K`, `SyncAuthorized : SC → Nat → Nat → Prop` | `structure KC (R : Type) extends K`, `SyncAuthorized : R → SC → Nat → Nat → Prop`. Le noyau n'importe pas `SyncLib` ; `libKC k L : KC SyncReg` | C2, C14 |
| `DeriveSyncPre` (`Sync.lean:36`) | 8 champs, `authorized : kc.SyncAuthorized s g top` | 9 champs : ajout de `mode : OptP (A[g]?) (fun y => Mode.modify.le y.mode) False` ; `authorized : kc.SyncAuthorized r s g top`. Le reste est inchangé | C15.1–C15.6 |
| `DeriveSyncStep`, `CStepS` | `kc` | `kc r` (registre explicite) | C14, C15 |
| `SyncInv` (`SyncLib.lean:169`) | `guarded`, `grant`, `control`, `unique` (C21.1, .2, .3, .5 de WC2) | 7 champs : `guarded` (C21.1), `grant` (C21.2), `control` (C21.3), `ctlUnique` (C21.4, 1ʳᵉ phrase, nouvelle définition `CtlUnique`), `unique` (C21.4, 2ᵉ phrase), `grantSubtree` (C21.5), `regBound` (C21.6, sur toutes les entrées) | C21 |
| `GrantSubtree`, `RegBound`, ancien `SyncState` (`SyncPreserve.lean`) | auxiliaires hors WC2 | supprimés, intégrés à `SyncInv`. `SyncState := SyncInv ∧ GrantDiscipline` | C21.5, C21.6 |
| `NewMutexPreBase` → `NewMutexPre` (`SyncLib.lean:209`) | 7 champs, sans `k` | paramètre `k : K`, 10 champs. Ajouts : C13.3, le contrôleur est aussi *utilisable* ; `disjointM`, `footprint(guarded) ∩ footprint(M) = ∅` avec `M = mutexOf s g`, le parent structurel de `slot` (C13.4) ; `sharedMutable : K.SharedMutable(ctl)` (C13.6) ; `ctlUnique`, pas d'autre entrée vivante sur `ctl` (C13.8). `available : NoCoveringDesc` est maintenant cité en C13.9 | C13 |
| `NewMutexOk` | `L adm s reg c g` | `k L adm s reg c g` | C13 |
| `UnlockOk` (`SyncLib.lean:274`) | inchangée | inchangée. Vérification clause par clause : C17.1 `e.Live ∧ grant = some g` ; C17.2 et C17.3 = `ReleasePre` (O3 §62.1–§62.4, dont `noActiveDesc` et `anchors`) ; C17.4 = `CtrlRight`. Aucun écart ; seule la docstring change (la mise à jour du contrôleur est une obligation de réalisation) | C17 |
| `ResetLockOk` (`SyncLib.lean:284`) | sans `L`, C18.1 et C18.2 | paramètre `L`, ajout de `OptP (ControlOf L s e) (Usable ∧ isLeaf) False` (C18.3, voir problème W3) | C18 |
| `Encap` (`SyncLib.lean:332`) | — | définition inchangée ; docstring : C22.1, C22.2, C22.3 ; C22.4 sans contenu dans `S_C` (Spec 1 §41) | C22 |
| `JoinStep` (`Frames.lean:407`) | constructeur `ok` seulement | ajout de `reject : s.Live c → s.C[d]? = none → JoinStep s c d .reject` ; un contexte vivant n'a toujours pas d'issue | C8 |
| `SpawnPreBase` → `SpawnPre` (`Frames.lean:318`) | mêmes 5 champs | renommée ; docstrings C4.1, C4.3, C4.5 (voir §3) | C4 |
| Composite par valeur (`Transfer.lean`) | `spawnValEff` = `spawnEff` puis O4 ; `SpawnValPreBase` incomplète ; deux lectures `SrcRightBefore` et `SrcRightAfterSpawn` ; pas de relation | réécrit : `spawnCreate` (C5.1), `transfersEff` dans l'ordre déclaré (C5.2), `yieldEff` (C5.3), `spawnValEff` ; `ValTransferPre` évaluée au début de chaque phase de transfert ; `ValTransfersPre` récursive ; `SpawnValPre` (11 champs) ; relation `SpawnValStep`. `SrcRight*`, `readings_differ` et `readingA_final` sont supprimés | C4, C5 |

Détail de `SpawnValPre` (`Transfer.lean:130`) :

- **Avant le composite** : `creatorLive` (C4.1) ; `params` (C4.3, C5.3) ; `localsOK` (C4.5).
- **Destinations** : `freshDst` (C5 item 2).
- **Phases de transfert** (`transfers`, C5.2, C5 items 1, 3, 4) :
  - par argument : §63.1 côté source (usable, droit `Modify`) et côté destination (usable seulement) ;
  - §63.2, §63.3, §63.4, §63.5, et §63.6 première moitié ;
  - §63.8, lu sur l'état final.
- **Paramètres** : `paramsApart`, test sur les footprints des sources dans l'état avant le composite (C5 item 5) ; `paramsAtYield` (C5.3).
- **État final** (C5.4) :
  - `anchorOrder` (§63.6) ;
  - `dstUsableAfter` (§63.9) ;
  - `originHidden`, O6.3 vu depuis le contexte créé ;
  - `anchorOrderHeld`, O6.4, qui contient §63.7.

P1 (`Context.lean`, `Frames.lean`) :

- **Confirmation.** `alloc` exécuté par `c` passe par `ViewStep`, qui évalue `AllocStep` sur `s.view c`.
- **Théorèmes.** `alloc_ok_satisfiable` (`Frames.lean:282`) et `alloc_fail_unsatisfiable` l'énoncent.
- **Docstring.** Celle de `SC.view` cite C2 (P1).

## 3. `SpawnPre` comparée à `EnterPre`

| `EnterPre` (`Access/Ops.lean:498`) | `SpawnPre` | Différence |
|---|---|---|
| `callerLive : s.F ≠ []` (§72.1) | `creatorLive : s.stk c ≠ []` (C4.1) | réindexation (pile locale de `c`) |
| `params` sur `s` (§72.1) | `params` sur `s.view c` (C4.3) | aucune autre |
| `localsOK` (§72.2) | `localsOK` (C4.5) | identique |
| `originHidden` sur `enterEff s ps ls` (§72.3) | `originHidden` sur `(spawnEff s c ps ls).view s.C.length` (C4.5) | état final vu depuis le contexte créé (C4.5) au lieu du contexte appelant |
| `anchorOrderHeld : AnchorOrderHeld (enterEff …)` (§72.4) | `AnchorOrderHeldC (spawnEff …)` (C4.5) | sur `ancestorC` |

- **Clauses ajoutées.** Aucune : `SpawnPreBase` avait déjà les cinq clauses.
- **Placement sur la pile.** `spawnEff` crée une pile `[nF]` au lieu d'empiler `nF`.
- **§72.2 « modes, footprints, anchoring, parameter-passing ».** Cette partie n'est représentée ni dans `EnterPre` (sa docstring le dit) ni dans `SpawnPre`.
- **C4.2 et C4.4.** Elles tiennent par construction de `spawnEff`.

## 4. Théorèmes

Vérifications :

- `lake build` réussit, sans avertissement.
- Le `grep` d'`AGENTS.md` est vide ; aucun `noncomputable`.
- Audit `collectAxioms` sur les 746 théorèmes `Ern.Concurrency*` : aucun axiome hors `{propext, Quot.sound}`.
- `#print axioms` sur `spawnVal_preservesC`, `transfer_merges_controllers`, `realizability`, `encapsulated_inv`, `encapsulated_inv_noTransfer`, `lstep_ctlUnique`, `s4_detached_child`, `conservative_deriveSync`, `deriveSync_observe_rejected` et `deriveSync_breaks_i2_false` donne `[propext, Quot.sound]`.

### T1 (conservativité)

- **`syncAuthorized_false`, `conservative_deriveSync`** (`SyncLib.lean:376`) : re-prouvés.
  - Les deux portent maintenant sur `kc : KC SyncReg`.
  - Le registre passé à `SyncAuthorized` est celui de `SyncSound kc reg s` : `¬ kc.SyncAuthorized reg s g f` et `¬ DeriveSyncStep kc reg s c g (.ok s')`.
- **Autres énoncés de `Conservativity.lean`** : inchangés. `git diff 14d2541 HEAD` ne montre que des docstrings dans `Conservativity.lean`, `Context.lean` et `Reparent.lean`.

### T2 (préservation de `KInvCA`)

- **`deriveSync_preservesC`** (`Preservation.lean:1857`) : re-prouvé sans l'hypothèse `hmode`, pour tout `R`, `kc : KC R` et `r : R`. Le mode vient de `DeriveSyncPre.mode` (C15.1). Énoncé modifié : une hypothèse en moins.
- **`lstep_kInvCA`** (`Reachable.lean:28`) : re-prouvé sans l'hypothèse `SyncInv`, qui ne servait qu'au mode. Énoncé modifié : une hypothèse en moins. Le lemme `guarded_mode` est supprimé.
- **`spawn_preservesC`** sur `SpawnPre` : preuve inchangée.
- **`join_preservesC`** : preuve inchangée ; le cas `reject` n'a pas d'issue `ok`.
- **`spawnVal_preservesC`** (`TransferPreserve.lean:299`) : **nouveau, prouvé**. `KInvCA s → SpawnValStep k s c ps ls vs (.ok s') → KInvCA s'`, sans hypothèse supplémentaire. Structure de la preuve :
  1. La cession commute avec chaque transfert (`yield_transfer`, `yield_transfers`) : les paramètres sont tenus par des frames, et O4 ne déplace que les autorités tenues par des parties de la source.
  2. Création puis cession égale `spawnEff` avec paramètres (`create_yield`).
  3. Les invariants hors ordres d'ancrage (`KBase`) passent de `spawn` aux transferts. La preuve réutilise `transfer_wf3'`, `transfer_base'`, `transfer_heldAnchored'` et `transfer_rootHeldConv'`.
  4. L'utilisabilité de chaque destination après son transfert vient de ce qu'elle appartient à une frame (`spawn_frameOwned`, `transfer_usable_frameOwned`).
  5. `AnchorOrderC` et `AnchorOrderHeldC` sont les vérifications finales de C5.4.

### T4 (`SyncInv`, `GrantDiscipline`)

**Réfuté pour la clause C21.4, première phrase (unicité des contrôleurs) ; prouvé pour toutes les autres clauses.** Contre-exemple : problème W1 (§6).

- **`lstep_preserves`** (`SyncPreserve.lean:1291`) : énoncé modifié.
  - Conclusion : `SyncCore`, toutes les clauses de `SyncInv` sauf `ctlUnique`, plus `GrantDiscipline`. Elle vaut pour tout pas sous `Encap`.
  - `SyncCore` (`SyncPreserve.lean:60`) et `syncState_iff : SyncState ↔ SyncCore ∧ CtlUnique` sont nouveaux.
- **`lstep_ctlUnique`** (`SyncPreserve.lean:1325`) : nouveau. Tout pas sous `Encap` dont l'étiquette n'est pas un `transfer` noyau préserve `CtlUnique`. `newMutex` utilise C13.8.
- **`lstep_syncState`** (nouveau) : `SyncState` est préservé par tout pas encapsulé qui n'est pas un `transfer`.
- **`trace_preserves`** : énoncé modifié, `SyncCore` le long de toute trace encapsulée.
- **`trace_syncState`** (nouveau) : `SyncState` le long des traces encapsulées sans `transfer`.
- **`trace_inv`, `encapsulated_inv`** (`Reachable.lean:52`, `:101`) : énoncés modifiés, conclusion `KInvCA` (ou `KInvC`) et `SyncCore`.
- **`trace_inv_noTransfer`, `encapsulated_inv_noTransfer`** (nouveaux) : `KInvC ∧ SyncInv ∧ GrantDiscipline` sur les traces encapsulées sans `transfer`.
- **`init_inv`** : re-prouvé avec `SyncState` étendu.
- **`newMutex_nonleaf_rejected`** : re-prouvé sur `NewMutexPre`.

Hors du champ de T4 :

- **`LStep` n'a pas d'étiquette pour le composite par valeur.** Sa préservation de `SyncCore` n'est donc pas énoncée.
- **`EncapTraces.invA` et `invB`.** Ils obtiennent `SyncCore` par `trace_inv` et l'unicité par `ctlUnique_single` (registre d'une entrée).

### T5 (réalisabilité)

`realizability` est re-prouvé. Il fournit en plus `DeriveSyncPre.mode`, tiré de `SyncInv.guarded`.

L'instanciation n'a pas changé : `libKC`, `LibSyncAuthorized` et `EntryAuth`. Elle ne contient que :

- C14.1 : entrée vivante ;
- C14.2 : `grant = none` ;
- C14.3 : `CtrlRight`.

### Nouveaux théorèmes de test

- **S4** : `s4_steps`, `s4_detached_child` (`Traces.lean:283`). Déroulement :
  1. Le contexte 0 entre dans une frame 1 avec deux locales, les initialise et alloue `T` possédée par `v`.
  2. Il crée le contexte 1 par le composite, avec `v` déplacé dans la locale `d`.
  3. La frame 1 sort.

  Résultat : le contexte 1 est vivant et rattaché à la frame 0 ; `d` et `T` sont utilisables ; l'autorité racine de `T` est tenue par `d`. `KInvC`, donc `ConcurrentWF`, tient.
- **C8** : `join_unknown_rejected`, et `join_waits` mis à jour avec le cas `reject`.
- **S16** : `slot_transfer_breaks_control` est conservé. Sa docstring cite C22.3 et S16, et sa preuve passe par `trace_inv_noTransfer`.

### Théorèmes ouverts

Aucun énoncé demandé ne reste sans preuve ou réfutation.

## 5. Contre-exemples devenus rejets

| Avant | Après | Jumeau positif |
|---|---|---|
| `deriveSync_breaks_i2` (`ok` depuis une autorité `Observe` d'empreinte vide, puis I2 violé) | `deriveSync_observe_rejected` : avec un `SyncAuthorized` toujours vrai, le même `deriveSync(3)` est `reject` par C15.1. `deriveSync_breaks_i2_false` prouve la négation de l'ancien énoncé pour tout `KC R` | `deriveSync_modify_ok` : `deriveSync(0)` sur la racine `Modify` est `ok` |
| `shared_controller` (deux `newMutex` sur le même contrôleur acceptés) | `shared_controller_rejected` : le second `newMutex` est rejeté (`¬ NewMutexPre`) par C13.8 | `distinct_controllers_ok` (S9) : deux valeurs mutex aux contrôleurs `lock₁` = 2 et `lock₂` = 5, deux `newMutex` acceptés |
| `readings_differ` (D2, deux lectures possibles) | `spawnVal_covering_rejected` : le paramètre 3 couvre la feuille 0 de la source, `reject` par C5 item 5 | `spawnVal_apart_ok` : même composite sans paramètre, `ok`. Feuille 0 `Moved`, feuille 3 `Init` |

## 6. Problèmes de WC3

### W1. C21.4 n'est pas préservée par un `transfer(M, M′)` admis par C22.3

Passages concernés :

- **C12** : « A legal transfer of the whole mutex value `M` […] may carry `slot` and its controller together and preserve the association positionally ».
- **C21.4** : « Distinct live entries have distinct `ControlOf` leaves ».
- **C22.3** : la restriction porte sur « source equality with `slot` ».
- **C23** : « Formalization must demonstrate preservation of […] `SyncInv` (including controller uniqueness […]) ».

Contre-exemple `EncapTraces.transfer_merges_controllers` (`EncapTraces.lean:258`). Statique :

- `M = {slot, lock}`, champs `Init`, avec `T` possédée par `slot` : `guarded₁` = autorité racine 1 de `T`, tenue par `slot` (RootHeld) ;
- `M′ = {slot′, lock′}`, champs `Uninit`, avec `T′` possédée par `slot′` : `guarded₂` = autorité racine 3, tenue par `slot′`.

Depuis l'état initial à registre vide, la trace encapsulée est :

1. `newMutex(1)`, acceptée avec contrôleur `lock` = 2 ;
2. `newMutex(3)`, acceptée avec contrôleur `lock′` = 6, distinct (C13.8) ;
3. `transfer(M, M′)`.

Le troisième pas est `ok` par O4 : les feuilles de `M′` ne sont pas `Init`, ce qui satisfait §63.3. `Encap` l'admet, puisque la source est `M`. État obtenu :

- `KInvCA` et `SyncCore` tiennent ;
- les deux entrées sont vivantes ;
- `guarded₁` et `guarded₂` sont tenues par `slot′` ;
- `ControlOf` vaut 6 pour les deux entrées ;
- `SyncInv` est faux.

Ce cas suppose un `guarded` tenu comme racine possédée par un champ `Uninit`. C13.1 et C13.5 l'admettent : C13.5 ne contraint que le cas stocké par O8. Avec l'arrangement de référence de C13.5, le `guarded` est stocké par O8, ce qui rend `slot′` `Init` ; §63.3 rejette alors ce transfert. Je n'ai pas vérifié si cet arrangement exclut la fusion dans tous les cas.

### W2. C15.3 : l'alternative « tenue par la frame courante » de `ExercisableAt` reste-t-elle ?

C15.3 : « In place of **only** the holder-mediated exercisability alternative of `ExercisableAt(guarded, Modify)` in O1.1, `K_C.SyncAuthorized(…)` holds. »

Lecture littérale : seule la seconde alternative de §43 est remplacée, et la première (« held by the current frame ») demeure. La condition devient alors `actif ∧ mode ∧ (tenue par la frame courante ∨ SyncAuthorized)`.

Le modèle suit le brief (« le reste inchangé ») : `SyncAuthorized` est la seule autorisation.

Exemple où les lectures divergent : registre vide, `guarded` = autorité racine 0 `Modify` tenue par la frame courante (état `wd` de `DeriveSyncWitness`, sous `libKC`).

- Lecture littérale : `deriveSync(0)` est `ok`, et `conservative_deriveSync` (T1) devient faux.
- Modèle : `reject`.

Les deux lectures coïncident quand `guarded` est le `guarded` d'une entrée vivante sous `SyncInv` : il est alors tenu par une place (C21.1), et la première alternative ne s'applique pas. Elles diffèrent pour un `deriveSync` brut sur une autorité tenue par la frame courante, quel que soit le registre.

### W3. C18.3 « The controller association is valid » n'est pas défini

Le modèle lit C18.3 comme la validité du contrôleur de C21.3, qui porte le titre « Controller validity » : `ControlOf(entry)` est une feuille utilisable. La seconde moitié (« does not invalidate surviving dependent authorities ») tient par construction : `resetLock` ne change pas l'état noyau.

Sous `SyncInv`, la clause ajoutée est toujours vraie pour une entrée vivante. `ResetLockOk` exige `ExercisableAt(guarded)`, donc une entrée vivante.

### W4. C5.3 « its transmission must remain legal when the yield phase is performed »

« Legal » n'est pas défini. Le modèle lit la condition de §72.1 (paramètre actif, dérivé, tenu par la frame du créateur) réévaluée sur l'état d'entrée de la phase de cession (`paramsAtYield`).

### W5. Clauses sans contenu dans `S_C`, non représentées

- C13.3, seconde phrase (non-falsifiabilité par l'interface sûre) ;
- C13.6, seconde moitié (protocole du contrôleur applicable) ;
- C13.10 (état initial du contrôleur et du registre) ;
- C22.4 (protocole d'écriture du contrôleur) ;
- obligations de réalisation de C17 et C18.

## 7. Décisions de représentation

1. **`KC (R : Type)`.**
   - Le registre est le premier argument de `SyncAuthorized`, comme le demande le brief ; WC3 C14 écrit `(state, sync_registry, …)`.
   - `CStepS kc r` est paramétré par le registre.
   - `libKC k L : KC SyncReg` ne prend plus le registre ; `LStep` passe le registre courant.
2. **C15.1.** « own mode permits `Modify` » est encodé `Mode.modify.le y.mode`, l'encodage de §43 dans `S3.ExercisableAt`.
3. **`CtlUnique`.** Les entrées sont comparées par indice dans le registre, comme `unique`.
4. **`mutexOf`.** C13.4 évalue `footprint(M)` sur le parent structurel de la place qui tient `guarded`.
5. **`JoinStep`.** « Unknown to the execution » est lu comme `s.C[d]? = none` : les identités de contexte sont les indices de `C`, et aucun contexte n'est retiré.
6. **Composite par valeur.**
   - Les arguments par valeur forment une liste ordonnée `vs : List (Nat × Nat)`.
   - Les phases sont des fonctions d'effet.
   - Les clauses de phase sont récursives sur `vs` (`ValTransfersPre`) et évaluées sur l'état produit par les transferts précédents.
   - §63.8 est évaluée sur l'état final (C5.4), pour les autorités tenues par une partie de la source avant le transfert.
   - §63.7 est couverte par O6.4 (`AnchorOrderHeldC` de l'état final), qui contient la condition sur les autorités déplacées.
   - C4.2, C4.4 et C5 item 6 (aucune duplication) tiennent par construction des effets.
7. **`SyncCore`, `Label.NotTransfer`.** Ce sont des moyens d'énoncé pour les résultats partiels de T4 (§4). Ils ne changent aucune définition de WC3.

## 8. Écarts avec la Spec 1

Aucune clause gelée n'est modifiée.

Les règles candidates de WC3 diffèrent de la Spec 1 sur trois points :

- **`deriveSync`** remplace l'autorisation par le détenteur de §60.1 par `SyncAuthorized` (C15.3).
- **Composite (C5).** Il remplace l'exercice `Modify` côté destination de §63.1 par la condition de destination fraîche (C5 item 3). Il évalue aussi §63.6 (seconde moitié), §63.7, §63.8, §63.9, §72.3 et §72.4 sur l'état final du composite, au lieu de l'état résultant de chaque opération.
- **`ResetLockOk`, `NewMutexPre`, `UnlockOk`** sont des opérations de bibliothèque, hors noyau.
