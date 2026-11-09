# Spec 2, jalon 1 — passe corrective WC3.1

Branche `formal/spec2-m1`. Sources : WC3 (`ERN_Concurrency_Model_WC3_corrige.md`) amendée par « WC3.1 — Targeted Corrections » (C13, C21, C22.3, C15.3, C18.3, C5.3, « Formalization coverage »), non commitées ; Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md`.

Commit : `6be4024`. Il est groupé : `Encap` prend désormais `L`, `SyncInv` passe à 9 champs et `Label` gagne `spawnVal`, ce qui casse tous les modules qui en dépendent. Le rapport fait l'objet d'un commit séparé.

Vérifications :

- `lake build` réussit, sans avertissement.
- Le `grep` d'`AGENTS.md` est vide ; aucun `noncomputable`.
- Audit `collectAxioms` sur les 795 théorèmes `Ern.Concurrency*` : aucun axiome hors `{propext, Quot.sound}`.

## 1. Résultat principal : T4 complet est faux sous `Encap` seul

L'obligation de WC3.1 (« Formalization coverage ») est la préservation de `SyncInv` complet et de `GrantDiscipline` par toute transition admise par `Encap`. Elle **n'est pas déchargeable** : O12 `endUse` (Spec 1 §69) casse l'invariant d'initialisation de WC3.1 C21, et `Encap` ne l'exclut pas. La règle qui habilite le pas est l'effet `ok` de §69 :

> The leaves of value `place` become `Uninit`; `place` remains usable as a place.

`endUseS` ne libère que les autorités tenues **dans** `place`. Deux cas laissent donc l'entrée vivante :

| Pas | Clause cassée | Théorème |
|---|---|---|
| `endUse(ctl)` | `ctlInit` | `EncapTraces.endUse_ctl_breaks_ctlInit` (`EncapTraces.lean:240`) : trace encapsulée `derive`, `store`, `newMutex`, `endUse(lock)` depuis l'état initial ; `KInvCA` tient, l'entrée est vivante, `lock` est `Uninit`, `SyncInv` est faux |
| `endUse(q)`, `q` partie stricte de `slot` | `slotInit` | `EncapTraces.endUse_slotPart_breaks_slotInit` (`:278`) : `slot = {a, b}` possède `T`, `guarded` est la racine de `T` ; `newMutex`, puis `endUse(a)` ; `a` est `Uninit`, l'entrée est vivante |

L'unicité des contrôleurs (C21.4) en dépend aussi, le long des traces. `EncapTraces.endUse_then_transfer_merges` (`:331`) en donne un exemple, tous les pas étant admis par `Encap` :

1. `newMutex` sur deux mutex `M₁` et `M₂` à `slot` structurés ;
2. `endUse` des deux feuilles de `slot₂`, puis de `lock₂` ;
3. `transfer(M₁, M₂)`, accepté par §63.3 puisque `M₂` n'a plus de feuille `Init`.

Les deux entrées, vivantes, ont alors le contrôleur `lock₂`.

**Clause minimale de C22 proposée** (non ajoutée à `Encap`) : définie comme `EndUseExcl` (`SyncInit.lean:21`).

> While an entry is live, the safe mutex abstraction does not expose `endUse` whose place is the controller leaf `ctl` or a strict structural subplace of `slot`.

- **Nécessité de chaque cas.** Elle est montrée par les deux contre-exemples ci-dessus.
- **Cas non exclus.** `endUse(slot)`, `endUse(M)` et `endUse` d'un englobant de `M` libèrent `guarded`, tenu dans la place : l'entrée meurt. `endUse` d'un possesseur de `M` tue `slot` (le nettoyage libère `guarded`).
- **Suffisance.** Elle est prouvée : voir T4 au §3.

La décision de conception reste ouverte, comme l'exige WC3.1.

## 2. Définitions modifiées

| Définition | Avant (WC3) | Après (WC3.1) | Clause |
|---|---|---|---|
| `slotOf` (`SyncLib.lean:144`) | — | place qui tient `guarded` | WC3 C12 |
| `SlotInit`, `CtlInit` (`:179`, `:185`) | — | feuilles structurelles de `slotOf` `Init` ; `ControlOf(e)` `Init` ; sur les entrées vivantes | WC3.1 C21 |
| `SyncInv` (`:190`) | 7 champs | 9 champs : `slotInit`, `ctlInit` ajoutés | WC3.1 C21 |
| `NewMutexPre` (`:234`) | 10 champs | 11 : `initM : OptP (mutexOf s g) (fun m => ∀ l ∈ footprint s.P m, s.I l = .init) False` | WC3.1 C13 |
| `TransferExcl` (`:363`, avec instance `Decidable`) | — | pour toute entrée vivante : `¬ partOf P src slot` (items 1 et 2) et `ControlOf ≠ some src` (item 3) | WC3.1 C22.3 |
| `Encap` (`:383`) | `Encap st`, transfert : `holder ≠ place src` | `Encap L st` ; transfert : `TransferExcl L st src` ; `.spawnVal` : `EncapVals`, chaque source à l'état de sa phase de transfert | WC3.1 C22.3, « Formalization coverage » |
| `Label`, `LStep` | 9 étiquettes | ajout de `.spawnVal c ps ls vs` et du constructeur `LStep.spawnVal` sur `SpawnValStep` | WC3.1 « Formalization coverage » |
| `ResetLockOk` (`:311`) | inchangée | docstring WC3.1 C18.3 ; le champ existant (`ControlOf` feuille utilisable, C21.3) y correspond | WC3.1 C18.3 |
| `DeriveSyncPre` (`Sync.lean`) | inchangée | docstrings : `authorized` est l'autorisation exclusive | WC3.1 C15.3 |
| `SpawnValPre.paramsAtYield` (`Transfer.lean`) | inchangée | docstring WC3.1 C5.3, qui coïncide avec la lecture de la passe précédente | WC3.1 C5.3 |

Écart au brief :

- **`initM`.** Le brief écrit `∀ l ∈ footprint s.P (mutexOf s g)`. `mutexOf` est une `Option`, d'où la forme `OptP … False`. Si `mutexOf` vaut `none`, `newMutex` est rejeté ; `control` le rejette déjà dans ce cas.

Énoncés changés par répercussion :

- **`lstep_preserves`.** Il prend `KInvCA st.1` au lieu de `WF3 st.1.flat`, car le cas `spawnVal` a besoin des états intermédiaires. Il prend aussi `hx : EndUseExcl L st lbl`.
- **`trace_inv`, `trace_preserves`, `encapsulated_inv`.** Ils portent sur `ProposedTrace` (`SyncInit.lean:970`) : chaque pas satisfait `Encap` et `EndUseExcl`. `ProposedTrace.encap` le ramène à une `EncapsulatedTrace` ; `ProposedTrace.of_encap` couvre les traces encapsulées sans `endUse`.
- **`transfer_preserves`** (version `SyncCore`) devient `transfer_core`, au niveau de l'effet, pour servir aussi aux phases du composite.

## 3. État de T4

- **`lstep_preserves`** (`SyncInit.lean:934`). Tout pas sous `Encap` et `EndUseExcl` préserve `SyncState`, c'est-à-dire `SyncInv` complet et `GrantDiscipline`. Cela inclut `transfer`, le composite par valeur et toutes les opérations noyau et de bibliothèque.
- **`trace_inv`, `trace_preserves`, `encapsulated_inv`** (`Reachable.lean:50`, `:61`, `:94`) : mêmes conclusions le long d'une `ProposedTrace`. `encapsulated_inv` part de l'état initial.
- **`init_inv`** : re-prouvé avec les 9 champs.
- **Sans `EndUseExcl`** : réfuté (§1).

Retirés, car rendus inutiles par les théorèmes complets : `Label.NotTransfer`, `lstep_ctlUnique`, `lstep_syncState`, `trace_syncState`, `trace_inv_noTransfer`, `encapsulated_inv_noTransfer`, `ctlUnique_single`, `merge_steps`. `SyncCore` reste, mais seulement comme décomposition interne des lemmes par opération de `SyncPreserve.lean` (`:57`), jamais en conclusion d'un théorème T4.

## 4. Inductivité de l'initialisation, par opération

Liste des opérations et des lemmes qui portent la preuve ; toutes préservent `slotInit` et `ctlInit` sous `SyncState` et `Encap`, sauf la ligne O12.

| Opération | `slotInit`, `ctlInit` | Lemme |
|---|---|---|
| O1 `derive`, O2 `split`, O3 `release`, O5 `depend`, O9 `read`, O15 `pin`, O16 `unpin`, O7 `exit`, O13 `free` | préservés : `I` inchangé, empreintes des places existantes inchangées | `opStep_init` (`SyncInit.lean:210`), `init_step` (`:311`), `facts_syncState` (`:353`) |
| O8 `store`, O10 `write`, O11 `writeShared` | préservés : seuls des passages à `Init` | idem |
| O6 `enter`, O14 `alloc` | préservés : places ajoutées `Uninit`, anciennes inchangées (`Arena.footprint_shapeP`) | idem |
| O4 `transfer` | préservés sous WC3.1 C22.3 : si `slot` est dans la source, `guarded` passe à `corr(slot)` et le contrôleur à `corr(ctl)`, dans la destination, devenue `Init` ; sinon `slot` et `ctl` sont hors de la source (arbre, C22.3) | `transfer_syncState` (`:591`) |
| **O12 `endUse`** | **brèches** : `endUse(ctl)`, `endUse` d'une partie stricte de `slot` (§1) ; préservés sous `EndUseExcl` | `endUse_syncState` (`:387`) |
| `spawn` | préservé | `spawn_init` (`:302`), `facts_syncState` |
| composite par valeur | préservé : création, puis transferts sous `EncapVals`, la cession commutant avec les transferts | `spawnVal_syncState` (`:891`) |
| `terminate`, `join` | préservés : `I` et empreintes inchangés | `lstep_preserves` |
| `deriveSync` brut | exclu par `Encap` (C22.2) | `deriveSync_excluded` |
| `newMutex` | préservé : `initM` couvre `slot ⊆ M` et `ctl ∈ footprint(M)` | `newMutex_syncState` (`:721`) |
| `acquire`, `unlock`, `resetLock` | préservés : `I` inchangé, mise à jour d'entrée à `guarded` constant | `acquire_syncState`, `unlock_syncState`, `resetLock_syncState` (`:762`, `:780`, `:802`) |

**Unicité des contrôleurs.** Elle est préservée par chaque pas depuis `SyncState`. Pour `transfer`, deux arguments :

- **Contrôleur hors de la destination.** Le contrôleur d'une entrée non déplacée est `Init` (`ctlInit`). §63.3 garantit que la destination n'a aucune feuille `Init`, donc ce contrôleur n'est pas dans la destination.
- **Contrôleurs déplacés distincts.** `corr` est injectif sur les parties de la source (`corr_inj`, `SyncInit.lean:130`, nouveau).

Le long des traces, elle ne tombe qu'après une brèche d'`endUse` (`endUse_then_transfer_merges`). La même clause proposée l'exclut.

## 5. Rejets et jumeaux

| Énoncé | Verdict | Jumeau |
|---|---|---|
| `newMutex_uninit_rejected` (`EncapTraces.lean:382`) | dans la configuration de l'ancien `transfer_merges_controllers`, `newMutex(1)` est accepté et `newMutex(3)` est rejeté par `initM` (`M′` `Uninit`) | — |
| `transfer_merges_controllers_false` (`:388`) | négation de l'ancien énoncé : la trace `newMutex(1)`, `newMutex(3)`, `transfer(M, M′)` n'est pas un `LRun` | — |
| `transfer_into_live_mutex_rejected` (`SyncInit.lean:1005`, général) | sous `SyncState`, un `transfer` dont la destination contient le mutex d'une entrée vivante est rejeté par §63.3 : son `ctl` est `Init` | `invA`, `invB` : `transfer(M, M′)` vers `M′` sans entrée est `ok`, et `SyncState` complet tient (`traceA` et `traceB` sont des `ProposedTrace`) |
| `ctl_transfer_breaks_ctlInit` (`EncapTraces.lean:219`, S16 étendu) | `transfer(lock, Y)` est `ok` dans le noyau et exclu par C22.3 item 3 ; sans l'exclusion, `ctlInit` est faux (`lock` `Moved`) | `controlAB` |
| `slot_transfer_breaks_control` (S16) | inchangé, re-prouvé ; exclu par C22.3 item 1 | `controlAB` |

`transfer_merges_controllers` est donc remplacé par la preuve de la négation de son ancien énoncé.

Traces existantes, verdicts inchangés :

- `mutex_trace`, `distinct_controllers_ok`, `shared_controller_rejected` et `s4_*` : leurs états satisfont déjà `initM`.
- `EncapTraces.est` : `slot` devient `Init` par le `store` qui précède `newMutex`.

## 6. Théorèmes inchangés, re-prouvés, ouverts

- **T1** (`syncAuthorized_false`, `conservative_deriveSync`, `Conservativity.lean`) : énoncés et preuves inchangés.
- **T5** (`realizability`) : énoncé inchangé ; la preuve compile sans modification, elle n'utilise que `SyncInv.guarded`.
- **T2** :
  - `lstep_kInvCA` (`Reachable.lean:26`) couvre le cas `spawnVal` (`spawnVal_preservesC`) ; énoncé inchangé.
  - `spawnVal_preservesC`, `deriveSync_preservesC` : inchangés.
- **Ouverts.** Aucun énoncé demandé n'est resté sans preuve ou réfutation. T4 sous `Encap` seul est réfuté (§1) ; sous `EndUseExcl`, il est prouvé.

## 7. Problèmes de WC3.1

### W1. C22 n'exclut pas `endUse`, alors que l'obligation de « Formalization coverage » l'exige

Exemple : `endUse(lock)` après `newMutex` (§1). Spec 1 §69 habilite le pas. La clause proposée est `EndUseExcl` (§1) ; la décision reste ouverte.

### W2. C18.3 : « the controller-validity requirements of C21 »

Depuis WC3.1, C21 contient aussi l'invariant d'initialisation de `ctl`. Le modèle garde la validité de C21.3 (feuille utilisable existante) et n'y ajoute pas `ctlInit`, qui n'est pas intitulé « controller validity ». Sous `SyncInv`, la différence est sans effet : `ctlInit` tient pour toute entrée vivante.

### W3. C22.3 et le composite par valeur : état d'évaluation de l'exclusion

« Même exclusion que transfer pour chaque source de vs » ne dit pas dans quel état comparer. Le modèle compare chaque source à l'état du début de sa phase de transfert (`EncapVals`), comme O4 dans C5.2.

La lecture « état avant le composite » donnerait les mêmes pas admis. Argument, non prouvé : une source ultérieure ne peut être une locale de l'enfant (le créateur n'y a aucun droit), et une ancienne place de `slot` déplacée est `Moved`, donc rejetée par §63.3.

## 8. Décisions de représentation

1. **`slotOf` et `SlotInit`.** « all structural leaves of its `guarded`-holding field `slot` » se lit comme les feuilles de `footprint(slotOf)`.
2. **`TransferExcl`.** Les items 1 et 2 de C22.3 sont réunis en `partOf P src slot` (`slot` lui-même ou une partie stricte).
3. **`EndUseExcl` et `ProposedTrace`.** La clause proposée est une hypothèse des théorèmes, hors d'`Encap` : WC3.1 interdit d'ajouter une restriction en silence.
4. **`lstep_preserves`.** Il prend `KInvCA` avant le pas : le composite a besoin de `WF3` à chaque phase, obtenu par `TransferPreserveAux.transfers_base`.
5. **Lemmes copiés.** `corr_leaf'` copie la preuve de `Ern.MemoryModel.Refinement.corr_leaf` ; `ctl_transfer_eq` reprend `ctl_transfer` de `SyncPreserve.lean` en identifiant le contrôleur après le pas.
6. **Lemmes de la Spec 1 réutilisés.** `Ern.MemoryModel.Arena.kstep_fp` et `footprint_shapeP` sont importés (empreintes des places existantes) ; leurs axiomes sont dans l'audit.

## 9. Écarts avec la Spec 1

Aucune clause de la Spec 1 n'est modifiée. `EndUseExcl` ne restreint pas O12 : elle restreint ce que l'abstraction sûre expose, comme C22.1–C22.3. Les opérations noyau gardent leurs préconditions et issues.
