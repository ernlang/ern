# Spec 2, jalon 1 — modèle abstrait concurrent : rapport

Branche `formal/spec2-m1`, créée depuis `main` (d0c2d87). Formalisation exploratoire, jamais mergée.
Candidate de conception : `ERN_Concurrency_Model_WC2.md` (Working Candidate 2 corrigée), non normative, non commitée.
Référence normative : `specs/ERN_Memory_Model_Specification_v0.1.md` (ci-dessous « Spec 1 »).

Modules créés sous `formal/Ern/Concurrency/` : `Context`, `Frames`, `Conservativity`, `Sync`, `SyncLib`, `Transfer`, `Traces` (table du brief), plus `Preservation`, `Reparent`, `SyncPreserve` et `Reachable` (théorèmes 2 à 4 et leur assemblage ; la table du brief ne leur assignait pas de module). Les opérations O1–O16 ré-indexées sont dans `Frames` avec les transitions de frames. Tous les modules sont importés par `Ern.lean`.

Vérifications finales : `lake build` (dans `formal/`) réussit sans avertissement ; le `grep` de `AGENTS.md` ne renvoie rien ; l'audit `collectAxioms` de tous les théorèmes `Ern.Concurrency.*` ne trouve aucun axiome hors `{propext, Quot.sound}` (§ b).

## (a) Passages lus et implémentés

### Lecture préalable (Spec 1, en entier)

§38 (état), §39 (frames), §40 (places, `Usable`, `RootHeld`), §41, §42, §43 (`effective`, `ExercisableAt`, `HasRight`), §44 (ancres effectives, `AnchorOrder`, `AnchorOrderHeld`), §45, §46, §47, §48, §49 (WF3), §50–§54 (I1–I4, `NoDangling`, `NoOrphan`), §55, §56, §57 ; §60–§73 (O1–O7, O8–O14, et §74–§75 O15–O16 lus avec eux) ; §76–§78 (O17–O19) ; §80 ; §82. WC2 : en entier (C1–C25, §IV, §V, §VI).

### Implémentation

| Passage | Lieu |
|---|---|
| WC2 C1, C2 (état `S_C`, contextes, cycle de vie, « current frame relative to the executing context », « globally live frame structure ») | `Context.lean` : `Life`, `Ctx`, `SC`, `SC.Live`, `SC.stk`, `SC.frames`, `SC.view`, `SC.flat`, `SC.set` |
| WC2 C3 (H1 : piles non vides, identités uniques, frame de base, parent de la frame initiale, `ancestor` étendu, bien-fondé) ; Spec 1 §39, §49.1 ré-indexés | `Context.lean` : `parIn`, `SC.ctxOf`, `SC.parC`, `SC.ancestorC`, `FramesC` |
| Spec 1 §44, §54 ré-indexés sur `ancestorC` | `Context.lean` : `EffAnchorOKC`, `AnchorOrderC`, `AnchorOrderHeldC` |
| WC2 C20 ; Spec 1 §49–§57 ré-indexés | `Context.lean` : `ConcurrentWF`, `Inv3baseC`, `Inv3C`, `NoOrphanC`, `KInvC` ; congruence par appartenance (`wf3_mem_congr`, `i3_mem_congr`, `noDangling_mem_congr`, `SC.wf3_view`) |
| Spec 1 §60–§75 exécutées par un contexte (WC2 C2) ; §63.6–§63.7, §64.3, §65.4–§65.5, §72.4, §73.5 lues sur `ancestorC` | `Frames.lean` : `ViewStep`, `TransferPreC`, `DependPreC`, `StorePreC`, `EnterPreC`/`enterEffC`, `ExitPreC`/`exitEffC`, `opStepC` |
| WC2 C6 (`exitFrameC` = O7 + reparentage, C6.3) ; Spec 1 §73 | `Frames.lean` : `reparent`, `exitEffC`, `ExitPreC` |
| WC2 C4 (`spawn` sur O6) ; Spec 1 §72 | `Frames.lean` : `spawnEff`, `SpawnPreBase`, `SpawnStep` |
| WC2 C7 (`terminate`) ; Spec 1 §73 | `Frames.lean` : `termEffC`, `TermPre`, `TermStep` |
| WC2 C8 (`join`) | `Frames.lean` : `JoinStep` |
| WC2 C24 | `Conservativity.lean` |
| WC2 C2, C14 (`K_C`, projection sur `K`, `SyncAuthorized` opaque) ; Spec 1 §48 | `Sync.lean` : `KC` (`extends K`, projection `KC.toK`) |
| WC2 C15 (`deriveSync`) ; Spec 1 §60 | `Sync.lean` : `DeriveSyncPre`, `deriveSyncEff`, `DeriveSyncStep`, `deriveSync_created`, `CStepS` |
| WC2 C12 (registre, vivacité, `ControlOf` positionnel) ; Spec 1 §46, §56 | `SyncLib.lean` : `SyncEntry`, `SyncReg`, `MutexLayout`, `SyncEntry.Live`, `ControlOf` |
| WC2 C14, C25 (instanciation de `SyncAuthorized` par la bibliothèque ; obligation « unavailable outside the corresponding valid synchronization contract ») | `SyncLib.lean` : `CtrlRight`, `EntryAuth`, `LibSyncAuthorized`, `libKC`, `SyncSound`, `libKC_sound` |
| WC2 C21 (items 1, 2, 3, 5), C22 | `SyncLib.lean` : `SyncInv`, `CoveringDesc`, `NoCoveringDesc`, `GrantDiscipline` |
| WC2 C13, C16, C17, C18 ; Spec 1 §56, §62, §65.3 | `SyncLib.lean` : `NewMutexPreBase`/`NewMutexOk`, `AcquireOk`, `UnlockOk`, `ResetLockOk` |
| WC2 C22, C23, C25 (encapsulation comme hypothèse sur les traces) | `SyncLib.lean` : `Label`, `LStep`, `LRun`, `Encap`, `EncapsulatedTrace` |
| WC2 C5 ; Spec 1 §63 | `Transfer.lean` : `spawnValEff`, `FreshRootLocal`, `SpawnValPreBase`, `SrcRight`, `SrcRightBefore`, `SrcRightAfterSpawn`, `readings_differ` |
| Spec 1 §50 (I1) pour les grants | `SyncLib.lean` : `grants_exclusive` |
| WC2 §V (références seulement), traces minimales | `Traces.lean` |

Non formalisés (hors table du brief ou sans contenu formel) : C9, C10, C11 (descriptifs), C19 (administration synchronisée, `MetaRight`, Spec 1 §36), OB-C01 à OB-C06 (hors périmètre par construction, aucun modèle d'événements).

## (b) Audit des axiomes hérités

Méthode : script Lean (`collectAxioms` sur chaque théorème, et fermeture transitive des constantes utilisées par la valeur et le type de chaque théorème) exécuté sur `Ern` construit au commit d0c2d87. Les valeurs des théorèmes importés s'obtiennent par `ConstantInfo.thmInfo` (`value?` ne les renvoie pas).

1. `Ern.MemoryModel.Access.reachable_kinv` : `[propext, Quot.sound]`. De même `reachable_inv`, `init_kinv`, `kstep_preserves`, `op_preserves`.
2. Les 442 théorèmes des modules `Access/Main` (70) et `Access/Preserve/*` (Alloc 54, Common 1, DeriveSplitRelease 46, EndFree 71, Frames 112, Small 60, Transfer 28) : 342 dépendent de `[propext, Quot.sound]`, 64 de `[propext]`, 36 d'aucun axiome. Aucun ne dépend de `Classical.choice`.
3. Les trois preuves par `Classical.byContradiction` (`chainLen_step`, privé, `Access/Statics.lean:194` ; `Rename.perm_range_of_nodup`, `Access/Rename/Basic.lean:146` ; `Rename.shapeP_down`, `Access/Rename/Places.lean:264`) ont exactement 31 dépendants transitifs (34 théorèmes avec elles-mêmes), tous dans `Access.Rename.*` et `Access.StaticsConf.exists_renumber` : `Renumbered.{initRel, initSim, properties, reachable, reachable_back, rootIdx_α, rootPerm_perm, run, run_back, α.congr_simp, α.eq_1}`, `Sim.{run, run_back, run_back_any, step, step_back}`, `StaticsOK.renumbered`, `allocEff_down`, `allocEff_ren`, `alloc_corr`, `alloc_down`, `enterEff_down`, `enterEff_ren`, `enterPre_ren`, `enter_corr`, `enter_down`, `op_corr`, `op_down`, `renumber_renumbered`, `StaticsConf.exists_renumber`, `Renumbered.rootIdx_αg` (privé).
4. Dans tout `Ern` (3598 théorèmes), 136 dépendent de `Classical.choice` : les 34 ci-dessus et 102 autres de `Access.Rename.*`, `Access.StaticsConf.exists_renumber._proof_*` et trois lemmes privés de `Access/Statics.lean` (`idxOf_lt_of_key`, `iter_bound`, `nodup_length_le`). Les lemmes du cœur `List.perm_ext_iff_of_nodup` et `List.nodup_range`, utilisés par `perm_range_of_nodup`, dépendent eux-mêmes de `Classical.choice` ; la source de la dépendance des 102 autres n'a pas été détaillée.
5. Le jalon 1 ne réutilise aucun de ces 136 théorèmes : la bisimulation `StaticsOK` (b) n'est pas utilisée. Pas d'arrêt après l'audit.

Audit des modules créés : 635 constantes de théorème `Ern.Concurrency.*` (internes comprises), toutes à `{propext, Quot.sound}` ou moins. Ont été évités, parce qu'ils introduisent `Classical.choice` : `List.filter_eq_nil_iff` (→ `filter_nil_of`), `List.eq_nil_iff_forall_not_mem` (→ `nil_of_forall_not_mem` de la Spec 1), `List.getElem?_modify` (→ lemmes locaux `getElem?_modify'`), et `by_cases` sur l'égalité de `KernelOp`, qui n'a pas d'instance `DecidableEq` (→ analyse par constructeurs).

## (c) Théorèmes

Notation : `KInvCA s := KInvC s ∧ KAux s.flat ∧ HeldAnchored s.flat` (`Preservation.lean`) : l'invariant inductif de Spec 1 `reachable_inv` (`KInv`, `KAux`, `HeldAnchored`), ré-indexé. Les auxiliaires `KAux` et `HeldAnchored` ne sont pas des clauses de §57 ; ils valent dans l'état initial (`init_inv`) et l'énoncé sur les traces (`encapsulated_inv`) ne les suppose pas.

### Théorème 1 — conservativité (C24) : prouvé

Fragment : états à un contexte (`SC.Single`) munis de `FramesC`.

- `conservative_op` : pour chaque O1–O16, les issues coïncident une à une : `opStepC k op 0 s o → op.Step k s.toS3 (omap SC.toS3 o)` et réciproquement toute issue de Spec 1 sur `s.toS3` est l'image d'une issue concurrente. `conservative_ok` : une issue `ok` reste un état à un contexte, dont la projection est l'effet de Spec 1.
- `single_ancestorC` : `ancestorC` coïncide avec `ancestor` de §39 sur la pile (sous pile strictement décroissante, donnée par `FramesC` : `single_decreasing`).
- `single_anchorOrderC`, `single_anchorOrderHeldC`, `single_kInvC` : `AnchorOrderC`, `AnchorOrderHeldC`, `KInvC` coïncident avec `AnchorOrder`, `AnchorOrderHeld`, `FramesC ∧ KInv` de la projection.
- `reachable_decreasing`, `reachable_single` : tout état atteignable de Spec 1 (sous `DDSound`, `StaticsOK`) est la projection d'un état à un contexte avec `FramesC` et `KInvC` ; le domaine de `conservative_op` contient donc le domaine séquentiel atteignable.
- `syncAuthorized_false`, `conservative_deriveSync` : sans entrée vivante, sous l'obligation de C14 (`SyncSound`), `K_C.SyncAuthorized` est faux et `deriveSync` n'a pas d'issue `ok`. L'énoncé vaut pour tout état, pas seulement à un contexte. La bibliothèque satisfait l'obligation (`libKC_sound`).

### Théorème 2 — préservation (C20, C23) : prouvé, sauf `deriveSync` sans hypothèse de mode (réfuté) et `spawn` par valeur (ouvert)

- `opStepC_preservesC` (`DDSound k` pour `split`) : les quinze opérations héritées autres qu'O7, exécutées par un contexte, préservent `KInvCA`.
- `exitFrameC_preserves`, `terminate_preserves` : idem pour O7 ré-indexé (`exitFrameC`) et `terminate`.
- `spawn_preservesC` (précondition `SpawnPreBase`, donc toute lecture plus stricte de C4.6), `join_preservesC`.
- `deriveSync` : **réfuté** tel que défini : `deriveSync_breaks_i2` (D9). Prouvé sous l'hypothèse que `guarded` a le mode propre `Modify` : `deriveSync_preservesC`.
- `lstep_kInvCA` : tout pas étiqueté du noyau avec la bibliothèque (`LStep`) préserve `KInvCA`, sous `DDSound` et `SyncInv` ; `SyncInv` (C21.1) fournit le mode `Modify` de `guarded` pour `deriveSync` et `acquire`.
- **Ouvert** : le composite `spawn` par valeur, dont la relation n'est pas définie (D2).

Réutilisation de Spec 1 : les clauses lues seulement par appartenance viennent des lemmes de Spec 1 appliqués à `s.view c` (congruence d'appartenance) ; les ordres d'ancres sont prouvés à nouveau sur `ancestorC`. Les lemmes de Spec 1 qui prennent une structure de précondition contenant une clause d'ancêtre linéaire, ou qui sont privés, ont été recopiés dans `Preservation.lean` avec les seuls champs utilisés, chacun nommant le lemme recopié (`enter_wf`, `enter_rootHeld`, `enter_noDangling`, `enter_rootHeldConv`, les lemmes privés de `Preserve/Transfer` et de `Preserve/Small`, `endUse` et `free`).

### Théorème 3 — reparentage (OB-C13) : prouvé

Fragment : états avec `FramesC`, `WF3` et `AnchorOrderC` sur les frames vivantes (`Reparent.lean`).

- `exitEffC_ancestorC`, `termEffC_ancestorC` : les frames vivantes après le pas sont celles d'avant moins la frame sortante, et `ancestorC` après le pas coïncide avec `ancestorC` d'avant sur elles.
- `exitEffC_framesC`, `termEffC_framesC` : `FramesC` est préservé (bien-fondé, parents vivants, contextes enracinés, contexte initial inchangé).
- `exitEffC_reparent`, `termEffC_reparent` : la cible est le parent immédiat de la frame sortante (`s.parC f = some p`), et exactement les contextes vivants de parent `f` sont reparentés.
- `exitEffC_kernel`, `termEffC_kernel` : `A` et `D` sont ceux de l'effet de Spec 1 §73 sur la vue ; `P`, `I`, `dead`, `pins`, `nF` sont inchangés ; le reparentage ne change que `C`.
- `exitFrameC_anchorOrder`, `terminate_anchorOrder` : `AnchorOrderC` est préservé (ce n'est pas une précondition d'O7) et `AnchorOrderHeldC` est établi (§73.5).

### Théorème 4 — `SyncInv` et `GrantDiscipline` (C21–C23) : prouvé sous `EncapsulatedTrace` ; contre-exemple sans

- `lstep_preserves` (`SyncPreserve.lean`) : tout pas étiqueté pris sous `Encap` préserve `SyncState := SyncInv ∧ GrantDiscipline ∧ GrantSubtree ∧ RegBound`, avec pour seules hypothèses noyau `WF3` avant et après le pas (fournies par le théorème 2). `GrantSubtree` et `RegBound` sont des auxiliaires, pas des clauses de WC2 (D7).
- `trace_preserves`, `trace_inv` (`Reachable.lean`) : le long d'une `EncapsulatedTrace`, `KInvCA` et `SyncState` sont préservés ensemble ; `encapsulated_inv` : depuis l'état initial de Spec 1 §47 (un contexte, registre vide), tout état atteint par une `EncapsulatedTrace` satisfait `KInvC`, `SyncInv` et `GrantDiscipline`, sous `DDSound` et `StaticsOK`.
- `Encap` est un prédicat sur les pas d'une trace, jamais une précondition d'opération : pas de `derive` ni de `split` hérités depuis le `guarded` d'une entrée vivante, pas de `deriveSync` brut sur lui, pas de `transfer` dont la source est la place qui tient ce `guarded`.
- **Contre-exemple sans encapsulation** (`Traces.acquire_blocked_by_derive`, `Traces.derive_step`) : valeur mutex `m = {data, lock}`, `data` possédant la racine `T` ; après `newMutex(1)`, le propriétaire exclusif exécute `derive(1, [3], Observe)`, pas noyau habilité (O1) et non encapsulé ; l'entrée est vivante avec `grant = none`, `GrantDiscipline` est fausse et `acquire` n'a aucune issue `ok` (§60.2 : le mode effectif de `guarded` sur `T` est `Observe`). Jumeau positif : `acquire_enabled`, puis `unlock_enabled` et la trace encapsulée `mutex_trace`.

### Théorème 5 — réalisabilité (C25) : prouvé sous l'invariant noyau ; faux sous les seules hypothèses du brief

- `realizability` : sous `KInvC` (dont `WF3`, `I1`, `I2` servent), `SyncInv` et `GrantDiscipline`, l'instanciation de bibliothèque de `SyncAuthorized` pour la frame courante d'un contexte vivant entraîne `NoCoveringDesc s g` et `DeriveSyncPre (libKC k L reg) s c g` en entier : I1 pour le grant de footprint complet (§60.3) et chaîne d'origines active (§60.1) compris. `SyncAuthorized` n'est défini qu'avec des faits de registre et de contrôleur.
- **L'énoncé « sous `SyncInv ∧ GrantDiscipline` » seul est faux** (`Traces.realizability_needs_i1`) : dans un état où une autorité racine `Modify` sans lien de dérivation couvre aussi `T` (I1 violé), `SyncInv`, `GrantDiscipline` et l'instanciation tiennent, et la précondition de `deriveSync` échoue. L'hypothèse manquante est I1 (et `WF3`, `I2` pour les autres clauses).

### Théorème 6 — exclusivité des grants (§50) : prouvé

`grants_exclusive` : sous `WF3` et `I1` sur les frames vivantes, deux autorités actives distinctes de mode `Modify`, d'origine le même `guarded` et de footprint `footprint(guarded)` non vide, ne coexistent pas.

### Traces et non-vacuité (`Traces.lean`)

`c0_kInvC` (état initial à un contexte) et `f2_kInvC` (état à deux contextes après `spawn` depuis une frame d'appel) : `KInvC` n'est pas vide. `frames_run` : `enterFrame`, `spawn`, `exitFrameC` (le contexte 1 passe du parent 1 au parent 0), `terminate`, `join`. `join_waits` : `join` sur un contexte vivant n'a pas d'issue. `ancestry` : `ancestorC` à travers les contextes avant et après reparentage. `newMutex_nonleaf_rejected` (`SyncPreserve.lean`) : rôle de la clause « feuille » de `newMutex` (§ (e), correction).

## (d) Problèmes de la candidate

D1 à D6 et D8 ont arrêté la formalisation du point concerné : aucune interprétation n'a été choisie. Les définitions concernées portent le suffixe `Base` et ne contiennent que les clauses non ambiguës ; les théorèmes prouvés sur une relation `Base` valent pour toute lecture plus stricte. D7 et D9 sont apparus pendant les preuves ; ils sont traités par des hypothèses ou des auxiliaires nommés, avec contre-exemple ou justification.

**D1. « Invariants » parmi les préconditions (C4.6, C5.8, C6.5).** C4.6, sous l'en-tête *Preconditions* : « `AnchorOrderHeld` and the global authority invariants hold in the resulting state ». « Global authority invariants » n'est défini nulle part (Inv3 ? I1–I4 ? WF3 ?). Lu comme précondition, la préservation de ces invariants par `spawn` devient vraie par définition (le théorème 2 serait vide pour eux) ; lu comme obligation (convention de Spec 1 §49 dernier alinéa et §58 : la préservation est une propriété requise des transitions), c'est le théorème 2. Même question pour C5.8 (*Preconditions* du composite : « preserves WF3-corresponding requirements, I1–I4, AnchorOrder, AnchorOrderHeld, NoDangling, and NoOrphan ») et C6.5. Formalisé : `SpawnPreBase` (C4.1–C4.5 et la première moitié de C4.6) ; `exitFrameC` suit le brief (O7 + reparentage), C6.5 est traité comme obligation (théorème 3) ; `SpawnValPreBase` sans C5.8.

**D2. État d'évaluation des préconditions non résultantes du composite par valeur (C5.1, C5.4).** C5.4 fixe l'état final pour les conditions « resulting-state » d'O4, mais pas l'état d'évaluation des autres. Deux en dépendent : le droit du côté source d'O4.1 (C5.1) et l'exemption d'O4.4, parce que la partie `spawn` transfère les paramètres à la nouvelle frame. Exemple concret, vérifié par `decide` (`Transfer.readings_differ`) : frame 0 tient une dérivée `Modify` 3 sur la feuille 0 (sa locale), la transmet au contexte créé et transfère la valeur de la place 0 dans une locale fraîche (place 3) du nouveau contexte. Toutes les clauses de `SpawnValPreBase` sont vraies ; le droit source est vrai avant le composite (par l'autorité 3) et faux après la partie `spawn` (3 est tenue par la nouvelle frame et bloque la racine de la place 0, §43 cas 3). Selon la lecture, le composite est donc `ok` ou `reject`. Lecture (a) : le contexte enfant reçoit à la fois la valeur et une autorité `Modify` sur la feuille source devenue `Moved`. Non formalisé : la relation du composite. Même question, sans divergence constatée (non examinée), pour l'état d'évaluation des conditions résultantes de C4.5–C4.6 dans le composite (après la partie `spawn` ou après le composite).

**D3. `join` : identifiant inconnu et effet sur `C` (C8).** C8 exige que l'identifiant désigne un contexte connu dont l'état achevé est établi, mais ne donne pas l'issue pour un identifiant inconnu (`reject` ou non habilitée ?) ; il dit que `join` ne modifie pas `P`, `I`, `A`, `D` mais ne dit rien de `C` et `F_C` (un marqueur « joint » est-il prévu ?). Formalisé : seule l'issue `ok` est définie (état inchangé) ; contexte vivant : aucune issue (brief) ; identifiant inconnu : aucune issue, en attente d'arbitrage.

**D4. Associations de contrôleur distinctes (C12 contre C13).** C12 : « Different mutex instances must have distinct valid controller associations. » Aucune précondition de C13 ne l'assure (C13.7 porte sur l'identité de `guarded`). Avec le `ControlOf` positionnel, deux autorités `guarded` tenues par le même champ (deux racines de stockage possédées par `data`) ont le même contrôleur. Exemple vérifié (`Traces.shared_controller`) : statiques `m = {data, lock}`, `T₁` et `T₂` possédées par `data` ; `newMutex(1)` puis `newMutex(2)` sont acceptés et `ControlOf` vaut `lock` pour les deux entrées. C13.3 (« valid, non-falsifiable association ») le couvre peut-être, mais n'a pas de contenu formel. `SyncInv` ne contient donc pas la distinction des contrôleurs.

**D5. Clauses sans contenu formel.** Non formalisées, faute de définition : C21.4 (« Registry state and the permitted control operations remain coherent ») ; C13.3 pour « non-falsifiable » ; C13.4 (« Shared observations intended for the controller do not conflict structurally with the protected exclusive authority » : `ctl ∉ footprint(guarded)` serait une lecture) ; C13.6 (« declared appropriately for its mutation discipline » : `K.SharedMutable ctl` serait une lecture) ; C17.5 ; C18.3. C21.3 et C21.5 sont formalisés en lecture minimale explicite : contrôleur positionnel existant, feuille utilisable ; unicité de `guarded` parmi les entrées vivantes (C13.7). C18.4 est une obligation.

**D6. L'acquisition du contrôleur n'a pas d'effet représentable (C16.1, C17.5).** `S_C` ne porte pas de valeurs (Spec 1 §41 : états d'initialisation seulement) ; l'état « pris/libre » du contrôleur n'existe pas dans `S_C`. Conformément au brief, l'acquisition est représentée par le seul fait d'autorité (`CtrlRight`) et par `grant` dans le registre ; aucun `writeShared` sur le contrôleur n'est effectué par `acquire` ni `unlock`. La correspondance relève d'OB-C05.

**D7. `GrantDiscipline` n'est pas inductif seul (C22, C23).** `unlock` (C17) libère le grant `g` et pose `grant = none` ; `GrantDiscipline` n'est rétabli que si tout descendant actif de `guarded` couvrant une feuille protégée est `g` ou un descendant de `g` (O3.3 interdit alors tout descendant actif de `g`). Rien dans WC2 ne l'énonce ; C21.4 (« coherent ») le vise peut-être. Formalisé comme auxiliaire `GrantSubtree`. Second auxiliaire, `RegBound` (toute identité `guarded` enregistrée existe) : sans lui, une entrée morte dont l'identité n'existe pas encore deviendrait vivante à la création d'une autorité fraîche de même identité.

**D9. `deriveSync` perd la borne de mode propre (C15).** Le brief et C15 remplacent `ExercisableAt(source, Modify)` de §60.1 par `SyncAuthorized`. Or `ExercisableAt` porte aussi « le mode propre de `source` permet le mode demandé » ; §60.2 ne borne le mode que feuille par feuille et ne dit rien si le footprint est vide. C15 cite pourtant les « mode restrictions » parmi les exigences conservées. Contre-exemple (`Preservation.deriveSync_breaks_i2`) : état atteignable de Spec 1 où frame 0 dérive de la racine de la statique 0 une autorité 3 `Observe` de footprint vide ; avec un `SyncAuthorized` opaque vrai, `deriveSync(3)` crée une dérivée `Modify` d'une autorité `Observe` et viole I2 (§51). Avec l'instanciation de bibliothèque, `SyncInv` (C21.1) donne le mode `Modify` et la préservation tient (`lstep_kInvCA`). À arbitrer : `DeriveSyncPre` doit-il porter la borne, ou est-ce une obligation de `K_C` (C14 : « correct association with a live synchronization entry ») ?

**D8. Transposition d'O7.1 (C6, C7).** « The current frame is not the initial frame and has a surviving caller » : C6 parle d'une frame « non-base », mais C3 exige une pile non vide pour tout contexte vivant et C7 traite à part la sortie de la frame initiale d'un contexte. `exitFrameC` est donc défini pour une frame qui a un appelant dans sa propre pile, et `terminate` pour la frame initiale d'un contexte non initial ; C3 et C7 imposent cette lecture, signalée ici parce que C6 ne la formule pas.

## (e) Décisions de représentation prises ; décisions de conception proposées

### Prises (aucun programme accepté ni comportement ne change)

- Contextes : liste indexée par l'identité ; chaque `Ctx` porte sa pile (sommet en tête), son état de cycle de vie et le parent de sa frame initiale (C3 : un seul par contexte). `stk` d'un contexte non vivant est vide.
- `parC` dérivé des piles et des parents de contextes ; `ancestorC` suit `chain parC` ; le bien-fondé est représenté par l'ordre des identités (`FramesC.parent` : le parent précède l'enfant), conformément à Spec 1 §49 dernier alinéa. Sur les états à un contexte, cela ajoute « pile strictement décroissante » à WF3.1 ; tout état atteignable de Spec 1 la vérifie (`reachable_decreasing`, `reachable_single`).
- Vues : `SC.view s c` (pile de `c` d'abord, puis les autres frames vivantes) ; Spec 1 §43 ne lit la pile que par son sommet et l'appartenance, et les clauses de §49–§54 seulement par l'appartenance (`wf3_mem_congr` etc.) ; l'ordre des autres frames est donc sans effet sur ces clauses.
- `SyncAuthorized(state, guarded, requesting_frame)` reçoit la frame : `SC.viewAt` place cette frame au sommet.
- Les opérations de bibliothèque (`newMutex`, `acquire`, `unlock`, `resetLock`) n'ont qu'une issue `ok` (WC2 n'en définit pas d'autre) ; le blocage est une absence d'issue (brief).
- Traces : construites directement comme preuves des relations (préconditions décidées par `decide`), sans exécuteur ; un exécuteur sur le patron de `Corpus/Runner.lean` n'était pas nécessaire pour une dizaine de pas.
- Invariant inductif du théorème 2 : `KInvC` renforcé par les auxiliaires de Spec 1 (`KAux`, `HeldAnchored`) ; invariant inductif du théorème 4 : `SyncInv ∧ GrantDiscipline` renforcé par `GrantSubtree` et `RegBound`. Les énoncés à partir de l'état initial (`encapsulated_inv`) ne les supposent pas.

### Correction faite pendant le travail

`NewMutexPreBase.control` exigeait seulement que le `ControlOf` positionnel existe. La preuve du théorème 4 a montré qu'une valeur mutex dont le champ contrôleur n'est pas une feuille passait `newMutex` et violait `SyncInv.control`. C12 dit que `ControlOf` « identifies the synchronization-control leaf » : la clause exige maintenant que le contrôleur soit une feuille (commit ac538af). Ce n'est pas un choix d'interprétation : la version précédente disait moins que C12. `newMutex_nonleaf_rejected` montre l'état concerné : `KInvC` vrai, contrôleur `2` qui n'est pas une feuille, `newMutex` rejeté, et le registre résultant violerait `SyncInv`.

### Proposées, non prises (`DESIGN.md` ne les règle pas)

- **P1. `K.Satisfiable` dans le modèle concurrent.** `K` reste inchangé (C2) et `Satisfiable` prend un `S3` ; `alloc` exécuté par `c` l'évalue sur `SC.view s c`. Un `K` arbitraire peut distinguer deux linéarisations : à fixer (vue du contexte exécutant, ou `Satisfiable` sur `S_C` avec projection par l'état à un contexte).
- **P2. `K_C` instancié par l'état de bibliothèque.** L'instanciation `libKC k L reg` dépend du registre, qui varie le long d'une trace, alors que `K` est un paramètre fixe dans Spec 1. L'obligation de C14 est formalisée par état (`SyncSound kc reg s`). À fixer : `SyncAuthorized` prend-il l'état de bibliothèque en argument ?
- **P3. Positions déclarées de `ControlOf`.** `MutexLayout` (position du champ tenant `guarded`, position du contrôleur parmi les enfants ordonnés de la valeur mutex) est un paramètre unique de la bibliothèque (un seul type mutex de référence).
- **P4. Garde unifiée de Spec 1 §56 avec l'arène.** `newMutex` consulte le registre de synchronisation et une liste `adm` d'identités d'autres administrations ; `newArena` de `Ern.MemoryModel.Arena` ne consulte que le registre des arènes. Dans une bibliothèque combinée, `newArena` devrait consulter le registre de synchronisation (§56). Non fait (module Spec 1 inchangé).
- **P5. Style du jalon 4 de `DESIGN.md`.** Non pris : la sémantique reste relationnelle, sans modèle d'événements, et la question de la forme des contrats sous concurrence (DESIGN.md, *Unsafe contracts*) reste ouverte.

## (f) Écarts avec la Spec 1

- Spec 1 §39 et la formalisation de WF3.1 : le bien-fondé des parents de frames est implicite dans la liste. Avec plusieurs piles et des liens entre contextes, il devient une clause explicite (`FramesC.parent`). Sur les états à un contexte, `ancestorC` coïncide exactement avec §39 (`single_ancestorC`), conformément à C3.
- Spec 1 §58 : seules `ok`, `reject` et `fail` existent. L'attente (C8, C16) n'est pas une issue : c'est une transition non habilitée (brief). `Outcome3` n'est pas étendu.
- Spec 1 §57, I4 : `Read3Pre` dépend de la frame courante ; I4 ré-indexé est exigé pour chaque contexte (trivial, `i4_always`).
- Spec 1 §72.3 : la protection d'origine est évaluée avec le nouveau contexte comme contexte exécutant (C4) ; elle ne dit rien de l'exercice par le créateur, protégé seulement par la restriction de `effective` (§43 cas 3), comme C4 le dit.
- Aucune autre divergence trouvée : les seize opérations ré-indexées ont exactement les issues de Spec 1 sur les états à un contexte (théorème 1).
