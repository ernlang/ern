# Spec 2, jalon 1 — clôture sur WC4

Branche `formal/spec2-m1`. Sources : `ERN_Concurrency_Model_WC4.md` (non commitée, seule candidate citée) ; Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md`.

Commits de la passe :

- `9915575` : `Encap` avec C22.5, T4 sur `EncapsulatedTrace`, exclusions et jumeaux, traces. **Commit groupé** : le nouveau cas d'`Encap` casse les modules de test, où le cas `endUse` d'`Encap` valait `True`.
- `1b85c96` : docstrings WC3/WC3.1 → WC4.
- Le rapport fait l'objet d'un commit séparé.

Vérifications à `1b85c96` :

- `lake build` réussit (55 jobs), sans avertissement.
- Le `grep` d'`AGENTS.md` est vide ; aucun `noncomputable`.
- Audit `collectAxioms` : 798 théorèmes `Ern.Concurrency*`, dont 626 non internes. Aucun axiome hors `{propext, Quot.sound}` (§ B.7).

---

# Partie A — passe de clôture

## A.1 Passages lus

- **WC4 en entier.** Je l'ai comparée par `diff` à WC3 (texte reconstruit de la lecture de la passe WC3) et aux amendements WC3.1. WC4 est WC3 avec les amendements WC3.1 intégrés, plus quatre ajouts :
  - C22.5 ;
  - le paragraphe « Interface and realization obligations » de C13 ;
  - C21.7, numérotée ;
  - S17a, S17b et S18.

  Les autres clauses ont le même texte, numéros compris.
- **Spec 1 :** §69 (O12), §63.3 (O4), §70 (O13), §40 (parties structurelles).

## A.2 Définitions modifiées

| Définition | Avant (`31044c5`) | Après | Clause |
|---|---|---|---|
| `Encap` (`SyncLib.lean:385`) | cas `endUse` : `True` | cas `.kernel _ (.endUse p)` : pour toute entrée vivante `e`, `ControlOf L st.1 e ≠ some p` et `OptP (slotOf st.1 e.guarded) (fun q => partOf st.1.P p q → p = q) True` | WC4 C22.5 |
| `EndUseExcl` (`SyncInit.lean`) | prédicat séparé, hors `Encap` | supprimé : son contenu est le cas `endUse` d'`Encap` | WC4 C22, C23 |
| `ProposedTrace`, `ProposedTrace.encap`, `ProposedTrace.of_encap` | relation de traces `Encap` ∧ `EndUseExcl` | supprimés ; une seule relation, `EncapsulatedTrace` | WC4 C22, C23 |

Aucune autre définition ne change.

**`EncapsulatedTrace` et l'ancienne `ProposedTrace`.** Elles admettent les mêmes traces :

- pour `endUse`, l'ancien `Encap` valait `True` et `EndUseExcl` portait la clause ;
- pour les autres étiquettes, `EndUseExcl` valait `True`.

Par rapport à l'ancienne `EncapsulatedTrace`, la nouvelle n'exclut que les `endUse` couverts par C22.5.

**Lecture de « strict structural subplace ».** Le modèle écrit `partOf p q → p = q`. Cette forme équivaut à `¬ (partOf p q ∧ p ≠ q)`, l'égalité sur `Nat` étant décidable. C'est la forme de l'ancien `EndUseExcl`.

**Énoncés changés par répercussion :**

- **`lstep_preserves`** (`SyncInit.lean:923`) : il perd l'hypothèse `hx : EndUseExcl L st lbl`. Le reste est inchangé.
- **`trace_inv`, `trace_preserves`, `encapsulated_inv`** (`Reachable.lean:49`, `:60`, `:91`) : `ProposedTrace` devient `EncapsulatedTrace`.
- **`endUse_syncState`** (`SyncInit.lean:377`, lemme interne) : il perd `hx`, et lit la clause dans `he : Encap …`.
- **`init_inv`** : énoncé inchangé.

Les tests renommés ou ajoutés sont décrits en A.4 et A.5.

## A.3 État de T4

T4 est **prouvé sous `Encap` seule**, `transfer` et le composite par valeur compris.

| Théorème | Énoncé | Hypothèses |
|---|---|---|
| `lstep_preserves` (`SyncInit.lean:923`) | tout pas `LStep` préserve `SyncState` (`SyncInv`, C21.1–C21.7 ; `GrantDiscipline`, C22) | `Encap L st lbl`, `KInvCA st.1`, `WF3 st'.1.flat`, `SyncState` avant |
| `trace_inv` (`Reachable.lean:49`) | `KInvCA` et `SyncState` le long d'une `EncapsulatedTrace` | `DDSound k`, `KInvCA`, `SyncState` au départ |
| `trace_preserves` (`Reachable.lean:60`) | `SyncState` le long d'une `EncapsulatedTrace` | idem |
| `init_inv` (`Reachable.lean:67`) | l'état initial de Spec 1 §47 (registre vide) satisfait `KInvCA` et `SyncState` | `DDSound k`, `StaticsOK` |
| `encapsulated_inv` (`Reachable.lean:91`) | tout état atteint depuis l'état initial par une `EncapsulatedTrace` satisfait `KInvC`, `SyncInv` et `GrantDiscipline` | `DDSound k`, `StaticsOK` |

Preuve du cas `endUse` (`endUse_syncState`), inchangée sur le fond :

- **`slotInit`.** Une feuille de `slot` dans `footprint(p)` implique `p` partie de `slot` ou `slot` partie de `p` (`footprint_comparable`). Le premier cas est exclu par C22.5 (b), sauf `p = slot`. Si `slot` est une partie de `p`, `guarded` est libéré et l'entrée meurt.
- **`ctlInit`.** `ctl ∈ footprint(p)` et `ctl ≠ p` (C22.5 (a)) font de `p` un ancêtre strict de `ctl`, donc une partie contenant `M`, donc `slot` : l'entrée meurt.

## A.4 Exclusions et jumeaux

| Théorème (`EncapTraces.lean`) | Contenu | Clause |
|---|---|---|
| `endUse_ctl_excluded` (`:243`), ex-`endUse_ctl_breaks_ctlInit` | `traceMutex` est une `EncapsulatedTrace` jusqu'à `e2` ; `endUse(lock)` est un pas noyau `ok` ; `¬ Encap`. Sans l'exclusion : `KInvCA` tient, l'entrée est vivante, `lock` est `Uninit`, `¬ SyncInv` (`ctlInit`) | S17a, C22.5 (a), C21.7 |
| `endUse_slotPart_excluded` (`:307`), ex-`endUse_slotPart_breaks_slotInit` | `newMutex(1)` encapsulé, puis `endUse(2)`, partie stricte de `slot = {2, 3}` : `ok` au noyau, `¬ Encap`. Sans l'exclusion : feuille 2 `Uninit`, entrée vivante, `¬ SyncInv` (`slotInit`) | S17b, C22.5 (b), C21.7 |
| `endUse_mutex_kills_entry` (`:265`), jumeau | dans `e2`, `endUse(M)` est `ok` et admis par `Encap` ; l'entrée est vivante avant et morte après ; la trace encapsulée qui le termine donne `KInvCA` et `SyncState` (par `trace_inv`) | C22.5, S17b positif |
| `endUse_slot_kills_entry` (`:332`), jumeau | dans `z0`, `endUse(slot)` du `slot` structuré est `ok` et admis ; l'entrée meurt ; `KInvCA` et `SyncState` tiennent | C22.5, S17b positif |
| `endUse_then_transfer_merges` (`:381`) | la suite `newMutex(2)`, `newMutex(3)`, trois `endUse` sur `slot₂` et `lock₂`, puis `transfer(M₁, M₂)` est un `LRun`. Elle aboutit à `KInvCA`, deux entrées vivantes au même contrôleur (place 9), `¬ SyncInv`. Son premier `endUse` est exclu : `¬ Encap L0 (u0, regU) (endUse 7)` | C21.4, C21.7, C22.5 (b) |
| `endUse_then_transfer_merges_false` (`:417`), nouveau | pour tout `st`, ce `LRun` n'est pas une `EncapsulatedTrace` : les deux `newMutex` ont un résultat déterminé, puis `Encap` refuse `endUse(7)` | C22.5 (b) |
| `transfer_into_live_mutex_rejected` (`SyncInit.lean:962`), conservé | sous `SyncState`, un `transfer` dont la destination contient le mutex d'une entrée vivante est rejeté (§63.3 : son `ctl` est `Init`) ; docstring S18. Jumeaux : `invA` (`EncapTraces.lean:170`), `invB` (`EncapTraces.lean:177`) | S18, C21.7, Spec 1 §63.3 |

Les contre-exemples S16 (`slot_transfer_breaks_control`, `ctl_transfer_breaks_ctlInit`), `newMutex_uninit_rejected` et `transfer_merges_controllers_false` sont inchangés.

## A.5 Traces existantes

Aucun verdict ne change.

- **`traceA`, `traceB`, `traceMutex`** (`EncapTraces.lean:135`, `:145`, `:155`) redeviennent des `EncapsulatedTrace`. Leurs pas sont ceux de la passe précédente, sans `endUse` ; `invA`, `invB` et `inv2` les utilisent sans changement.
- **`mutex_trace`** (`Traces.lean:104`) était déjà une `EncapsulatedTrace` ; il compile sans modification.
- **`s4_*` et `distinct_controllers_ok`** n'étaient pas des traces : ce sont des faits de pas. J'ai ajouté leurs formes de trace, `s4_trace` (`Traces.lean:289`) et `distinct_controllers_trace` (`:252`), construites à partir des pas existants. Les énoncés `s4_steps`, `s4_detached_child` et `distinct_controllers_ok` sont inchangés.
- **Limite.** Ces deux traces ne testent pas C22.5 : `s4_trace` a un registre vide, et `distinct_controllers_trace` ne contient que des `newMutex`, pour lesquels `Encap` vaut `True`.

## A.6 Théorèmes T1, T2, T3, T5, T6

- **Énoncés.** Aucun n'a changé ; tous recompilent.
- **Dépendances.** Un parcours de la clôture des constantes utilisées (script `Dep.lean`, `getUsedConstants` sur types et valeurs) montre que ni `Encap`, ni `EncapsulatedTrace`, ni `endUse_syncState` n'apparaissent dans les dépendances de :
  - T1 : `conservative_op`, `conservative_ok`, `single_kInvC`, `reachable_single`, `syncAuthorized_false`, `conservative_deriveSync` ;
  - T2 : `lstep_kInvCA`, `spawnVal_preservesC`, `opStepC_preservesC` ;
  - T3 : `exitEffC_framesC`, `exitFrameC_anchorOrder`, `terminate_anchorOrder` ;
  - T5 : `realizability` ;
  - T6 : `grants_exclusive` ;
  - `init_inv`.
- **Conséquence.** Le changement de cette passe ne touche que T4 et les tests.

## A.7 Docstrings

- **Remplacement de WC3 / WC3.1 par WC4** dans les 13 modules concernés. Les numéros cités ont été vérifiés contre le texte de WC4 :
  - C13.10 : initialisation de `footprint(M)`, `initM` ;
  - C21.7 : `SlotInit`, `CtlInit` ;
  - C22.3 (a), (b), (c) : `TransferExcl`, les anciens « items 1–3 » ;
  - C22.5 : `Encap` ;
  - C15.3 : `DeriveSyncPre.authorized` ;
  - C18.3 : `ResetLockOk` ;
  - C5.3 : `SpawnValPre.params`, `paramsAtYield`, `yieldEff` ;
  - C23 : couverture du composite dans `LStep`, l'ancien « Formalization coverage » ;
  - S16, S17a, S17b, S18.
- **Contrôle des citations.** Toutes les citations entre guillemets ont été comparées mécaniquement au texte de WC4 et de la Spec 1. Trois passages de `Conservativity.lean` (C3, C24) sont des extraits fidèles mais pas littéraux : majuscule, deux puces jointes, ellipse. Ils n'ont pas été touchés.
- **`NewMutexPre`.** La docstring déclarait non représentés « la seconde phrase de C13.3, la seconde moitié de C13.6, C13.10 ». Dans WC4, ces passages ne sont plus des préconditions : ce sont les obligations d'interface et de réalisation de C13 (C13.3, C13.6, « former C13.10 »). La docstring les cite ainsi. `sharedMutable` cite C13.6 entier.
- **Erreur de citation antérieure corrigée (C21.4).** Les docstrings attribuaient l'unicité des identités `guarded` à la « seconde phrase » de C21.4. Or C21.4 se compose de :
  - une première phrase en deux propositions : « Distinct live entries have distinct `ControlOf` leaves; the guarded-identity uniqueness guard is also respected. » ;
  - une seconde phrase, sur le contrôleur enregistré deux fois.

  Les champs `ctlUnique` et `unique` citent maintenant la première et la seconde proposition (« first clause », « second clause »). Le contenu des champs est inchangé.
- **Historique retiré.** Les docstrings ne décrivent plus les versions antérieures, par exemple « the WC3 counterexample ».

## A.8 Problèmes de WC4

Aucun silence ni aucune ambiguïté n'a arrêté la formalisation. Trois remarques :

**X1. C22, dernier alinéa.**

> The requirement in item 5 is the proposed `EndUseExcl` condition verified separately in the exploratory formalization

Ce passage décrit l'état de la passe WC3.1. Après cette passe, la condition est une clause d'`Encap` et n'est plus vérifiée séparément. La remarque est rédactionnelle : C22.5 et C23 sont cohérents avec le modèle.

**X2. S17a, jumeau positif.**

> Positive: legal end of use after the mutex entry has ceased to be live

WC4 donne ce positif ; le brief demande `endUse(M)` et `endUse(slot)`, qui sont les positifs de S17b. Le positif de S17a, littéralement `endUse(ctl)` après la mort de l'entrée, n'est pas formalisé. Il suffirait de prolonger `endUse_slot_kills_entry` par `endUse(lock = 4)`, admis par `Encap` puisque aucune entrée n'est plus vivante. Non fait : hors brief.

**X3. C13, « former C13.10 ».** Ce renvoi désigne un numéro qui n'existe plus dans WC4, puisque C13.10 y est l'initialisation. Les docstrings reprennent la formule telle quelle.

**Points de WC3.1 résolus par WC4.**

- **W2 (C18.3).** WC4 C18.3 renvoie à C21.3 pour la validité du contrôleur, et à C21.7 « separately » pour l'initialisation : c'est la lecture du modèle.
- **W3 (composite par valeur).** WC4 C22.3 fixe l'état d'évaluation : « against the state at the start of its own transfer phase », ce qu'est `EncapVals`.
- **W1.** C22.5 est la clause proposée.

**Nécessité des clauses d'`Encap`, à titre d'information.** Le modèle a un témoin de nécessité pour C22.1 (`acquire_blocked_by_derive`), C22.3 (a) et (c) (S16), et C22.5 (a) et (b) (S17). Il n'en a pas pour :

- **C22.2.** Sous l'instanciation de bibliothèque, tout `deriveSync` brut `ok` cible le `guarded` d'une entrée vivante, et `Encap` l'exclut (`deriveSync_excluded`) ; aucun état ne montre ce qu'il casserait.
- **C22.3 (b), transfert d'une partie stricte de `slot`.** Ce n'est pas un défaut de WC4 : aucun témoin n'a été demandé.

## A.9 Écarts avec la Spec 1

Aucune clause de la Spec 1 n'est modifiée. C22.5 restreint l'interface sûre, pas O12 :

- `endUse_ctl_excluded` et `endUse_slotPart_excluded` établissent que le pas noyau est `ok` (`opStepC … (.ok …)`) ;
- `Encap` reste un prédicat sur les traces, jamais une précondition d'opération.

---

# Partie B — index consolidé du jalon 1

État de la branche à `1b85c96`. Les numéros de ligne sont ceux de ce commit.

## B.1 Modules de `formal/Ern/Concurrency/`

| Module | Définitions principales | Clause |
|---|---|---|
| `Context.lean` | `Life`, `Ctx`, `SC` (`:46`) | WC4 C1, C2 (`S_C = (C, F_C, P, I, A, D)`), C3 |
| | `SC.view` (`:84`), `SC.set`, `SC.flat`, `SC.Single`, `SC.toS3`, `SC.ofS3` | C2 (P1 : vue du contexte exécutant), C24 |
| | `SC.parC`, `SC.ancestorC` (`:128`) | C3 (H1) |
| | `AnchorOrderC` (`:149`), `AnchorOrderHeldC` (`:163`) | Spec 1 §44 sur `ancestorC` |
| | `FramesC` (`:190`) | C3 |
| | `ConcurrentWF` (`:209`) | C20 |
| | `KInvC` (`:224`) | Spec 1 §57 ré-indexé, C20 |
| `Frames.lean` | `ViewStep` (`:36`) ; `opStepC` (`:270`) : O1–O16 exécutées par un contexte, sur sa vue | C2 |
| | `transferEffC`, `storeEffC`, `enterEffC`, `dependEffC` et leurs préconditions | Spec 1 §61–§72 ré-indexés |
| | `exitEffC` (`:225`), `reparent` (`:218`), `ExitPreC` (`:233`) | C6 |
| | `spawnEff`, `SpawnPre` (`:318`), `SpawnStep` (`:344`) | C4 |
| | `termEffC`, `TermPre` (`:361`), `TermStep` | C7 |
| | `JoinStep` (`:407`) : `ok`, `reject` sur identifiant inconnu, aucune issue sur un contexte vivant | C8 |
| | `alloc_ok_satisfiable`, `alloc_fail_unsatisfiable` (`:282`, `:293`) | C2 (P1) |
| `Conservativity.lean` | théorèmes T1 | C24, C3 |
| `Sync.lean` | `KC (R : Type)` (`:23`) | C2, C14 (P2) |
| | `deriveSyncEff`, `DeriveSyncPre` (`:36`, 9 champs), `DeriveSyncStep` (`:78`), `CStepS` | C15.1–C15.6 |
| `SyncLib.lean` | `SyncEntry` (`:29`), `SyncReg`, `MutexLayout` (`:40`), `SyncEntry.Live` (`:46`), `ControlOf` (`:55`) | C12 |
| | `CtrlRight` (`:72`), `EntryAuth`, `LibSyncAuthorized` (`:92`), `libKC` (`:102`), `SyncSound` (`:113`) | C14 |
| | `slotOf` (`:143`), `mutexOf` (`:223`) | C12, C13 |
| | `CoveringDesc`, `NoCoveringDesc`, `GrantDiscipline` (`:167`) | C22 |
| | `CtlUnique` (`:172`), `SlotInit` (`:178`), `CtlInit` (`:184`), `SyncInv` (`:188`, 9 champs) | C21.1–C21.7 |
| | `NewMutexPre` (`:232`, 11 champs), `NewMutexOk` | C13.1–C13.10 |
| | `AcquireOk` (`:290`) | C16 |
| | `UnlockOk` (`:300`) | C17 |
| | `ResetLockOk` (`:311`) | C18 |
| | `Label` (`:321`), `LStep` (`:337`), `LRun` (`:396`) | C23 |
| | `TransferExcl` (`:363`), `EncapVals` (`:375`), `Encap` (`:385`), `EncapsulatedTrace` (`:404`) | C22.1–C22.3, C22.5, C23 |
| | théorèmes T1 (partie `SyncAuthorized`), T5, T6 | |
| `Transfer.lean` | `spawnCreate` (`:25`), `transfersEff` (`:29`), `yieldEff` (`:35`), `spawnValEff` (`:40`) | C5.1–C5.3 |
| | `FreshRootLocal` | C5, précondition 2 |
| | `ValTransferPre` (`:61`), `ValTransfersPre` | C5.2, préconditions 1, 3, 4 |
| | `SpawnValPre` (`:130`), `SpawnValStep` (`:185`) | C4, C5 |
| `TransferPreserve.lean` | `yieldF`, `KBase` (`:145`), `FrameOwned` ; `spawnVal_preservesC` (T2) | C5, C20 |
| `Preservation.lean` | `KInvCA` (`:24`) ; T2 pour O1–O16, `spawn`, `join`, `deriveSync` ; copies des lemmes de la Spec 1 (§ B.5) ; contre-exemples de `deriveSync` | C20, C23, C15.1 |
| `Reparent.lean` | `repO`, `Pop` ; T3 ; T2 pour `exitFrameC` et `terminate` | C6, C7, OB-C13 |
| `SyncPreserve.lean` | `SyncState` (`:25`), `EntryOK`, `Uniq`, `SyncCore` (`:57`, décomposition interne), `StepFacts` | lemmes par opération pour C21.1–C21.6, C22 |
| | `newMutex_nonleaf_rejected` | C12, C13.3 |
| `SyncInit.lean` | lemmes d'arbre ; `InitFacts` ; lemmes `endUse`, `transfer`, bibliothèque, composite | C21.4, C21.7, C22.3, C22.5 |
| | `lstep_preserves` (T4), `transfer_into_live_mutex_rejected` | S18 |
| `Reachable.lean` | `lstep_kInvCA` (T2) ; `trace_inv`, `trace_preserves`, `init_inv`, `encapsulated_inv` (T4) | C20–C23 |
| `Traces.lean`, `EncapTraces.lean` | modules de test : états, pas, traces, contre-exemples | § B.3 |

## B.2 Théorèmes T1–T6

| T | Nom Lean (module:ligne) | Énoncé | Hypothèses |
|---|---|---|---|
| T1 | `conservative_op` (`Conservativity.lean:457`) | pour chaque O1–O16, les issues de `opStepC k op 0 s` sont exactement celles de Spec 1 sur `s.toS3` | `s.Single`, `FramesC s` |
| T1 | `conservative_ok` (`:489`) | une issue `ok` reste à un contexte et projette l'effet de Spec 1 | idem |
| T1 | `single_ancestorC` (`:141`) | `ancestorC` = `ancestor` de §39 sur la pile | `s.Single`, pile strictement décroissante |
| T1 | `single_anchorOrderC` (`:209`), `single_anchorOrderHeldC` (`:218`) | coïncidence avec `AnchorOrder`, `AnchorOrderHeld` | idem |
| T1 | `single_kInvC` (`:229`) | `KInvC s ↔ FramesC s ∧ KInv s.toS3` | `s.Single` |
| T1 | `reachable_decreasing` (`:534`), `reachable_single` (`:569`) | tout état atteignable de Spec 1 est la projection d'un état à un contexte avec `FramesC` et `KInvC` | `DDSound`, `StaticsOK` |
| T1 | `syncAuthorized_false` (`SyncLib.lean:423`), `conservative_deriveSync` (`:431`) | sans entrée vivante, `SyncAuthorized` est faux et `deriveSync` n'a pas d'issue `ok` | `SyncSound kc reg s` |
| T1 | `libKC_sound` (`SyncLib.lean:117`) | l'instanciation de bibliothèque satisfait `SyncSound` | — |
| T2 | `opStepC_preservesC` (`Preservation.lean:1815`) | les O1–O16 autres qu'O7 exécutées par un contexte préservent `KInvCA` | `DDSound`, `KInvCA`, `op ≠ exit` |
| T2 | `exitFrameC_preserves` (`Reparent.lean:779`), `terminate_preserves` (`:792`) | `KInvC`, `RootHeldConv`, `HeldAnchored` préservés | ces trois invariants |
| T2 | `spawn_preservesC` (`Preservation.lean:1844`), `join_preservesC` (`:1851`) | `KInvCA` préservé | `KInvCA` |
| T2 | `deriveSync_preservesC` (`:1857`) | `KInvCA` préservé, pour tout `KC R` et registre | `KInvCA` |
| T2 | `spawnVal_preservesC` (`TransferPreserve.lean:299`) | le composite par valeur préserve `KInvCA` | `KInvCA` |
| T2 | `lstep_kInvCA` (`Reachable.lean:25`) | tout `LStep` préserve `KInvCA` | `DDSound`, `KInvCA` |
| T3 | `exitEffC_ancestorC` (`Reparent.lean:690`), `termEffC_ancestorC` (`:700`) | frames vivantes après le pas, et `ancestorC` inchangé sur elles | `FramesC`, appelant / pile d'une frame |
| T3 | `exitEffC_framesC` (`:654`), `termEffC_framesC` (`:671`) | `FramesC` préservé | idem |
| T3 | `exitEffC_reparent` (`:711`), `termEffC_reparent` (`:720`) | cible = parent immédiat ; seuls les contextes de parent `f` sont reparentés | idem |
| T3 | `exitEffC_kernel` (`:731`), `termEffC_kernel` (`:739`) | `A`, `D` de Spec 1 §73 ; `P`, `I`, `dead`, `pins`, `nF` inchangés | — |
| T3 | `exitFrameC_anchorOrder` (`:757`), `terminate_anchorOrder` (`:767`) | `AnchorOrderC` préservé, `AnchorOrderHeldC` établi | `FramesC`, `WF3`, `AnchorOrderC` |
| T4 | `lstep_preserves` (`SyncInit.lean:923`) | tout `LStep` préserve `SyncState` (`SyncInv` C21.1–C21.7, `GrantDiscipline`) | **`Encap`**, `KInvCA` avant, `WF3` après, `SyncState` |
| T4 | `trace_inv` (`Reachable.lean:49`), `trace_preserves` (`:60`) | `KInvCA` et `SyncState` le long d'une trace | **`EncapsulatedTrace`**, `DDSound`, invariants au départ |
| T4 | `init_inv` (`:67`) | état initial : `KInvCA` et `SyncState` | `DDSound`, `StaticsOK` |
| T4 | `encapsulated_inv` (`:91`) | depuis l'état initial : `KInvC`, `SyncInv`, `GrantDiscipline` | **`EncapsulatedTrace`**, `DDSound`, `StaticsOK` |
| T5 | `realizability` (`SyncLib.lean:473`) | l'instanciation de `SyncAuthorized` pour la frame courante entraîne `NoCoveringDesc` et `DeriveSyncPre` entier | `KInvC`, `SyncInv`, `GrantDiscipline`, contexte vivant |
| T6 | `grants_exclusive` (`SyncLib.lean:451`) | deux autorités actives distinctes d'origine `g` et de footprint `footprint(g)` non vide, dont une `Modify`, ne coexistent pas | `WF3`, `I1` |

## B.3 Contre-exemples, exclusions et jumeaux

| Énoncé (module:ligne) | Verdict | Jumeau positif | Clause |
|---|---|---|---|
| `acquire_blocked_by_derive` (`Traces.lean:75`) | `derive(guarded, Observe)` non encapsulé : entrée vivante, `grant = none`, `GrantDiscipline` faux, `acquire` non habilité | `acquire_enabled` (`:92`), `unlock_enabled` (`:99`), `mutex_trace` (`:104`) | C22.1, C16 |
| `realizability_needs_i1` (`Traces.lean:119`) | `SyncInv`, `GrantDiscipline` et l'instanciation tiennent, I1 est violé, `DeriveSyncPre` échoue | `realizability` | C25, Spec 1 §50 |
| `join_waits` (`Traces.lean:164`) | `join` sur un contexte vivant : aucune issue | `frames_run` (`:156`) : `join` `ok` après `terminate` | C8 |
| `join_unknown_rejected` (`Traces.lean:172`) | identifiant inconnu : `reject`, pas d'`ok` | `frames_run` | C8 |
| `shared_controller_rejected` (`Traces.lean:225`) | second `newMutex` sur le même contrôleur rejeté | `distinct_controllers_ok` (`:245`), `distinct_controllers_trace` (`:252`) | C13.8 (S9, partiel : constructions, pas d'acquisition) |
| `s4_steps`, `s4_trace`, `s4_detached_child` (`Traces.lean:280`, `:289`, `:302`) | positif : l'enfant reçoit une valeur par le composite et survit à son créateur | — (le négatif de S4 n'est pas formalisé) | S4, C5, C6 |
| `deriveSync_observe_rejected` (`Preservation.lean:1883`) | `deriveSync` depuis une autorité `Observe` : `reject` | `deriveSync_modify_ok` (`:1890`) | C15.1 |
| `deriveSync_breaks_i2_false` (`Preservation.lean:1896`) | négation, pour tout `KC R`, de l'ancien contre-exemple I2 | — | C15.1 |
| `spawnVal_covering_rejected` (`Transfer.lean:205`) | un paramètre couvre une feuille d'une source par valeur : `reject` | `spawnVal_apart_ok` (`:214`) | C5, précondition 5 |
| `newMutex_nonleaf_rejected` (`SyncPreserve.lean:1351`) | contrôleur positionnel non feuille : `newMutex` rejeté | `newMutex_ok` (`Traces.lean:58`) | C12, C13.3 |
| `newMutex_uninit_rejected` (`EncapTraces.lean:450`) | `newMutex` sur un mutex aux champs `Uninit` : rejeté | sa première moitié (`newMutex(1)` accepté) | C13.10 |
| `transfer_merges_controllers_false` (`EncapTraces.lean:456`) | `newMutex(1)`, `newMutex(3)`, `transfer(M, M′)` depuis `m0` n'est pas un `LRun` | — | C13.10 |
| `slot_transfer_breaks_control` (`EncapTraces.lean:202`) | `transfer(slot, Y)` `ok` au noyau, `¬ Encap` ; sans l'exclusion, `ControlOf` indéfini, `¬ SyncInv` | `controlAB` (`:184`), `invA`, `invB` | S16, C22.3 (a) |
| `ctl_transfer_breaks_ctlInit` (`EncapTraces.lean:222`) | `transfer(lock, Y)` `ok`, `¬ Encap` ; sans l'exclusion, `lock` `Moved`, `¬ SyncInv` | `controlAB` | S16 étendu, C22.3 (c) |
| `transfer_into_live_mutex_rejected` (`SyncInit.lean:962`) | sous `SyncState`, transfert vers le mutex d'une entrée vivante : rejeté (§63.3) | `invA` (`EncapTraces.lean:170`), `invB` (`:177`) | S18, C21.7 |
| `endUse_ctl_excluded` (`EncapTraces.lean:243`) | `endUse(ctl)` `ok`, `¬ Encap` ; sans l'exclusion, `¬ SyncInv` (`ctlInit`) | `endUse_mutex_kills_entry` (`:265`) | S17a, C22.5 (a) |
| `endUse_slotPart_excluded` (`EncapTraces.lean:307`) | `endUse` d'une partie stricte de `slot` `ok`, `¬ Encap` ; sans l'exclusion, `¬ SyncInv` (`slotInit`) | `endUse_slot_kills_entry` (`:332`) | S17b, C22.5 (b) |
| `endUse_then_transfer_merges` (`EncapTraces.lean:381`), `endUse_then_transfer_merges_false` (`:417`) | `LRun` fusionnant deux contrôleurs, qui n'est pas une `EncapsulatedTrace` | `invA`, `invB` | C21.4, C22.5 (b) |
| `alloc_ok_satisfiable`, `alloc_fail_unsatisfiable` (`Frames.lean:282`, `:293`) | `K.Satisfiable` évalué sur la vue du contexte exécutant | — | C2 (P1) |

Couverture du corpus de WC4 §V au jalon 1 :

- **Couverts, au moins pour une moitié :** S2 (positif ; le négatif « competing full-footprint grant » relève de `grants_exclusive`), S4 (positif), S7 (`traceA`, `traceB`), S9 (partiel), S16, S17a, S17b, S18.
- **Non formalisés :** les autres cas. La validation adversariale est l'objet du jalon 3 (WC4 §VI).

## B.4 Décisions de représentation (cumulées)

Aucune ne change de programme accepté ni de comportement. Origine : la passe 1 (WC2) a produit `reports/spec2-m1.md` ; les passes WC3, WC3.1 et la clôture suivent.

1. **Contextes** (passe 1).
   - Liste indexée par l'identité.
   - Chaque `Ctx` porte sa pile (sommet en tête), son état de cycle de vie et le parent de sa frame initiale.
   - La pile d'un contexte non vivant est vide.
2. **Ancêtres** (passe 1). `parC` est dérivé des piles et des parents de contextes ; `ancestorC` suit `chain parC`. Le bien-fondé est représenté par l'ordre des identités (`FramesC.parent`), comme en Spec 1 §49, dernier alinéa.
3. **Vues** (passe 1).
   - `SC.view s c` : pile de `c` d'abord, puis les autres frames vivantes.
   - Les clauses de Spec 1 ne lisent la pile que par le sommet et l'appartenance, d'où les lemmes `*_mem_congr`.
   - `SC.viewAt` place la frame demandeuse au sommet pour `SyncAuthorized`.
4. **Opérations de bibliothèque à issue `ok` seule** (passe 1). Le blocage est une absence d'issue ; `Outcome3` n'est pas étendu.
5. **Traces** (passe 1). Ce sont des preuves des relations, avec préconditions décidées par `decide`, sans exécuteur.
6. **`KInvCA`** (passe 1). `KInvC` est renforcé par `KAux` et `HeldAnchored`, les auxiliaires de `reachable_inv` de la Spec 1. Les énoncés depuis l'état initial ne les supposent pas.
7. **`ControlOf` positionnel** (passe 1, P3). Un paramètre `MutexLayout` unique donne la position du champ `guarded` et celle du contrôleur parmi les enfants ordonnés du mutex. Le contrôleur doit être une feuille.
8. **`KC (R : Type)`** (WC3, P2).
   - Le registre est le premier argument de `SyncAuthorized`.
   - `libKC k L : KC SyncReg` ; `LStep` passe le registre courant.
   - `SyncSound` est une obligation par état.
9. **C15.1** (WC3). « own mode permits `Modify` » est encodé `Mode.modify.le y.mode`.
10. **`CtlUnique` et `unique`** (WC3). Les entrées sont comparées par indice dans le registre.
11. **`mutexOf`** (WC3). `M` est le parent structurel de la place qui tient `guarded` ; `footprint(M)` est évalué sur lui (C13.4, C13.10).
12. **`JoinStep`** (WC3). « Unknown to the execution » se lit `s.C[d]? = none` : aucun contexte n'est retiré de `C`.
13. **Composite par phases** (WC3).
    - Arguments par valeur : liste ordonnée `vs`.
    - Phases : fonctions d'effet `spawnCreate`, `transfersEff`, `yieldEff`.
    - Clauses de phase : récursives (`ValTransfersPre`), évaluées sur l'état produit par les transferts précédents.
    - §63.8 sur l'état final ; §63.7 couverte par O6.4 (`AnchorOrderHeldC` final).
    - Non-duplication : par construction.
14. **`slotOf` et `SlotInit`** (WC3.1). Les « structural leaves of … `slot` » sont les feuilles de `footprint(slotOf)`.
15. **`TransferExcl`** (WC3.1). C22.3 (a) et (b) sont réunis en `partOf P src slot`.
16. **`lstep_preserves` sous `KInvCA`** (WC3.1). Le composite a besoin de `WF3` à chaque phase.
17. **C22.5 dans `Encap`** (clôture). Clause en ligne dans le cas `endUse`, de forme `partOf p q → p = q`.
18. **`SyncCore`** (WC3, puis WC3.1). Décomposition interne de `SyncPreserve.lean`, jamais en conclusion d'un théorème T4.

Propositions de la passe 1 et leur sort :

- **P1** (`Satisfiable` sur la vue) : adoptée par WC4 C2, en décision candidate.
- **P2** (registre en argument) : adoptée par WC4 C2 et C14, en décision candidate.
- **P3** : adoptée par WC4 C12 (« per-instance positional relationship »).
- **P4** (garde unifiée) : renvoyée à OB-C16.
- **P5** (style du jalon 4 de `DESIGN.md`) : non prise.

## B.5 Lemmes de la Spec 1 copiés ou adaptés

Tous sont dans `Preservation.lean`, sauf `corr_leaf'` (`SyncInit.lean`). Les chemins sont relatifs à `Ern/MemoryModel/`.

| Lemme du jalon (ligne) | Origine | Nature |
|---|---|---|
| `effAnchorOKC_of_same` (`:81`) | `Access/Preserve/Frames.lean` `effAnchorOK_of_same` | adapté à `ancestorC` |
| `releases_base` (`:304`) | `Access/Preserve/EndFree.lean` `releases_preserve` | preuve sans les parties `AnchorOrder`, `AnchorOrderHeld` |
| `endUse_base` (`:384`), `free_base` (`:407`) | `Access/Preserve/EndFree.lean` `endUse_preserves`, `free_preserves` | sans les ordres d'ancrage |
| `alloc_effAnchorOKC_old` (`:470`), `alloc_effAnchorOKC_new` (`:498`), `alloc_anchorOrderC` (`:523`), `alloc_anchorOrderHeldC` (`:541`) | `Access/Preserve/Alloc.lean` `effAnchorOK_old`, `effAnchorOK_new`, `anchorOrder`, `anchorOrderHeld` | adaptés à `ancestorC` |
| `skel_of_A` (`:661`), `wf3_skel` (`:667`), `inv3base_skel` (`:689`), `noDangling_skel` (`:698`), `rootHeldConv_of` (`:710`) | `Access/Preserve/Small.lean`, lemmes privés de même nom | copies |
| `effAnchorOKC_skel` (`:718`) | `Access/Preserve/Small.lean` `effAnchorOK_skel` (privé) | adapté à `ancestorC` |
| `storeEff_eq` (`:813`), `store_get` (`:822`), `store_skel` (`:828`), `store_root` (`:836`), `store_D` (`:845`) | `Access/Preserve/Small.lean`, lemmes privés de même nom | copies |
| `enter_rootHeld'` (`:967`), `enter_wf'` (`:998`), `enter_noDangling'` (`:1049`), `enter_rootHeldConv'` (`:1071`) | `Access/Preserve/Frames.lean` `enter_*` | preuves reprises sans la précondition d'ancêtre linéaire (seul §72 sert) |
| `getElem?_append_cases` (`:1095`) | `Access/Main.lean` (privé) | copie |
| `push_preserves` (`:1170`) | `Access/Preserve/Frames.lean` `enter_anchorOrder` | adapté à `ancestorC` |
| `optP_false_iff'` (`:1557`), `mem_movedTo'` (`:1565`), `mem_movedDeps_part'` (`:1575`), `not_partOf_src'` (`:1582`), `transfer_rootHeld'` (`:1589`), `transfer_rootHeldConv'` (`:1610`) | `Access/Preserve/Transfer.lean`, lemmes privés de même nom | copies |
| `transfer_wf3'` (`:1625`) | `Access/Preserve/Transfer.lean` `transfer_wf3` (privé) | preuve reprise, §63.1 et §63.9 seulement |
| `transfer_base'` (`:1686`) | `Access/Preserve/Transfer.lean` `transfer_inv3` (privé) | sans `AnchorOrder` |
| `transfer_heldAnchored'` (`:1712`) | `Access/Preserve/Transfer.lean` `transfer_preserves_heldAnchored` | preuve reprise |
| `transfer_preserves` (`:1748`) | `Access/Preserve/Transfer.lean` `transfer_anchorOrderHeld` (privé) | adapté à `ancestorC` |
| `corr_leaf'` (`SyncInit.lean:168`) | `Refinement.lean` `corr_leaf` | copie de la preuve |

Lemmes de la Spec 1 importés tels quels :

- `init_kinv` (état initial) ;
- `Arena.kstep_fp`, `Arena.footprint_shapeP`, `Arena.KInvB.sound` ;
- les lemmes de `Access` appliqués à `s.view c`.

Lemmes nouveaux sur les structures de la Spec 1, à remonter dans la Spec 1 à la reconstruction. Ils ne dépendent de rien de concurrent :

- **`SyncInit.lean`, sur l'arbre des places et `corr` :**
  - `partOf_trans`, `partOf_total`, `footprint_comparable` ;
  - `partOf_parent`, `partOf_leaf`, `leaf_mem_footprint`, `partOf_of_mem_footprint` ;
  - `getElem?_posIn`, `corr_parent`, `corr_inj`.
- **`Context.lean`, congruence par appartenance de pile :** `usable_mem_congr`, `holderLive_mem_congr`, `wf3_mem_congr`, `i3_mem_congr`, `noDangling_mem_congr`.
- **`Preservation.lean` :** `heldAnchored_mem_congr`.

## B.6 Obligations ouvertes OB-C01 à OB-C16

| OB | Ce que le jalon 1 en dit |
|---|---|
| OB-C01 événements, exécutions permises | Rien. La sémantique est relationnelle, pas à pas, sans modèle d'événements. |
| OB-C02 conflits, synchronizes-with, happens-before | Rien. |
| OB-C03 atomiques, ordres mémoire | Rien. |
| OB-C04 `LockOrder` | Rien (S6 non formalisé). |
| OB-C05 réalisation atomique d'`acquire`, `unlock`, `resetLock` | Seul l'abstrait est formalisé. `AcquireOk`, `UnlockOk` et `ResetLockOk` n'ont qu'une issue `ok`. L'état du contrôleur n'est pas représenté dans `S_C`, qui n'a pas de valeurs (Spec 1 §41) : seuls le fait d'autorité (`CtrlRight`) et `grant` le sont. Les obligations de réalisation de C17 et C18 sont nommées dans les docstrings, non prouvées. |
| OB-C06 absence de courses | Rien. |
| OB-C07 typage de la transférabilité et de la partageabilité | Rien. `Encap` est un prédicat sur les traces, pas une règle de typage. |
| OB-C08 encapsulation, contrat de bibliothèque | C22.1–C22.3 et C22.5 sont formalisés par `Encap` et `EncapsulatedTrace`. T4 est prouvé sous eux. Témoins de nécessité : § A.8 ; C22.2 et C22.3 (b) n'en ont pas. C22.4 n'est pas représentée (obligation de réalisation). L'application par les Specs 4 et 10 est ouverte. |
| OB-C09 conventions par valeur, annulation, terminaison anormale | Le composite provisoire est formalisé (`SpawnValPre`, phases, T2, T4). Annulation, terminaison anormale et nettoyage ne sont pas modélisés ; `terminate` exige que les frames imbriquées soient sorties. |
| OB-C10 contextes externes | Rien. Les seuls contextes sont le contexte initial et ceux créés par `spawn` ou par le composite. |
| OB-C11 ordre des événements de `join` et de la complétion | `join` : `ok` à état inchangé, `reject` sur identifiant inconnu, aucune issue sur un contexte vivant (`join_waits`, `join_unknown_rejected`). L'ordre des événements est ouvert. |
| OB-C12 correspondance concrète (Spec 1 §82) | Rien au jalon 1 : c'est le jalon 2. |
| OB-C13 H1 sous reparentage | **T3 prouvé** (`Reparent.lean`), sous `FramesC`, `WF3` et `AnchorOrderC`. |
| OB-C14 composite par valeur | Prouvés : `spawnVal_preservesC` (T2) et le cas `spawnVal` de `lstep_preserves` (T4). S4 en positif ; rejet de C5, précondition 5 (`spawnVal_covering_rejected`). La forme finale de la convention relève d'OB-C09. |
| OB-C15 contrat de `SyncAuthorized` | `KC R` avec registre en argument (P2) ; obligation par état `SyncSound`, satisfaite par `libKC` (`libKC_sound`). `LibSyncAuthorized` ne contient que les faits de C14.1–C14.3. `realizability` (T5) les relie à `DeriveSyncPre` sous `KInvC`, `SyncInv` et `GrantDiscipline` ; `realizability_needs_i1` montre que I1 est nécessaire. |
| OB-C16 garde unifiée des identités administratives | `NewMutexPre.otherAdmin` consulte une liste fixe `adm`, que rien ne relie au registre des arènes de `Ern.MemoryModel.Arena` (proposition P4 de la passe 1). Les arènes (O17–O19, opérations dérivées de Spec 1 §76–§78) ne sont pas des étiquettes de `LStep`. Non intégré. |

## B.7 Audit final des axiomes

- **Méthode.** Script `collectAxioms` sur toutes les constantes `thmInfo` dont le nom commence par `Ern.Concurrency` ou `_private.Ern.Concurrency`, après `import Ern`.
- **Résultat.** 798 théorèmes, dont 626 non internes : aucun axiome hors `{propext, Quot.sound}`.
- **`#print axioms`** sur `lstep_preserves`, `trace_inv`, `init_inv`, `encapsulated_inv`, `endUse_ctl_excluded` et `endUse_then_transfer_merges_false` : `[propext, Quot.sound]`.
- **Absences vérifiées.** Le `grep` d'`AGENTS.md` (`sorry`, `admit`, `native_decide`, `axiom`) est vide sur le dépôt. Aucun `noncomputable` dans `formal/Ern/Concurrency/`.
