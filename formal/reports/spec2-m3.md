# Spec 2, jalon 3 — complétude et validation adversariale

Branche `formal/spec2-m3`, créée depuis `e30355f` (tête de `formal/spec2-m2`). Exploratoire, jamais mergée ; rien n'est poussé.

Sources :

- WC4 corrigée, non commitée. Le brief la nomme `ERN_Concurrency_Model_WC4.md`. Ce fichier n'est pas sur le disque. Le texte lu est `~/Downloads/ERN_WC4.md`, la WC4 corrigée du jalon 2 : C13 n'y cite plus « former C13.10 ».
- `corpus-spec2-m3.md`, non commité : source des verdicts attendus.
- Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md`.

**Fragment.** Les énoncés de réalisation (R1–R5 et leurs extensions A4) portent sur le fragment du jalon 2 : les contextes s'entrelacent **au grain des pas abstraits**. Les énoncés de l'étape B portent sur la machine d'autorités seule. Aucun n'est une preuve d'absence de data races.

## Commits

| Commit | Contenu |
|---|---|
| `3b9b7ff` | A1, A2, A3 : étiquettes d'arène dans `LStep`, état `(SyncReg, ArenaReg)`, garde §56 unifiée, `AdminSep`, `ArenaInvC`, T7, extension de T2, T4, R1. **Commit groupé** : le changement de type de l'état de bibliothèque casse tous les modules qui utilisent `LStep`. |
| `84d3ece` | A5 : conservativité des opérations d'arène (T1, R5). |
| `1fb106f` | A4 : §82.3 et §82.6 sous `ReprC`. |
| `9cf417c` | A6 : docstring de `NewMutexPre`. |
| `460ce07` | Corpus, bloc MX. |
| `6e4f3f1` | Corpus, bloc AR (S3). |
| `e039840` | Corpus, frames (S1a, S1b, S4 négatif, S13, S14). |
| `917b77e` | Corpus : S10, W-C22.3 (b), jumeau de S17a, `CrossContextConflictOnlyShared`. |
| `602fea5` | `AdminSep` supposée pour `issue` et `reset` seulement dans `lstep_preserves` ; `libInv_nil` ; `adminSep_needed`. |
| `bf139f2` | coupure d'une ligne de docstring. |
| `8e2bccf` | corrections de la revue (§ « Revue adversariale ») : `W_C22_2_reenable`, `S10_1_ok` avec `Encap` et `s10_trace`, `W_C22_3b_ok`, docstrings. |

Le rapport fait l'objet d'un commit séparé.

## Vérifications à `8e2bccf`

- `lake build` réussit (66 jobs). Aucun avertissement : chaque module de `Ern/Concurrency/` et de `Ern/Concurrency/Corpus/` a été recompilé seul par `lake env lean`, sans sortie.
- Le `grep` d'`AGENTS.md` est vide ; aucun `noncomputable` dans `Ern/Concurrency`.
- Audit `collectAxioms` : 1092 théorèmes `Ern.Concurrency*`, dont 835 non internes. Aucun axiome hors `{propext, Quot.sound}`.
- Aucune ligne ajoutée de plus de 100 caractères (lignes `+` de `git diff -U0 e30355f`). Quatre lignes plus longues, antérieures au jalon, restent dans des fichiers modifiés : `SyncLib.lean:44`, `SyncPreserve.lean:1239`, `Traces.lean:15` et `:156`.

## Passages lus

- **Spec 1 :** §§36, 43, 45–46, 50, 54–58, 59–78 et 82, en entier.
- **WC4 corrigée :** en entier.
- **Corpus :** en entier.
- **Lean :** `Arena.lean` (O17–O19, `ArenaInv`, transport et préservation de `LInv`) ; `RefinementArena.lean` (`kexp`, `lopsOf`) ; dans `Refinement.lean`, `pointer_sound_store` et `pinned_address_stable` ; les modules des jalons 1 et 2 touchés.

---

# Partie A — le jalon 3

## A.1 Audit des axiomes d'`Arena.lean` et de `RefinementArena.lean`

Fait en premier, comme le demande le brief (script `AuditArena.lean`, `collectAxioms` sur les théorèmes de chaque module).

| Module | Théorèmes (non internes) | Hors `{propext, Quot.sound}` |
|---|---|---|
| `Ern.MemoryModel.Arena` | 218 (176) | 0 |
| `Ern.MemoryModel.RefinementArena` | 99 (74) | 0 |

Aucune dépendance à `Classical.choice` : rien n'arrête le jalon.

## A.2 Étape A

### A1 — arènes dans `LStep`

| Définition | Module:ligne | Contenu | Source |
|---|---|---|---|
| `ArenaReg` | `SyncLib.lean:229` | `List Arena.ArenaEntry`, état de bibliothèque séparé de `S_C` et du registre de synchronisation | Spec 1 §46 ; WC4 C2 |
| `NewArenaPreC s reg ar c storage internal` | `SyncLib.lean:344` | les clauses de `Arena.NewArenaBase` sur la vue de `c` ; §76.6 lu sur l'état noyau concurrent : `WF3` et `I1` de `s.flat`, `AnchorOrderC`, `AnchorOrderHeldC` ; la garde §76.4 (A3) | Spec 1 §76 ; WC4 C2, C3, C20 |
| `NewArenaStepC` | `SyncLib.lean:395` | `ok` (l'entrée d'`Arena.newArenaEff` est enregistrée) ou `reject` | Spec 1 §76, §58 |
| `IssueStepC k s ar c i region dst` | `SyncLib.lean:406` | forme d'`Arena.IssueD` : contrôles statiques (§77.1, §77.2) et `fail` de disponibilité (§77.4) sur la vue de `c`, puis `split` de `internal` et `store` du bloc, **tous deux exécutés par `c`** (`opStepC`) ; mise à jour `Arena.issueMeta` | Spec 1 §77, §58, Partie XIV ; WC4 C2, C3 |
| `ResetStepC s ar c i` | `SyncLib.lean:431` | `Arena.ResetD` sur la vue de `c`, réécrit dans `s` | Spec 1 §78, Partie XIV ; WC4 C2 |
| `Label` | `SyncLib.lean:497` | `.newArena c storage internal`, `.issue c arena region dst`, `.reset c arena` ; `.newMutex c g` perd la liste `adm` (A3) | WC4 C19, C23 |
| `LStep` | `SyncLib.lean:517` | état `SC × SyncReg × ArenaReg` ; les étiquettes du jalon 1 laissent le registre d'arènes inchangé ; les étiquettes d'arène laissent le registre de synchronisation inchangé | WC4 C2, C19, C23 |
| `LRun`, `EncapsulatedTrace` | `SyncLib.lean:589`, `:599` | sur le nouvel état ; `Encap` est lu sur `(st.1, st.2.1)` | WC4 C22, C23 |
| `newArenaStepC_ok`, `issueStepC_ok`, `resetStepC_ok` | `SyncLib.lean:447`, `:455`, `:467` | décomposition d'un pas `ok` en pas noyau | Partie XIV |

**`Encap` est inchangée.** Son texte est identique au caractère près ; les étiquettes d'arène tombent dans le cas `_ => True`. Aucune clause n'est nécessaire. T4 tient sur les étiquettes d'arène sous l'invariant `AdminSep`, qu'établit la garde A3 (§ A3). Il ne faut donc pas de restriction de trace.

**Décision : réindexation d'`issue` et de §76.6.** Le brief demande que les étiquettes d'arène soient « réalisées par les opérations dérivées de `Ern.MemoryModel.Arena` sur `s.view c` ». Appliquée à la lettre, cette consigne fait lire à `IssueD` et `NewArenaBase` l'`ancestor` séquentiel de §39. Or celui-ci se calcule sur l'ordre de la pile de la vue. Deux points interviennent :

- §77.3 et §77.6 (`IssueArrival`), ainsi que §65.4 et §65.5 dans le `store` de `IssueD`, lisent `ancestor` ;
- §76.6 lit `AnchorOrder` et `AnchorOrderHeld` sur l'état entier.

WC4 C3 impose l'ancêtre étendu (« follows the frame-parent links, including links across contexts »). Le jalon 1 a déjà réindexé sur `ancestorC` les clauses des opérations héritées qui lisent `ancestor`, dont `store`. J'ai suivi cette convention :

- `issue` = `split` exécuté par `c` (vue) puis `store` exécuté par `c` (`StorePreC`, réindexé) ;
- §76.6 lu sur `AnchorOrderC` et `AnchorOrderHeldC` ;
- `reset` = `ResetD` littéral sur la vue, car `derive` et `release` ne lisent pas `ancestor`.

La lecture littérale change des verdicts. Le témoin est `S3_8_view_literal` (`Corpus/AR.lean:175`). Au pas 8 de S3, `Arena.IssueD` sur la vue du contexte 0 rejette le `store` : `¬ AnchorOrderHeld` sur la vue, car dans la pile `[0, 1]` de la vue, la frame 0 n'est pas ancêtre de la frame 1 qui tient `d1`. `AnchorOrderHeldC` tient, et `S3_8_ok` est `ok`, comme le corpus le prescrit. En contexte unique, les deux lectures coïncident (A5). Cette décision change des programmes acceptés par rapport à la lettre du brief : je la signale comme point à arbitrer (§ A.4, P1).

### A2 — `ArenaInvC`, T7, extension de T4

- **`ArenaInvC s ar := Arena.LInv ⟨s.flat, ar⟩`** (`ArenaPreserve.lean:27`). C'est `ArenaInv` (§55) de chaque entrée vivante, avec les auxiliaires de `Arena.LInv` : tout `internal` enregistré existe, et `IssuedShape` tient. `ArenaInv` seul n'est pas inductif : il faut `IssuedShape` pour `issue`, et la borne pour qu'une entrée morte ne redevienne pas vivante.
- **Préservation de base.** `lstep_keep` (`:176`) : tout `LStep` conserve les autorités (`Arena.AKeep`) et les empreintes des places existantes.
- **T7.** `lstep_arenaInv` (`:333`) : tout `LStep` préserve `ArenaInvC`. Hypothèses : `WF3` avant le pas et `NoDangling` après, comme `Arena.lInv_stepNG`. Cela couvre :
  - `transfer`, y compris le transfert de la valeur d'arène, par `AKeep` et les empreintes ;
  - `spawn`, `spawnVal`, `terminate` et `exitFrameC`, idem ;
  - `newArena`, par `NewArenaPreC.arenaInv` ;
  - `issue`, par `lInv_issue_core` ;
  - `reset`, par `Arena.lInv_reset` appliqué à la vue et `lInv_congrF`.
- **Forme trace.** `encapsulated_arenaInv` (`Reachable.lean:143`).
- **Extension de T4.** `lstep_preserves` (`SyncInit.lean:945`) traite les trois étiquettes d'arène :
  - `newArena` ne change ni `s` ni `reg` ;
  - `issue` et `reset` sont deux pas noyau, auxquels s'applique `kernel_syncState` (`:921`), lemme nouveau qui assemble `opStep_facts` et `opStep_init` du jalon 1. La clause d'`Encap` du `split` ou du `derive` de `internal` (C22.1 : source ≠ `guarded` vivant) se déduit de `AdminSep`.
- **`AdminSep` n'est supposée que pour `issue` et `reset`** (hypothèse conditionnelle `lbl = .issue … ∨ lbl = .reset … → AdminSep …`). Pour les étiquettes du jalon 1, l'hypothèse est vide : l'énoncé du jalon 1 est retrouvé.
- **`LibInv L st := SyncState ∧ AdminSep ∧ ArenaInvC`** (`Reachable.lean:62`).
  - `lstep_inv` (`:75`) et `trace_inv` (`:87`) portent `KInvCA` et `LibInv`.
  - `libInv_nil` (`:67`) : avec un registre d'arènes vide, `LibInv` est `SyncState`. Les énoncés du jalon 1 correspondent à ce cas.
- **Préservation de `SyncState` par les étiquettes d'arène.** Dans `lstep_preserves` ci-dessus.

### A3 — garde §56 unifiée

- **`newMutex` consulte les `internal` des arènes vivantes.** `NewMutexPre.otherAdmin : g ∉ Arena.liveInternals s.flat ar` (`SyncLib.lean:249`). La liste fixe `adm` disparaît de `NewMutexPre`, `NewMutexOk` et `Label.newMutex`.
- **`newArena` consulte les `guarded` des entrées vivantes.** `NewArenaPreC.guard : Arena.Guard56 [Arena.liveInternals s.flat ar, liveGuardeds s reg] internal`, avec `liveGuardeds` (`SyncLib.lean:233`) l'image du registre de synchronisation en registre d'administrations vivantes.
- **Ce que `NewArenaPre.guard` d'`Arena.lean` permet sans modification.** Le paramètre `others : List (List Nat)` reçoit tout registre supplémentaire. Le passer à `[liveGuardeds s reg]` donne la garde unifiée, et `conservative_newArena` le montre en contexte unique : `NewArenaStepC` coïncide avec `Arena.NewArenaStep [liveGuardeds s reg]`. **Aucune modification d'`Arena.lean` n'est nécessaire.**
- **Ce qu'`Arena.lean` ne permet pas en multi-contexte.** `NewArenaPre` ne peut pas s'utiliser tel quel sur une vue. Ce n'est pas dû à la garde : `NewArenaBase` exige `AnchorOrder` et `AnchorOrderHeld` de §39 (A1). `NewArenaPreC` reprend donc les clauses une à une ; seule `Guard56` est réutilisée.
- **Invariant de la garde.** `AdminSep s reg ar` (`SyncLib.lean:490`) : aucune identité n'est à la fois le `guarded` d'une entrée vivante et l'`internal` d'une arène vivante. C'est la partie inter-registres de §56.
  - `lstep_adminSep` (`ArenaPreserve.lean:412`) : préservée par tout `LStep`. `newMutex` et `newArena` la vérifient par la garde. Les autres pas n'enregistrent rien et ne réactivent aucune autorité (`AKeep`), les identités enregistrées existant (`RegBound`, borne d'`ArenaInvC`).
  - **Nécessité.** `adminSep_needed` (`Corpus/Witness.lean:109`). Dans `MX₃`, qui vérifie `KInvCA` et `SyncState`, on ajoute une arène d'`internal` = `guarded` vivant. `AdminSep` est fausse. `issue(T)` est un pas `ok` admis par `Encap`, après lequel `GrantDiscipline` est fausse.
  - Cohérence avec §56 (« This guard is not a condition for any safety property in Section 57 ») : `AdminSep` sert à T4, qui est un invariant de bibliothèque. T2 et T7 ne l'utilisent pas.
- **Non fait.** L'unicité des `internal` vivants à l'intérieur du registre d'arènes (`Arena.Unique56` en séquentiel) n'est pas énoncée en concurrent. Ce n'était pas demandé.

### A4 — §82.3 et §82.6 sous `ReprC` (extension de R1)

Module `RealizeSound.lean`.

- **`pointer_sound_storeC`** (`:38`).
  - Énoncé : pour un `store` `ok` exécuté par `c`, les conclusions de `Refinement.pointer_sound_store` sur la vue de `c`. Les octets de la cible décodent l'adresse, avec la provenance de l'allocation de l'ancre effective ; règle de l'empan vide ; règle de l'adresse la plus basse.
  - Hypothèses : `ReprC`, `FramesC`, `WF3` et `NoDangling` de `s.flat`, plus les obligations de taille et d'encodage de l'original.
  - Preuve : copie de l'original. Celui-ci ne lit que §65.1 et §65.2, présents dans `StorePreC`.
- **`issue_pointer_soundC`** (`:124`) : les mêmes conclusions pour le bloc stocké par `issue`, sur l'état `t` après `split`.
- **`pinned_address_stableC`** (`:210`).
  - Énoncé : pour **tout** `LStep` depuis un état `KInvCA`, une feuille épinglée (obligation dynamique active ou `K.Pinned`) dont l'allocation est vivante garde une allocation vivante et la même adresse après la réalisation du pas.
  - Opérations héritées lues sur la vue : `Refinement.pinned_address_stable` sur la vue.
  - `exitFrameC` et `terminate` : `exit_keeps_pinned` (`:179`), copie du cas `exit` de l'original avec `ExitPreC.notPinned` et `TermPre.notPinned`.
  - Autres réalisations : aucune désallocation (`valOps_noDealloc` pour le composite).
- **Réalisation des étiquettes d'arène** (dans `3b9b7ff`).
  - `realize` prend le registre d'arènes : `issue` est la réalisation de `store` sur l'état après `split` (`realize_issue`, `Realize.lean:314`) ; `newArena` et `reset` n'ont aucune opération brute (`realize_arena_nil`, `:324`).
  - `r1_lstep` (`:512`) couvre les trois étiquettes. `issue` : `realize_store` sur la vue de l'état après `split`, `WF3` par `split_preserves_wf3`, sans `DDSound`. `reset` : exécution vide, `ReprC` conservée.
  - `StepOblC` des étiquettes d'arène : `OblAlong` de leurs opérations brutes.

### A5 — conservativité

Module `ArenaConservativity.lean`. Sur `s.Single` avec `FramesC s` :

- **`conservative_newArena`** (`:58`) : les issues de `NewArenaStepC s reg ar 0` sont celles d'`Arena.NewArenaStep [liveGuardeds s reg]` sur `⟨s.toS3, ar⟩`. Préconditions : `newArenaPreC_single` (`:36`).
- **`conservative_issue`** (`:91`) : celles d'`Arena.IssueD`, issue par issue, `fail` compris. Par T1 (`conservative_op`) sur `split` et `store`.
- **`conservative_reset`** (`:172`) : celles d'`Arena.ResetD`.
- **`r5_arena`** (`:196`) : `realize` de `newArena`, `issue` et `reset` est `RefinementArena.lopsOf` de l'opération correspondante sur la projection.

### A6 — docstring

`NewMutexPre` (`SyncLib.lean:245`) : « former C13.10 » est retiré. Les obligations non représentées sont nommées « C13.3, C13.6, initial physical controller state », comme dans le paragraphe d'interface de WC4 C13.

### A7 — re-vérification

- **Recompilation.** Tous les théorèmes des jalons 1 et 2 recompilent.
- **Comparaison mécanique des énoncés.** Script `stmts.py` : énoncé coupé au `:=` de niveau 0, espaces normalisés, comparé à `e30355f`. Aucune déclaration retirée. Les déclarations dont le texte change sont listées ci-dessous.

  | Classe | Déclarations | Nature |
  |---|---|---|
  | type de l'état de bibliothèque | `LStep`, `LRun`, `EncapsulatedTrace`, `EncapsulatedTrace.run`, `.snoc`, `simulationC`, `concrete_safety`, `lstep_kInvCA`, `encapsulated_inv` ; traces de test `traceA`, `traceB`, `traceMutex`, `endUse_*` (6), `transfer_merges_controllers_false`, `mutex_trace`, `distinct_controllers_trace`, `s4_trace`, `s4_simRun`, `s4_realized` | `SC × SyncReg` devient `SC × SyncReg × ArenaReg`, avec `(s, reg)` remplacé par `(s, reg, [])` ; contenu inchangé |
  | garde A3 | `NewMutexPre`, `NewMutexOk`, `newMutex_syncState`, `newMutex_preserves`, `newMutex_ctlUnique` ; `Label.newMutex` | `adm : List Nat` devient `ar : ArenaReg` ; `otherAdmin` lit le registre d'arènes |
  | étiquettes (A1) | `Label` | trois constructeurs ajoutés : `newArena`, `issue`, `reset` |
  | hypothèse ajoutée, conditionnelle | `lstep_preserves` | `AdminSep` pour `issue` et `reset` seulement ; énoncé inchangé pour les étiquettes du jalon 1 |
  | invariant élargi | `trace_inv` (hypothèse et conclusion `LibInv`), `trace_preserves` (hypothèse `LibInv`, conclusion `SyncState` inchangée), `init_inv` (conclusion `LibInv`) | équivalent à l'ancien quand le registre d'arènes est vide au départ (`libInv_nil`) |
  | réalisation | `realize`, `StepOblC`, `realize_sync`, `r5_realize`, `stepOblCDec` ; `SimRunC`, `r1_lstep`, `r3_step` (qui passent aussi `st.2.2`, en plus du changement de type) ; états du témoin `mS1`–`mS6` | argument `ar` ajouté ; même valeur sur les étiquettes du jalon 2 |

  Faux positifs du script : `Encap`, `EncapVals` et `valOps` sont des définitions par filtrage. Leur texte est identique, vérifié par comparaison de blocs.
- **Dépendances.** Script `Dep.lean` : clôture de `getUsedConstants` sur types et valeurs, restreinte aux constantes `Ern.Concurrency`. Les définitions modifiées sont `LStep`, `Label`, `NewMutexPre`, `NewMutexOk`, `LRun`, `EncapsulatedTrace`, `realize`, `StepOblC`, `SimRunC`, et les théorèmes modifiés ci-dessus. Aucune n'apparaît dans les dépendances de :
  - T1 : `conservative_op`, `conservative_ok`, `single_kInvC`, `reachable_single`, `syncAuthorized_false`, `conservative_deriveSync` ;
  - T2 : `opStepC_preservesC`, `spawnVal_preservesC` ;
  - T3 : `exitEffC_framesC`, `exitFrameC_anchorOrder`, `terminate_anchorOrder` ;
  - T5 : `realizability` ;
  - T6 : `grants_exclusive` ;
  - R1 par pas noyau (`r1_kernel`), `reprC_view`, `repr_frames_congr` ;
  - R4 et R4′ : `r4_nonConflict`, `r4_bytes`, `cross_context_disjoint` ;
  - `transfer_into_live_mutex_rejected`.

## A.3 Étape B — le corpus

Modules `Ern/Concurrency/Corpus/` : `MX.lean`, `AR.lean`, `Frames.lean`, `S10.lean`, `Witness.lean`.

- **Contrat.** `KC sm` : celui de `K0`, sauf que seules les feuilles de `sm` sont `SharedMutable`.
- **États.** Ceux de MX et AR sont atteints depuis l'état initial par des `EncapsulatedTrace` (`mx3_trace`, `mx4_trace`, `s2_trace`, `s9_trace`, `ar_trace`, `s3_trace`).
- **Encodage des verdicts** (règles du corpus §4) :
  - `ok`, `reject`, `fail` : issues de la relation de pas ;
  - `non habilité` (`wait`) : `∀ st', ¬ Op … st'` ;
  - `ok noyau / hors C22` : `ok` noyau et `¬ Encap`, avec la clause d'invariant qui tombe.
  - `unlock` et `resetLock` ne définissent que `ok` (décision 4 du jalon 1). Pour eux, `reject` s'écrit : absence d'issue `ok`, conjointe à la clause défaillante citée par le corpus.

| Cas | Verdict attendu (clause du corpus) | Verdict obtenu | Théorème (module:ligne) | Écart |
|---|---|---|---|---|
| S1a | `reject` (O7.2, `NoDangling`) ; jumeau `ok` | `reject` ; jumeau `ok` | `S1a_1_reject` (`Corpus/Frames:47`), `S1a_2_ok` (`:60`) | — |
| S1b | `ok` (O7.4, O7.5) ; puis `write3(Y)` `reject` (§43.3) | `ok` (`q` libérée, `a` réancrée sur `root_Y`, contexte 1 reparenté sur 0) ; `reject` | `S1b_1_ok` (`Corpus/Frames:86`), `S1b_2_reject` (`:97`) | — |
| S2 | `ok`, `ok`, `ok` ; négatif `non habilité` (C14.2) | idem | `S2_1_ok` … `S2_3_ok` (`Corpus/MX:136`–`136`), `S2_4_wait` (`:142`) ; T6 `grants_exclusive` | — |
| S3.1 | `reject` (§77.1) | `reject` (statique : `¬ MetaRight`) | `S3_1_reject` (`Corpus/AR:83`) | — |
| S3.2, S3.3 | `ok`, `ok` (§43 cl. 2, §77.3, §77.6) | `ok`, `ok` | `S3_2_ok` (`Corpus/AR:93`), `S3_3_ok` (`:109`) | — |
| S3.4 | `non habilité` (C14.2) | idem | `S3_4_wait` (`Corpus/AR:115`) | — |
| S3.5, S3.6 | `ok`, `ok` | idem | `S3_5_ok` (`Corpus/AR:131`), `S3_6_ok` (`:140`) | — |
| S3.7 | **`fail`** (§77.4) | `fail`, statiques vrais, aucune issue `ok` | `S3_7_fail` (`Corpus/AR:146`) | — |
| S3.8 | `ok` | `ok` | `S3_8_ok` (`Corpus/AR:167`) | `ok` grâce à la réindexation A1 ; lecture littérale : `S3_8_view_literal` (`:175`, P1) |
| S3, négatif supplémentaire | `reject` (§78.2) | `reject` | `S3_3b_reject` (`Corpus/AR:123`) | même verdict, autre clause : l'opération dérivée rejette au `derive` (§60.2, mode effectif absent) (P6) |
| S4 | `ok` (C5, C6) ; négatif `reject` (O7.2) | `ok` ; `reject` | référencés : `s4_trace` (`Traces:289`), `s4_detached_child` (`:302`), `s4_realized` (`Realize:842`) ; nouveau : `S4_2_reject` (`Corpus/Frames:114`) | négatif absent avant ce jalon |
| S5a | `reject` (O11.1) ; jumeau `ok` | idem | `S5a_1_reject` (`Corpus/MX:160`) ; jumeau `S2_2_ok` | — |
| S5b | `ok noyau` (O11.1, O11.2), hors C22.4, OB-C05 | `ok` noyau, admis par `Encap` | `S5b_1_ok` (`Corpus/MX:170`) | non refusé, comme prescrit |
| S6 | `hors fragment` (OB-C04) | — | aucun théorème | — |
| S7 | `ok` (O4) ; négatif `reject` (§63.1, §63.4) | `ok` ; `reject`, les deux clauses fausses | référencés : `traceA`, `traceB` (`EncapTraces:135`, `:145`) ; nouveau : `S7_2_reject` (`Corpus/MX:179`) | négatif absent avant ce jalon |
| S8 | `reject` (§43) ; jumeau `ok` | idem | `S8_1_reject` (`Corpus/MX:193`), `S8_2_ok` (`:206`) | — |
| S9 | `ok`, `ok`, propriété ; négatif `reject` (C13.8) | idem | `S9_1_ok` (`Corpus/MX:424`), `S9_2_ok` (`:432`), `s9_trace` (`:408`) ; référencé : `shared_controller_rejected` (`Traces:225`) | — |
| S10 | **`reject`** (O4.7) | **`ok`**, admis par `Encap`, sur une `EncapsulatedTrace` depuis l'état initial | `S10_1_ok` (`Corpus/S10:43`), `s10_trace` (`:52`) ; jumeau référencé : `traceB` | **désaccord** (P2) |
| S11.1 | `ok` (O7 libère `g`) | `ok` | `S11_1_ok` (`Corpus/MX:278`) | mise en place lue avec `o1′` cédée à `f1′` (P3) ; lecture littérale : `S11_setup_wait` (`:258`) |
| S11.2 | `non habilité` (C14.2) | idem | `S11_2_wait` (`Corpus/MX:287`) | — |
| S11.3 | `reject` (C18.1) | aucune issue `ok` ; `¬ ExercisableAt(guarded, Modify)` | `S11_3_reject` (`Corpus/MX:294`) | encodage de `reject` (P7) |
| S11, jumeau | `ok` ×4 | idem | `S11_4_ok` (`Corpus/MX:308`) | — |
| S12 | `ok noyau`, hors C22.4, OB-C05 ; jumeau `acquire`/`unlock` | `ok` noyau, admis par `Encap` ; jumeau `ok` | `S12_1_ok` (`Corpus/MX:322`), `S12_2_ok` (`:333`) | le corpus le dit « déjà encodé » ; il ne l'était pas (P4) |
| S13 | `reject` (O10.1) ; jumeaux (a) et (b) `ok` | idem | `S13_1_reject` (`Corpus/Frames:135`), `S13_2_ok` (`:149`), `S13_3_ok` (`:164`) | — |
| S14 | `ok`, `ok` ; négatif `reject` (O1.2, O1.3) | idem | `S14_1_ok` (`Corpus/Frames:188`), `S14_2_ok` (`:193`), `S14_3_reject` (`:199`) | — |
| S15 | `ok`, `ok`, `ok`, **`reject`** (C17.2) ; jumeau `ok` | idem | `S15_1_ok` (`Corpus/MX:222`), `S15_4_reject` (`:231`), `S15_5_ok` (`:244`) | encodage de `reject` (P7) |
| S16 (a), (c) | `ok noyau / hors C22.3`, sans l'exclusion `control` resp. `ctlInit` faux | idem | référencés : `slot_transfer_breaks_control` (`EncapTraces:202`), `ctl_transfer_breaks_ctlInit` (`:222`) | (c) est encodé avec `transfer(lock, Y)` au lieu de `Z` : sans effet |
| S17a | `ok noyau / hors C22.5 (a)` ; jumeau : `endUse(slot)`, puis `endUse(lock)` admis | idem | référencé : `endUse_ctl_excluded` (`EncapTraces:243`) ; nouveau : `S17a_2_ok` (`Corpus/Witness:83`) | jumeau du corpus absent avant ce jalon (P5) |
| S17b | `ok noyau / hors C22.5 (b)` ; jumeau `ok` | idem | référencés : `endUse_slotPart_excluded` (`EncapTraces:307`), `endUse_slot_kills_entry` (`:332`) | — |
| S18 | (1) `reject` C13.10 ; (2) `reject` §63.3 | idem | référencés : `newMutex_uninit_rejected` (`EncapTraces:450`), `transfer_into_live_mutex_rejected` (`SyncInit:1017`) ; jumeaux `traceA`, `traceB` | (2) est un théorème général sous `SyncState`, sans instance concrète de la configuration (2) |
| W-C22.2 | `ok noyau / hors C22.2` ; après le pas, `GrantDiscipline` faux, `acquire` plus jamais habilité | `ok` noyau, `¬ Encap`, `¬ GrantDiscipline`, `acquire` non habilité pour les contextes 0 et 1 dans l'état d'arrivée ; **mais** un `release` ordinaire de la dérivée, admis par `Encap`, rétablit `GrantDiscipline` et `acquire` redevient habilité | `W_C22_2_encap` (`Corpus/MX:346`), `W_C22_2_reenable` (`:365`) ; jumeau `S2_1_ok` | **désaccord** sur « plus jamais » (P8) |
| W-C22.3 (b) | `ok noyau / hors C22.3 (b)`, `slotInit` faux ; jumeau `transfer(M, M′)` | idem ; jumeau `ok`, admis par `Encap`, `SlotInit` vrai | `W_C22_3b_encap` (`Corpus/Witness:48`), `W_C22_3b_ok` (`:66`) | — |
| témoin R4 | — | référencé | `r4_nonvacuous` (`NonConflict:185`) | — |
| `CrossContextConflictOnlyShared` | prouvé | prouvé | `crossContextConflictOnlyShared` (`Corpus/Witness:136`) | — |
| témoin de `CrossContextConflictOnlyShared` | `writeShared(lock)` par `c0` et `read3(lock)` par `c1` habilités dans `MX₄`, `L ∩ L′ = {lock}` | idem | `crossContextConflictOnlyShared_witness` (`Corpus/Witness:143`) | — |

**Cas déjà encodés : contrôle de correspondance.**

- **Contrat.** Les encodages des jalons 1 et 2 (`est`, `sst`, `mst`, S4) utilisent `K0`, où toute feuille est `SharedMutable`. Le corpus n'exige `SharedMutable` que pour `lock`. Aucun pas de ces cas ne lit `SharedMutable`, sauf C13.6 sur `lock` : les verdicts sont inchangés.
- **Statiques.** `est` ajoute une place `Y` au bloc MX ; `sst` est exactement le `MX₃` de S17b.

## A.4 Problèmes trouvés

- **P1 — lecture littérale des opérations dérivées sur la vue** (brief A1 ; WC4 C2, C3).
  - Passage du brief : « réalisées par les opérations dérivées de `Ern.MemoryModel.Arena` sur `s.view c` ».
  - Exemple : S3, pas 8. Avec `Arena.IssueD` sur `a10.view 0`, `store` est rejeté (`S3_8_view_literal`), alors que le corpus prescrit `ok`.
  - Choix fait : la convention du jalon 1, tirée de WC4 C3. Il faut confirmer qu'il est le bon.
- **P2 — S10 : désaccord entre le corpus et le modèle.**
  - **Clause citée par le corpus :** O4.7, avec la justification « `g` détenue par `f0`, son anchor effectif `root_T` passe en `f1` ».
  - **État :** `r3`. Depuis `MX₃`, `c0` a acquis `g` (autorité 4, tenue par la frame 0) puis est entré en `f1` en cédant `m := derive(root_M, Modify)`, avec un local `M′`.
  - **Verdict effectif :** `ok` de la machine avec la bibliothèque, pas seulement du noyau. `S10_1_ok` (`S10.lean:43`) établit que `transfer(M, M′)` est `ok` et admis par `Encap` ; `s10_trace` (`:52`) en fait une `EncapsulatedTrace` depuis l'état initial. Après le pas, l'ancre effective de `g` est en `f1`, qui n'est pas ancêtre de la frame 0 (`¬ EffAnchorOKC r4 4 (some 0)`), et `exitFrameC(f1)` est rejeté.
  - **Cause :** la première phrase de §63.7 porte sur les autorités tenues **déplacées** (« All moved held authorities … satisfy `AnchorOrderHeld` »). `AnchorOrderHeld` (§44) ne porte que sur les autorités tenues par des places. `g` est tenue par une frame et ne bouge pas. Les autorités déplacées (`guarded` vers `slot′`, `root_T` vers `M′`) satisfont la règle en `f1`. La seconde phrase, « no authority may escape a local anchor on the grounds that its containing value was transferred », ne dit pas si elle couvre une autorité non déplacée dont l'ancre effective est déplacée. Le modèle de la Spec 1 encode §63.7 de la même façon (`Access/Ops.lean`, `TransferPre.anchorOrderHeld` : les seules autorités `AnchorMoves`).
  - **Conséquence :** le pas n'est pas dangereux. L'état est bloqué : `f1` ne peut plus sortir. C'est un silence de la Spec 1 §63.7, à arbitrer ; ni le corpus ni le modèle ne sont corrigés.
- **P3 — S11 : mise en place sous-spécifiée.**
  - Passage : « `c1 : enterFrame f1′` ; `acquire(e)` → `g` détenue par `f1′` ».
  - Exemple : `f1′` entrée sans paramètre ne tient aucune autorité sur `lock`. C14.3 (`CtrlRight`) échoue, et `acquire` n'est pas habilité (`S11_setup_wait`).
  - Les cas S11 sont encodés en cédant `o1′ := derive(o1, Observe)` à `f1′`. Les verdicts du corpus sont alors tous obtenus. Ce choix de mise en place est à confirmer.
- **P4 — S12 « déjà encodé ».** Aucun théorème des jalons 1–2 n'encodait `write3(lock)`. Le jalon 2 le mentionne seulement dans son rapport. Encodé ici : `S12_1_ok`, `S12_2_ok`.
- **P5 — jumeau de S17a.** Le jalon 1 encodait `endUse(M)`, positif de S17b, faute du positif littéral (remarque X2 de `spec2-m1-close.md`). Le jumeau du corpus, `endUse(slot)` puis `endUse(lock)` admis par `Encap`, est encodé ici (`S17a_2_ok`).
- **P6 — clause de rejet du `reset` sous bloc actif.** Le corpus cite §78.2. L'opération dérivée rejette au `derive` de `internal` : son mode effectif sur `R1` est absent (§43.3, §60.2). Même verdict. Sur les états accessibles séquentiels, `Arena.reset_iff_derive_release` établit l'équivalence des deux lectures. Elle n'est pas transportée au cas concurrent.
- **P7 — `reject` des opérations à issue `ok` seule.** `UnlockOk` et `ResetLockOk` ne définissent que `ok` (WC4 C17, C18 ne donnent pas d'autre issue). Le modèle ne distingue donc pas `reject` de « non habilité » pour elles. S11.3 et S15.4 sont encodés par l'absence d'`ok` et la clause défaillante du corpus.
- **P8 — W-C22.2 : désaccord sur « `acquire(e)` plus jamais habilitée ».**
  - **Clause citée par le corpus :** C13.9/C14 (« descendant bloquant »).
  - **État :** `x5`, après le `deriveSync` brut du contexte 1 depuis `MX₄` ; le registre garde `grant = none`.
  - **Verdict effectif :** dans `x5`, `acquire` n'est habilité pour aucun contexte (`W_C22_2_encap`). Mais le contexte 1 peut libérer la dérivée par un `release` ordinaire (O3), pas `ok` admis par `Encap` ; `GrantDiscipline` est alors rétablie et `acquire(e)` par le contexte 1 est habilité (`W_C22_2_reenable`, `MX.lean:365`). WC4 C15 (effet) le permet : la dérivée « is ordinary after creation … for its … legal release ».
  - **Lecture :** « plus jamais » est trop fort ; le blocage dure tant que la dérivée est active. Ni le corpus ni le modèle ne sont corrigés.
- **P9 — nom du document WC4.** Voir l'en-tête.

## A.5 Décisions de représentation du jalon 3

1. **État de bibliothèque.** `SC × SyncReg × ArenaReg`. `Encap` garde sa signature et est lu sur `(st.1, st.2.1)`.
2. **Opérations d'arène exécutées par un contexte.** `newArena` : clauses de `NewArenaBase` sur la vue, §76.6 sur l'état concurrent. `issue` : forme d'`IssueD` avec `opStepC` pour `split` et `store`. `reset` : `ResetD` sur la vue. Voir P1.
3. **Issues.** Les relations d'arène ont des issues `Outcome3`, `fail` compris pour `issue`. `LStep` ne contient que les pas `ok`, comme au jalon 1.
4. **`ArenaInvC`** est `Arena.LInv` sur `s.flat` : `ArenaInv` (§55), avec `IssuedShape` et la borne des `internal`.
5. **`AdminSep`.** Partie inter-registres de §56, invariant de trace. L'unicité intra-registre n'est énoncée que pour le registre de synchronisation (`SyncInv.unique`, jalon 1).
6. **`lstep_preserves`.** `AdminSep` y est une hypothèse conditionnelle, active pour `issue` et `reset` seulement.
7. **`realize` et `StepOblC`.** Ils prennent le registre d'arènes. `issue` est réalisé par `store` sur l'état après `split`, comme `RefinementArena.kexp`. `newArena` et `reset` n'ont aucune opération brute.
8. **Corpus.** Contrat `KC sm` ; encodages des verdicts de § A.3 ; noms `S<cas>_<n>_<verdict>`. Le verdict obtenu est dans le nom quand il diffère du corpus (S10), et le désaccord est dans la docstring.
9. **§76.6, « `WF3` ».** Lu `WF3 s.flat`, composant de la Spec 1 sur les frames vivantes. `FramesC`, la structure des contextes de WC4 C20, n'est pas exigé par `newArena`, qui ne change pas les contextes ; il tient sur les états atteints (T2).

## A.6 Écarts avec la Spec 1

Aucun, hors la réindexation sur `ancestorC` exigée par WC4 C3. A5 montre qu'en contexte unique les opérations d'arène coïncident avec celles d'`Arena.lean`, issue par issue, et que leurs réalisations coïncident avec celles de `RefinementArena.lean`.

## A.7 Revue adversariale

Quatre relecteurs indépendants, en lecture seule, ont revu le jalon : étape A ; extensions de réalisation (A4, R1) ; encodage du corpus ; exactitude du rapport. Verdicts : `ok`, `ok`, `changes`, `changes` ; aucun point bloquant. Chaque constat a été vérifié avant correction.

| Constat | Vérification | Suite |
|---|---|---|
| W-C22.2 : « plus jamais habilitée » réfuté par un `release` ordinaire | confirmé par `decide` | `W_C22_2_reenable`, P8 réécrit en désaccord |
| S10 : `S10_1_ok` ne montrait qu'un `ok` noyau | `TransferExcl` vrai | `Encap` ajouté à `S10_1_ok`, `s10_trace` |
| W-C22.3 (b) : jumeau dans une autre configuration (`slot` à une feuille) | confirmé | `W_C22_3b_ok` dans la configuration `slot = {a, b}` |
| OB-C12 : §82.7 présenté comme couvert | confirmé : rien dans `Ern/Concurrency` ne transporte `arena_realized` | ligne réécrite |
| ligne de 105 caractères dans `AR.lean`, et affirmation fausse sur les lignes longues | confirmé | ligne coupée, affirmation corrigée |
| plage de lignes T3, attribution de `kernel_syncState`, table A7 incomplète, B.3 incomplète | confirmés | corrigés |
| `NewArenaPreC.wf3` citait C20 sans exiger `FramesC` | confirmé ; sans effet sur les états atteints | docstring corrigée, décision 9 |
| docstrings de `Label` et de `Reachable.lean` périmées | confirmé | corrigées |
| P1 (lecture d'`IssueD` sur la vue), unicité intra-registre | déjà signalés | inchangés |

---

# Partie B — index consolidé des jalons 1 à 3

État de la branche à `8e2bccf`. Les numéros de ligne sont ceux de ce commit. Chemins relatifs à `formal/Ern/Concurrency/`.

## B.1 Modules

| Module | Jalon | Définitions principales | Clauses |
|---|---|---|---|
| `Context.lean` | 1 | `SC` (`:46`), `SC.view` (`:84`), `SC.set`, `SC.flat`, `SC.Single`, `SC.toS3`, `SC.ofS3` ; `SC.parC`, `SC.ancestorC` (`:128`) ; `AnchorOrderC` (`:149`), `AnchorOrderHeldC` (`:163`) ; `FramesC` (`:190`), `ConcurrentWF` (`:209`), `KInvC` (`:224`) | WC4 C1–C3, C20, C24 ; Spec 1 §44, §57 |
| `Frames.lean` | 1 | `ViewStep` (`:36`), `opStepC` (`:270`) ; préconditions réindexées ; `exitEffC` (`:225`), `ExitPreC` (`:233`) ; `SpawnPre` (`:318`), `SpawnStep` (`:344`) ; `TermPre` (`:361`) ; `JoinStep` (`:407`) | C2, C4, C6–C8 ; Spec 1 §60–§75 |
| `Conservativity.lean` | 1 | T1 | C24, C3 |
| `Sync.lean` | 1 | `KC R` (`:23`), `DeriveSyncPre` (`:36`), `DeriveSyncStep` (`:78`) | C2, C14, C15 |
| `SyncLib.lean` | 1, 3 | registre de synchronisation, `ControlOf` (`:61`), `CtrlRight` (`:78`), `libKC` (`:108`), `GrantDiscipline` (`:173`), `SyncInv` (`:194`) ; `NewMutexPre` (`:249`), `AcquireOk` (`:308`), `UnlockOk` (`:318`), `ResetLockOk` (`:329`) ; **jalon 3 :** `ArenaReg` (`:229`), `liveGuardeds` (`:233`), `NewArenaPreC` (`:344`), `NewArenaStepC` (`:395`), `IssueStepC` (`:406`), `ResetStepC` (`:431`), `AdminSep` (`:490`) ; `Label` (`:497`), `LStep` (`:517`), `Encap` (`:578`), `EncapsulatedTrace` (`:599`) | C12–C18, C21–C23 ; Spec 1 §46, §56, §76–§78 |
| `Transfer.lean` | 1 | composite par valeur : `spawnValEff` (`:40`), `SpawnValPre` (`:130`), `SpawnValStep` (`:185`) | C4, C5 |
| `TransferPreserve.lean` | 1 | `KBase`, `spawnVal_preservesC` (`:299`) | C5, C20 |
| `Preservation.lean` | 1 | `KInvCA` (`:24`), T2 pour O1–O16, `spawn`, `join`, `deriveSync` | C20, C23 |
| `Reparent.lean` | 1 | T3, T2 pour `exitFrameC` et `terminate` | C6, C7, OB-C13 |
| `SyncPreserve.lean` | 1 | `SyncState` (`:25`) et lemmes par opération | C21, C22 |
| `SyncInit.lean` | 1, 3 | T4 par pas (`lstep_preserves`, `:945`), `kernel_syncState` (`:921`), `transfer_into_live_mutex_rejected` (`:1017`) | C21.4, C21.7, C22, C23 |
| `ArenaPreserve.lean` | 3 | `ArenaInvC` (`:27`), `Keep`, `lstep_keep` (`:176`), T7 (`lstep_arenaInv`, `:333`), `lstep_adminSep` (`:412`) | Spec 1 §55, §56 ; C19 |
| `Reachable.lean` | 1, 3 | `lstep_kInvCA` (`:28`), `LibInv` (`:62`), `libInv_nil` (`:67`), `lstep_inv` (`:75`), `trace_inv` (`:87`), `init_inv` (`:105`), `encapsulated_inv` (`:131`), `encapsulated_arenaInv` (`:143`) | C20–C23 ; Spec 1 §55 |
| `ArenaConservativity.lean` | 3 | `projL`, conservativité des opérations d'arène, `r5_arena` | C24 ; Spec 1 §76–§78, §82.7 |
| `Repr.lean` | 2 | `ReprC` (`:23`), `repr_congr`, `repr_frames_congr` (`:38`), `reprC_view` (`:46`) | C2, C25 ; Spec 1 §82.1 |
| `Realize.lean` | 2, 3 | `kopOf`, `valOps`, `realize` (`:271`), `StepOblC` (`:337`), R1, R5, `SimRunC` (`:678`), R2, R3, témoin S4 | C2, C4–C8, C13–C19, C25 ; Spec 1 §82 |
| `RealizeSound.lean` | 3 | §82.3 et §82.6 sous `ReprC` | Spec 1 §82.3, §82.6 |
| `NonConflict.lean` | 2 | R4, R4′ | Spec 1 §43, §50, §82.8 |
| `Traces.lean`, `EncapTraces.lean` | 1 | tests des jalons 1–2 | § B.3 |
| `Corpus/MX.lean`, `Corpus/AR.lean`, `Corpus/Frames.lean`, `Corpus/S10.lean`, `Corpus/Witness.lean` | 3 | corpus du jalon 3, `CrossContextConflictOnlyShared` | `corpus-spec2-m3.md` |

## B.2 Théorèmes

| T | Nom (module:ligne) | Énoncé | Hypothèses |
|---|---|---|---|
| T1 | `conservative_op`, `conservative_ok` (`Conservativity:457`, `:489`) | en contexte unique, O1–O16 ont les issues de la Spec 1 sur la projection | `s.Single`, `FramesC s` |
| T1 | `single_ancestorC`, `single_anchorOrderC`, `single_anchorOrderHeldC`, `single_kInvC` (`Conservativity:141`, `:209`, `:218`, `:229`) | coïncidences avec §39, §44, §57 | `s.Single` (et pile décroissante) |
| T1 | `reachable_decreasing`, `reachable_single` (`Conservativity:534`, `:569`) | tout état atteignable de la Spec 1 est la projection d'un état à un contexte avec `KInvC` | `DDSound`, `StaticsOK` |
| T1 | `syncAuthorized_false`, `conservative_deriveSync` (`SyncLib:618`, `:626`), `libKC_sound` (`:123`) | sans entrée vivante, ni `SyncAuthorized` ni `deriveSync` | `SyncSound` |
| T1 (j. 3) | `conservative_newArena`, `conservative_issue`, `conservative_reset` (`ArenaConservativity:58`, `:91`, `:172`) | en contexte unique, `newArena`, `issue`, `reset` ont les issues de `NewArenaStep [liveGuardeds s reg]`, `IssueD`, `ResetD` sur la projection | `s.Single`, `FramesC s` (`reset` : `s.Single`) |
| T2 | `opStepC_preservesC` (`Preservation:1815`), `exitFrameC_preserves`, `terminate_preserves` (`Reparent:779`, `:792`), `spawn_preservesC`, `join_preservesC`, `deriveSync_preservesC` (`Preservation:1844`, `:1851`, `:1857`), `spawnVal_preservesC` (`TransferPreserve:299`) | `KInvCA` préservé par pas | `DDSound` (pour `split`), `KInvCA` |
| T2 | `lstep_kInvCA` (`Reachable:28`) | tout `LStep`, étiquettes d'arène comprises, préserve `KInvCA` | `DDSound`, `KInvCA` |
| T3 | `exitEffC_framesC`, `termEffC_framesC` (`Reparent:654`, `:671`) ; `exitEffC_ancestorC`, `termEffC_ancestorC`, `exitEffC_reparent`, `termEffC_reparent`, `exitEffC_kernel`, `termEffC_kernel`, `exitFrameC_anchorOrder`, `terminate_anchorOrder` (`Reparent:690`–`767`) | reparentage : `FramesC`, `ancestorC`, `AnchorOrderC` | `FramesC`, `WF3`, `AnchorOrderC` |
| T4 | `lstep_preserves` (`SyncInit:945`) | tout `LStep` préserve `SyncState` | **`Encap`**, `KInvCA` avant, `WF3` après, **`AdminSep` pour `issue` et `reset`** |
| T4 | `trace_inv`, `trace_preserves` (`Reachable:87`, `:98`) | `KInvCA` et `LibInv` le long d'une trace | **`EncapsulatedTrace`**, `DDSound`, invariants au départ |
| T4 | `init_inv`, `encapsulated_inv` (`Reachable:105`, `:131`) | état initial ; depuis l'état initial : `KInvC`, `SyncInv`, `GrantDiscipline` | `DDSound`, `StaticsOK` (et **`EncapsulatedTrace`**) |
| T5 | `realizability` (`SyncLib:668`) | les faits C14.1–C14.3 entraînent `DeriveSyncPre` | `KInvC`, `SyncInv`, `GrantDiscipline`, contexte vivant |
| T6 | `grants_exclusive` (`SyncLib:646`) | deux grants actifs pleins ne coexistent pas | `WF3`, `I1` |
| T7 | `lstep_arenaInv` (`ArenaPreserve:333`) | tout `LStep` préserve `ArenaInvC` | `WF3` avant, `NoDangling` après |
| T7 | `encapsulated_arenaInv` (`Reachable:143`) | depuis l'état initial : `ArenaInvC` et `AdminSep` | **`EncapsulatedTrace`**, `DDSound`, `StaticsOK` |
| §56 | `lstep_adminSep` (`ArenaPreserve:412`) | tout `LStep` préserve `AdminSep` | `AdminSep`, bornes des identités enregistrées |
| R1 | `r1_lstep` (`Realize:512`) | la réalisation d'un pas est une exécution de pas bruts `ok` qui garde `ReprC` | `ParamsOK`, `ReprC`, `KInvCA`, `StepOblC` |
| R1, §82.3 | `pointer_sound_storeC` (`RealizeSound:38`), `issue_pointer_soundC` (`:124`) | adresse et provenance écrites par `store` et par `issue` | `ReprC`, `FramesC`, `WF3`, `NoDangling`, taille et encodage |
| R1, §82.6 | `pinned_address_stableC` (`RealizeSound:210`) | une feuille épinglée vivante garde allocation et adresse, pour tout `LStep` | `ReprC`, `KInvCA`, allocation vivante |
| R2 | `simulationC` (`Realize:699`) | toute `SimRunC` est atteinte par une exécution `ok` depuis la mémoire vide, sous `ReprC`, et sa suite d'étiquettes est une `EncapsulatedTrace` | `DDSound`, `ParamsOK` |
| R3 | `r3_step` (`Realize:750`), `concrete_safety` (`:764`) | aucune opération brute `ub` | celles de R1 ; de R2 |
| R4 | `r4_nonConflict` (`NonConflict:141`) | deux accès ordinaires habilités de contextes distincts ne partagent pas de feuille non `SharedMutable` (en fait aucune) | `KInvC` |
| R4′ | `r4_bytes` (`NonConflict:150`) | disjonction en octets | `KInvC`, `LayoutWF` |
| R5 | `r5_realize` (`Realize:644`), `r5_arena` (`ArenaConservativity:196`) | en contexte unique, réalisations de la Spec 1 | `s.Single` |
| corpus §3 | `crossContextConflictOnlyShared` (`Corpus/Witness:136`) | un `writeShared` et un accès de contextes distincts ne partagent que des feuilles `SharedMutable` | aucune |

## B.3 Corpus complet

**Jalon 3** (`corpus-spec2-m3.md`) : la table de § A.3 donne pour chaque ligne le verdict attendu, le verdict obtenu, la clause et le théorème. Deux désaccords : S10 (P2) et « plus jamais habilitée » de W-C22.2 (P8) ; S6 est hors fragment.

**Jalon 1** (`spec2-m1-close.md` § B.3, repris avec les jumeaux ; « P1 » y désigne la proposition P1 de la passe 1 du jalon 1) :

| Énoncé (module:ligne) | Verdict | Jumeau positif | Clause |
|---|---|---|---|
| `acquire_blocked_by_derive` (`Traces:75`) | `derive(guarded, Observe)` non encapsulé : `GrantDiscipline` faux, `acquire` non habilité | `acquire_enabled` (`Traces:92`), `unlock_enabled` (`:99`), `mutex_trace` (`:104`) | C22.1, C16 |
| `realizability_needs_i1` (`Traces:119`) | I1 nécessaire à T5 | `realizability` (`SyncLib:668`) | C25, Spec 1 §50 |
| `join_waits` (`Traces:164`), `join_unknown_rejected` (`:172`) | `join` : aucune issue sur un contexte vivant ; `reject` sur identifiant inconnu | `frames_run` (`Traces:156`) | C8 |
| `shared_controller_rejected` (`Traces:225`) | second `newMutex` sur le même contrôleur : rejeté | `distinct_controllers_ok` (`:245`), `distinct_controllers_trace` (`:252`) ; au jalon 3 : `S9_1_ok`, `S9_2_ok` | C13.8 (S9) |
| `deriveSync_observe_rejected` (`Preservation:1883`) | `deriveSync` depuis `Observe` : `reject` | `deriveSync_modify_ok` (`:1890`) | C15.1 |
| `deriveSync_breaks_i2_false` (`Preservation:1896`) | négation, pour tout `KC R`, de l'ancien contre-exemple I2 | — | C15.1 |
| `spawnVal_covering_rejected` (`Transfer:205`) | paramètre couvrant une source par valeur : `reject` | `spawnVal_apart_ok` (`:214`) | C5, précondition 5 |
| `newMutex_nonleaf_rejected` (`SyncPreserve:1351`) | contrôleur non feuille : `newMutex` rejeté | `newMutex_ok` (`Traces:58`) | C12, C13.3 |
| `newMutex_uninit_rejected` (`EncapTraces:450`) | `newMutex` sur des champs `Uninit` : rejeté | sa première moitié | C13.10 (S18 (1)) |
| `transfer_merges_controllers_false` (`EncapTraces:456`) | `newMutex(1)`, `newMutex(3)`, `transfer(M, M′)` depuis `m0` n'est pas un `LRun` | — | C13.10 |
| `slot_transfer_breaks_control` (`EncapTraces:202`), `ctl_transfer_breaks_ctlInit` (`:222`) | S16 (a), (c) | `controlAB` (`:184`), `invA` (`:170`), `invB` (`:177`) | C22.3 (a), (c) |
| `transfer_into_live_mutex_rejected` (`SyncInit:1017`) | S18 (2) | `invA`, `invB` | §63.3, C21.7 |
| `endUse_ctl_excluded` (`EncapTraces:243`) | S17a | `endUse_mutex_kills_entry` (`:265`) ; au jalon 3 : `S17a_2_ok` | C22.5 (a) |
| `endUse_slotPart_excluded` (`EncapTraces:307`) | S17b | `endUse_slot_kills_entry` (`:332`) | C22.5 (b) |
| `endUse_then_transfer_merges`, `_false` (`EncapTraces:381`, `:417`) | fusion de contrôleurs dans un `LRun` qui n'est pas une `EncapsulatedTrace` | `invA`, `invB` | C21.4, C22.5 (b) |
| `alloc_ok_satisfiable`, `alloc_fail_unsatisfiable` (`Frames:282`, `:293`) | `K.Satisfiable` évalué sur la vue | — | C2 (P1 du jalon 1) |
| `s4_steps`, `s4_trace`, `s4_detached_child` (`Traces:280`, `:289`, `:302`) | S4 positif | — ; au jalon 3, négatif `S4_2_reject` | C5, C6 |

**Jalon 2** :

| Énoncé (module:ligne) | Verdict | Clause |
|---|---|---|
| `s4_realized` (`Realize:842`) | trace S4 réalisée en mémoire, aucun pas `ub` | C5, C6 ; Spec 1 §82 |
| `r4_nonvacuous` (`NonConflict:185`) | non-vacuité de R4 | — |

**Jalon 3, hors table de § A.3** :

| Énoncé (module:ligne) | Verdict | Clause |
|---|---|---|
| `adminSep_needed` (`Corpus/Witness:109`) | nécessité de `AdminSep` pour T4 | Spec 1 §56 ; C13.7 |
| `S3_8_view_literal` (`Corpus/AR:175`) | lecture littérale d'`IssueD` sur la vue : `reject` du pas 8 de S3 | WC4 C3 ; Spec 1 §65.5 |
| `S11_setup_wait` (`Corpus/MX:258`) | lecture littérale de la mise en place de S11 : `acquire` non habilité | C14.3 |

## B.4 Décisions de représentation (cumulées)

- **Jalon 1** : les décisions 1 à 18 de `spec2-m1-close.md` § B.4 restent en vigueur, avec deux mises à jour :
  - la 4 (opérations de bibliothèque à issue `ok` seule) détermine l'encodage de `reject` pour `unlock` et `resetLock` (§ A.4, P7) ;
  - la 10 (`unique` par indice) ne vaut que dans le registre de synchronisation.
- **Jalon 2** : les décisions 1 à 10 de `spec2-m2.md` § 6 restent en vigueur.
  - La 3 (réalisation unique par `opsOf` sur la vue) s'étend à `issue` : `store` sur l'état après `split`.
  - Les hypothèses retirées restent retirées : `DDSound` en R1, `ReprC` en R4′.
- **Jalon 3** : les décisions 1 à 9 de § A.5. La décision 2 (réindexation des clauses d'ancêtre des opérations d'arène) est à arbitrer (P1).

## B.5 Lemmes de la Spec 1 copiés ou à généraliser

**Jalon 1.** La table de `spec2-m1-close.md` § B.5 est inchangée : copies dans `Preservation.lean` et `corr_leaf'`. Restent à remonter dans la Spec 1 :

- les lemmes d'arbre de `SyncInit.lean` ;
- les congruences par appartenance de `Context.lean` ;
- `heldAnchored_mem_congr`.

**Jalon 2** (`Realize.lean`). Copies des preuves de `Refinement.lean`, chacune avec les seules clauses lues :

| Lemme | Origine | Clauses lues |
|---|---|---|
| `realize_transfer` (`:49`) | `r6_transfer` | §63.1, §63.2, §63.3 |
| `realize_store` (`:92`) | `r6_store` | §65.2 |
| `realize_enter` (`:119`) | `r6_enter` | §72.2 |
| `realize_exit` (`:142`) | `r6_exit` | pile non vide |

**Jalon 3** :

| Lemme | Origine | Nature |
|---|---|---|
| `akeep_enter` (`ArenaPreserve:35`) | cas `enter` d'`Arena.kstep_akeep` | copie ; ne lit que §72.1 |
| `akeep_transfer` (`ArenaPreserve:54`) | cas `transfer` d'`Arena.kstep_akeep` | copie ; ne lit aucune précondition |
| `lInv_keep` (`ArenaPreserve:226`) | `Arena.lInv_kernel` | preuve reprise ; ne lit du pas que `AKeep` et les empreintes |
| `lInv_issue_core` (`ArenaPreserve:250`) | `Arena.lInv_issue` | preuve reprise ; ne lit que §77.1, §77.2, §77.5 et `issueKEff` |
| `pointer_sound_storeC` (`RealizeSound:38`) | `Refinement.pointer_sound_store` | preuve reprise ; §65.1, §65.2 |
| `exit_keeps_pinned` (`RealizeSound:179`) | cas `exit` de `Refinement.pinned_address_stable` | preuve reprise ; §73.1, §73.3 |

Lemmes nouveaux, indépendants du concurrent, à remonter dans la Spec 1 :

- `akeep_of_A`, `akeep_yield`, `lInv_congrF` (`ArenaPreserve.lean`) ;
- `resetD_F` (`ArenaConservativity.lean`).

Les copies s'expliquent par la forme des énoncés de la Spec 1. `Arena.kstep_akeep`, `Arena.lInv_issue` et `Refinement.pointer_sound_store` prennent l'`OpStep`, l'`IssueD` ou le `StoreStep` séquentiels, dont les préconditions lisent `ancestor`. Un énoncé paramétré par les seules clauses lues éviterait toutes les copies du jalon.

## B.6 Obligations OB-C01 à OB-C16 : état final

| OB | État après le jalon 3 |
|---|---|
| OB-C01 événements, exécutions permises | ouverte ; rien de formalisé |
| OB-C02 conflits, synchronizes-with, happens-before | ouverte |
| OB-C03 atomiques, ordres mémoire | ouverte. `crossContextConflictOnlyShared_witness` en montre la surface : un `writeShared(lock)` et un `read3(lock)` de deux contextes sont habilités simultanément. |
| OB-C04 `LockOrder` | ouverte ; S6 hors fragment, aucune trace |
| OB-C05 réalisation atomique d'`acquire`, `unlock`, `resetLock` | ouverte. Réalisations vides (jalon 2). S5b et S12 sont `ok` noyau et admis par `Encap` ; C22.4 n'est pas représentée. |
| OB-C06 absence de courses | ouverte. **Réduction** citée ci-dessous. |
| OB-C07 typage de la transférabilité | ouverte |
| OB-C08 encapsulation | C22.1–C22.3 et C22.5 formalisées par `Encap` et `EncapsulatedTrace`, T4 sous elles. Témoins de nécessité : C22.1 (`acquire_blocked_by_derive`), C22.2 (`W_C22_2_encap`), C22.3 (a) et (c) (S16), C22.3 (b) (`W_C22_3b_encap`, jumeau `W_C22_3b_ok`), C22.5 (S17a, S17b). C22.4 n'est pas représentée. L'application par les Specs 4 et 10 reste ouverte. |
| OB-C09 conventions par valeur, annulation | composite provisoire formalisé et réalisé ; annulation et terminaison anormale ouvertes |
| OB-C10 contextes externes | ouverte |
| OB-C11 ordre de `join` et de la complétion | issues de `join` formalisées ; l'ordre des événements reste ouvert |
| OB-C12 correspondance concrète (§82) | sur le fragment des pas abstraits : §82.1 (`ReprC`) ; §82.2–§82.5 (R1, R2) ; §82.3 adresse et provenance (`pointer_sound_storeC`, `issue_pointer_soundC`) ; §82.6 (`pinned_address_stableC`) ; §82.7, partiel : les opérations d'arène se réalisent par leurs pas noyau (R1, `r5_arena`) ; **non couverts** en concurrent : l'absence d'accès après invalidation (`RefinementArena.arena_realized` n'est pas transporté) et la partie « métadonnées » de §82.7, que `arena_realized` ne couvre pas non plus en séquentiel (lecture déclarée dans sa docstring) et dont `realize` hérite ; §82.8 (R4′). |
| OB-C13 H1 sous reparentage | T3 prouvé |
| OB-C14 composite par valeur | T2, T4, R1 pour le composite ; S4 positif, S4 négatif |
| OB-C15 contrat de `SyncAuthorized` | `SyncSound`, `libKC_sound`, T5 et sa nécessité d'I1 |
| OB-C16 garde unifiée | **intégrée** (A3). `newMutex` lit les `internal` vivants, `newArena` les `guarded` vivants. `AdminSep` est préservé (`lstep_adminSep`) et nécessaire à T4 (`adminSep_needed`). L'unicité intra-registre des arènes n'est pas énoncée. `HandlePool` et `DataStack` n'existent pas dans le modèle concurrent. |

**Réduction d'OB-C06** (`corpus-spec2-m3.md` §3, citée mot pour mot) :

> Une fois la data race définie en C/D (OB-C01, OB-C02), son absence devra se déduire de : R4, `CrossContextConflictOnlyShared`, la discipline des feuilles `SharedMutable` (OB-C03, OB-C05), et la réalisation des ordres d'autorité par `happens-before` (OB-C04, OB-C11). Ce n'est pas une équivalence formelle : la définition et les ordres appartiennent à C/D

Ce plan de preuve est consigné ; il n'est pas formalisé.

## B.7 Audit final des axiomes

- **Méthode.** Script `collectAxioms` sur toutes les constantes `thmInfo` dont le nom commence par `Ern.Concurrency` ou `_private.Ern.Concurrency`, après `import Ern`.
- **Résultat à `8e2bccf`.** 1092 théorèmes, dont 835 non internes. Aucun axiome hors `{propext, Quot.sound}`.
- **Évolution.** Jalon 1 : 798 (626) ; jalon 2 : 873 (675) ; jalon 3 : 1092 (835).
- **Théorèmes réutilisés d'`Arena.lean` et de `RefinementArena.lean`.** Audités en § A.1 : tous propres.
- **Absences.** Le `grep` d'`AGENTS.md` est vide sur le dépôt. Aucun `noncomputable` dans `formal/Ern/Concurrency/`. Le corpus n'utilise aucun `example`.

## Ce qui n'est pas vérifié

- P1, P2, P3 et P8 attendent un arbitrage.
- Les numéros de ligne ont été relevés à `8e2bccf` et contrôlés par script. Ceux des tables des jalons 1 et 2 citées par renvoi se rapportent à leurs propres commits.
- Aucun `SimRunC` concret ne contient de pas `issue` : les hypothèses d'`issue_pointer_soundC` ne sont pas montrées satisfaites ensemble sur une exécution.
- L'unicité des `internal` vivants à l'intérieur du registre d'arènes n'est pas énoncée en concurrent.
