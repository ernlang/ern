# Spec 2, jalon 4, première passe — passation d'autorité

Branche `formal/spec2-m4`, créée depuis `b4d18ce` (tête de `formal/spec2-m3` après les commits de clôture). Exploratoire, jamais mergée ; rien n'est poussé, aucune PR.

- **Sources :**
  - `ERN_Concurrency_Model_WC5.md`, candidate non normative ; lus : C16–C18, C22, C43–C46, partie IV, partie VI (jalon 4) ;
  - `corpus-spec2-m3.md` v4, verdicts de référence, lu en entier ;
  - Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md` ; lus : §42–§45, §60–§75.
- **Fichiers non modifiés :** `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md`, `formal/Ern/MemoryModel/`.
- **Définitions existantes :** aucune n'est modifiée (`Encap`, `EncapsulatedTrace`, `SyncInv`, `GrantDiscipline`, `LStep`, `ArenaInvC`, `AdminSep` comprises). Tout est ajouté à côté ; `git diff b4d18ce` ne retire aucune ligne.
- **Périmètre :** machine d'autorités seule. Aucun événement, aucune relation `po`, `rf`, `mo`, `sw`, `hb`, aucun énoncé sur les courses.

Chemins relatifs à `formal/Ern/Concurrency/`. Numéros de ligne à `66d2d4e`, dernier commit de code.

## Résultats

| Énoncé | Statut |
|---|---|
| W-GR, 5 verdicts | tous obtenus |
| `cap_sound` | prouvé, sous `FramesC` (écart 1) |
| L1 pour `cap` | **réfuté** par W-GR, comme le brief l'attendait |
| `cap5_sound` | **réfuté** |
| `cap5_compat` (L2, état) | **prouvé** |
| `cap5_drop_own` (L1) | **inachevé** : prouvé pour 17 des 28 sortes d'étiquettes, non entrepris pour les 11 autres |
| `handoff_loss_exists` (L2, trace) | **réfuté** |
| S10b | verdicts obtenus ; échouent `anchorOrderHeld` (§63.7) et `anchorOrder` (§63.6) |

Les deux réfutations ont la même cause : `GuardedExcl` ne porte que sur l'argument d'autorité du pas, alors que la troisième clause de Spec 1 §43 est récursive le long de la chaîne des détenteurs (§ Tâche 4).

## Commits

| Commit | Tâche |
|---|---|
| `a1cfadb` | 1 — témoin W-GR |
| `18a0756` | 2 — `Attr`, `cap`, `cap_sound`, tables de `cap`, contre-exemple L1 pour `cap` |
| `eac4b11` | 3 — `GuardedExcl`, `CtlExcl`, `Encap5`, `Attr5`, `cap5`, témoins, tables de `cap5` |
| `fbc1898`, `2f5b6bc` | 4 — `cap5_compat` ; réfutations de `cap5_sound` et `handoff_loss_exists` ; retrait d'un `Classical.choice` |
| `73b73cd`, `37f4267`, `bd77fa6` | 4 — L1 sur `cap5`, étiquette par étiquette |
| `66d2d4e` | 5 — S10b |
| commit suivant | ce rapport |

## Tâche 1 — W-GR (`Corpus/GuardedRead.lean`, corpus v4 § 2 ter)

Depuis `MX₄` (`x4`, registre `regX`), contrat `KM`.

| Pas | Attendu | Obtenu | Clause | Théorème (`Corpus/GuardedRead`) |
|---|---|---|---|---|
| 1. `c1 : read3(T)`, `access = guarded` | `ok` | `ok` | O9.1 ; O9.2 par la 3ᵉ clause de §43 | `W_GR_1_ok` (`:26`) |
| 2. `c0 : acquire(e)` | `ok` | `ok` ; `g` (autorité 5) tenue par la frame 0 | C14.1–C14.3, C15 | `W_GR_2_ok` (`:30`) |
| 3. `c0 : write3(T)` via `g` | `ok` | `ok` | O10.1 | `W_GR_3_ok` (`:34`) |
| 4. négatif : `read3(T)` par `c1` pendant que `g` est active | `reject` | `reject` ; `effective(guarded, T) = none` | O9.2, §43.3 | `W_GR_4_reject` (`:40`) |
| 5. pas 1–3 depuis l'état initial | `EncapsulatedTrace` | vrai | C22, C23 | `w_gr_trace` (`:45`) |

## Tâche 2 — capacité de contexte (`Cap.lean`, WC5 C43)

- **`Attr s c x m`** (`Cap:22`) : `S3.ExercisableAt` de §43, inductif, avec « tenue par une frame vivante de `c` » (`f ∈ s.stk c`) à la place de « tenue par la frame courante ». La clause « tenue par une place » a la même forme. Décidabilité par `attr_iff` (`:35`) : une chaîne de détenteurs se termine en une seule autorité tenue par une frame, donc `Attr` est `ExercisableAt` lu depuis une frame de `c`.
- **`cap s c l`** (`Cap:64`) : le plus grand `m` tel que `CapAt s c l m` (`:55`), c'est-à-dire qu'une autorité attribuable à `c` en mode `m` ait un mode effectif permettant `m` sur `l`.
- **`cap_sound`** (`Cap:122`) : pour un pas `ok` de `read3`, `write3` ou `writeShared` de `c`, `Allows (cap s c l) m` sur chaque feuille accédée, `m` étant le mode requis. Hypothèse : `FramesC s` (écart 1).

**Valeurs de `cap`** (`Corpus/CapValues.lean`), une ligne par état, colonnes `c0`, `c1`, `c2` ; `M` = `Modify`, `O` = `Observe`, `—` = `none`.

| Témoin, feuille (théorème) | États et valeurs | Baisses : contexte, pas qui la cause |
|---|---|---|
| W-HO, `left` (`w_ho_cap`, `:26`) | `t0` M — ; `t1` M — ; `t2` — M ; `h1` — M ; `h2` M — ; `h3` M — | `c0` au `spawn` (son pas) ; `c1` à `release(a)` (son pas) |
| W-HO′, `X` (`w_ho2_cap`, `:34`) | `k0`…`k4` M — ; `k5`, `k6` — M | `c0` à `release(b)` (son pas) |
| W-HO″, `X` (`w_ho3_cap`, `:44`) | `k0`, `m1` M — — ; `m2`, `m3` — M — ; `m4`, `m5` — — M ; `m6` — M — ; `m7`, `m8`, `m9` M — — | `c0` à son `spawn` ; `c1` à son `spawn` ; `c2` à `release(a₂)` ; `c1` à `release(a)` — tous leurs propres pas |
| W-GR, `T` (`w_gr_cap`, `:56`) | `x0`, `x1`, `x2` M — ; `x3` O — ; `x4`, `gr1` O O ; `gr2`, `gr3` M — | `c0` à `derive(root_M, Observe)` (son pas) ; **`c1` à `acquire(e)`, pas de `c0`** |

- **Contre-exemple à L1 pour `cap`** : `cap_L1_counterexample` (`Corpus/CapValues:69`). Dans W-GR, sur une `EncapsulatedTrace` depuis l'état initial, le pas `acquire(e)` de `c0`, admis par `Encap`, fait passer `cap` de `c1` sur `T` de `Observe` à `none`.
- **Sans la lecture du pas 1**, la même baisse se produit depuis `MX₄` (état `gx`). La capacité de `c1` sur `T` repose sur `guarded`, tenue par `slot`, au travers de `o1`. Exclure la lecture ne rétablit donc pas L1 pour `cap` ; c'est ce qui motive `cap5`.

## Tâche 3 — encapsulation étendue (`Encap5.lean`)

- **`GuardedExcl`** (`Encap5:26`), proposition du brief absente de WC5. Pour toute entrée vivante, l'argument d'autorité du pas n'est pas `guarded`. Constructeurs de `KernelOp` retenus, ceux dont la précondition applique `ExercisableAt` à un argument :
  - `derive` (§60.1), `split` (§61.1) — déjà exclus par C22.1 dans `Encap` ;
  - `read` (§66.2), `write` (§67.1), `writeShared` (§68.2).
- **Constructeurs non retenus :**
  - `release` (§62.2 : condition sur le détenteur, pas `ExercisableAt` ; exclu par le brief) ;
  - `store` (§65.1 : tenue par la frame courante) ;
  - `depend` (§64.2 : autorité active).
  - Les autres (`transfer`, `enter`, `exit`, `pin`, `unpin`, `endUse`, `free`, `alloc`) n'ont pas d'argument d'autorité exercée.
- **`CtlExcl`** (`Encap5:38`), WC5 C22, exigence 4 : pas de `read3`, `write3` ni `writeShared` brut dont les feuilles contiennent `ControlOf(e)`.
- **`Encap5`** (`:49`), **`EncapsulatedTrace5`** (`:54`), **`encapsulatedTrace5_imp`** (`:63`) : toute `EncapsulatedTrace5` est une `EncapsulatedTrace`, et T2–T7 s'y appliquent sans nouvelle preuve.
- **`Attr5`** (`:91`), **`cap5`** (`:198`) : `NotGuarded` (`:82`) est exigé à chaque nœud de la chaîne. Une chaîne qui passe par `guarded` est donc coupée (lecture littérale de « n'est attribuable à aucun contexte »). Les grants restent attribuables. Décidabilité par itération bornée (`attr5_iff`, `:176`), sur le modèle d'`exR`.

**Témoins** (`Corpus/Encap5Witness.lean`), par `decide` :

| Témoin | Obtenu | Théorème |
|---|---|---|
| W-GR, pas 1 | `ok` noyau, admis par `Encap`, `¬ GuardedExcl` | `W_GR_1_guardedExcl` (`:20`) |
| S12, `write3(lock)` depuis `MX₃` | `ok` noyau, admis par `Encap`, `¬ CtlExcl` | `S12_1_ctlExcl` (`:27`) |
| `read3(lock)` via `o1` depuis `MX₄` | `ok` noyau, admis par `Encap`, `¬ CtlExcl` | `read_lock_ctlExcl` (`:35`) |
| non-vacuité : MX depuis `x0`, puis `acquire`, `write3(T)` via le grant, `unlock` | `EncapsulatedTrace5` | `cycle_trace5` (`:43`) |

**Valeurs de `cap5`** (`Corpus/CapValues.lean`) :

- **W-HO, W-HO′, W-HO″** : registres vides, donc `cap5 = cap` (`w_ho_cap5`, `:87`).
- **W-GR** (`w_gr_cap5`, `:103`), sur `T`, avec les registres ; `x2` figure avant et après `newMutex` :
  - `(x0, [])`, `(x1, [])`, `(x2, [])` : M — ;
  - de `(x2, regX)` à `(gr1, regX)` : — — ;
  - `(gr2, regG)`, `(gr3, regG)` : M —.
- **Baisses sur W-GR :** une seule, `c0` à son `newMutex`, car `guarded` cesse d'être attribuable. `c1` n'a de `cap5` sur `T` dans aucun état : la baisse de `cap` à `acquire(e)` disparaît.

## Tâche 4 — L1 et L2 sur `cap5` (`CapPreserve.lean`)

Énoncés en `Prop` (`CapPreserve`) :

- `Cap5Sound` (`:55`), `Cap5DropOwn` (`:70`), `HandoffLossExists` (`:81`) ;
- outils : `capRank` (`:20`), `Label.Access` (`:27`), `Run5` (`:35`, trace aux états nommés), `run5_of_trace` (`:41`).

Tous partent d'une `EncapsulatedTrace5` depuis un état initial `SC.ofS3 (S3.init statics)` avec `StaticsOK`. Les preuves supposent `DDSound`.

### `cap5_sound` — réfuté

`cap5_sound_false : ¬ ∀ k L, DDSound k → Cap5Sound k L` (`Corpus/GuardedChain:102`). Contrat `KM`, qui satisfait `DDSound` (`ddKC`).

**Contre-exemple minimal** (`Corpus/GuardedChain.lean`) :

- **Statiques :** bloc MX sans `M′`, plus un local `Y` de la frame de base, `Init` (`zst`, `:25`).
- **Trace** `gc_setup` (`:65`), chaque pas `ok` et admis par `Encap5` :
  1. `z := derive(root_Y, Modify)` ;
  2. `store(z, T)` ;
  3. `guarded := derive(root_T, Modify)` ;
  4. `store(guarded, slot)` ;
  5. `newMutex(guarded)` ;
  6. `o1 := derive(root_M, Observe)` ;
  7. `spawn c1` cédant `o1`.
- **Pas fautif :** `c1 : read3(Y)` via `z` est `ok` et admis par `Encap5` (`gc_read`, `:81`).
  - `z` est exerçable en `Observe` par la 3ᵉ clause de §43, le long de la chaîne `z` → `T` → `guarded` → `slot` → `o1`.
  - L'argument d'autorité est `z`, non `guarded`, donc `GuardedExcl` l'admet ; `Y` n'est pas le contrôleur, donc `CtlExcl` l'admet.
- **Valeurs à ce pas :** `cap5 gc6 greg 1 Y = none` et `cap gc6 1 Y = Observe` (`gc_cap5_none`, `:87`).

### `cap5_compat` — prouvé

`cap5_compat` (`CapPreserve:268`). Pour `c ≠ c'`, jamais `cap5 c l = Modify` avec `cap5 c' l ≠ none`.

- **Hypothèses utilisées :** `KInvC` par `encapsulated_inv`, d'où l'unicité des frames (`FramesC.nodup`), `I1` et `WF3`.
- **Clé :** `attr_compat` (`:188`), par induction sur la chaîne d'attribution.
  - Deux autorités distinctes : contradiction par `I1` (`auth_compat`, `:157`).
  - Même autorité tenue par une frame : unicité des frames.
  - Même autorité tenue par une place : récurrence sur une feuille de la place. Elle existe par `footprint_ne` (`:94`), lemme nouveau, car les parents précèdent les enfants (§49.2).
- **Portée :** `attr_compat` porte sur `Attr` ; la forme d'état de L2 vaut donc aussi pour `cap`.

### `cap5_drop_own` (L1) — inachevé

**Lemme de transport** : `cap5_transport` (`CapPreserve:320`), par `attr5_transport` (`:282`). `cap5` de `c` ne baisse pas si, du premier état au second :

- les frames de `c` restent vivantes ;
- les empreintes des places existantes sont inchangées ;
- chaque autorité attribuable à `c` garde activité, mode propre, détenteur et `NotGuarded`, ainsi qu'un mode effectif suffisant.

| Étiquette | Statut | Argument | Théorème (`CapPreserve`) |
|---|---|---|---|
| `read3`, `write3`, `writeShared`, `depend`, `pin`, `unpin`, `join`, `resetLock`, `newArena` | prouvé | ni `A`, ni `P`, ni contextes, ni identités `guarded` ne changent | `cap5_drop_own_inert` (`CapPreserve:421`) |
| `derive` | prouvé | seuls la source et ses ancêtres perdent du mode effectif ; `attr_compat` et `I1` | `cap5_drop_own_derive` (`:520`) |
| `store` | prouvé | l'autorité stockée est tenue par la frame courante de l'acteur (§65.1) | `cap5_drop_own_store` (`:645`) |
| `transfer` | prouvé | les détenteurs déplacés sont des parties de la source, sur lesquelles l'acteur a `Modify` (§63.1) ; squelettes et empreintes gardés | `cap5_drop_own_transfer` (`:686`) |
| `acquire` | prouvé | le grant descend du `guarded` vivant, non attribuable ; ses ancêtres n'ont pas de mode effectif | `cap5_drop_own_acquire` (`:775`) |
| `deriveSync` brut | prouvé | aucun pas admis par `Encap5` (C14, C22.2) | `cap5_drop_own_deriveSync` (`:824`) |
| `release` | prouvé | l'autorité libérée n'est attribuable qu'à l'acteur (§62.2) ; les modes effectifs ne peuvent que monter | `cap5_drop_own_release` (`:948`) |
| `unlock` | prouvé | comme `release` (C17.2, C17.3) | `cap5_drop_own_unlock` (`:970`) |
| `newMutex` | prouvé | le nouveau `guarded` n'est attribuable qu'à l'acteur (C13.2, `attr_excl`) | `cap5_drop_own_newMutex` (`:1002`) |
| `split`, `enterFrame`, `exitFrame`, `endUse`, `free`, `alloc`, `spawn`, `terminate`, `spawnVal`, `issue`, `reset` | **non entrepris** | voir ci-dessous | — |

**Pour les 11 étiquettes restantes**, l'état du but est le même : établir, pour `c ≠ lbl.ctx`, les cinq hypothèses de `cap5_transport` entre l'état de départ et l'état d'arrivée. Aucun contre-exemple n'a été trouvé, et aucune n'a résisté à une tentative : elles n'ont pas été tentées. Ce qui manque, par étiquette :

- **`split` :** comme `derive`, avec plusieurs régions (`splitEff_cons`).
- **`enterFrame`, `spawn`, `alloc` :**
  - les nouvelles racines n'ont pas d'origine, donc les modes effectifs des anciennes autorités sont inchangés ;
  - les empreintes des anciennes places sont gardées (`enter_footprint_old`) ;
  - les paramètres changent de détenteur entre frames de l'acteur.
- **`exitFrame`, `terminate` :**
  - il faut montrer que le réancrage (§73.4) ne fait que raccourcir les chaînes d'origine ;
  - il faut montrer que les autorités libérées, tenues par des places qui meurent, ne sont attribuables à aucun autre contexte, en lisant §73.2 dans `ExitPreC` et `TermPre`.
- **`endUse`, `free` :** même question pour les places possédées qui meurent (§69.2, §70.3).
- **`spawnVal`, `issue`, `reset` :** composites. Il faut des versions par état des lemmes ci-dessus et les invariants entre les phases (T2).

### `handoff_loss_exists` — réfuté

`handoff_loss_exists_false : ¬ ∀ k L, DDSound k → HandoffLossExists k L` (`Corpus/GuardedChain:112`).

- **Trace :** la trace précédente, prolongée de `c0 : acquire(e)` et de `c0 : write3(Y)` via `z` (exerçable en `Modify` au travers du grant). L'ensemble est une `EncapsulatedTrace5` (`gc_trace`, `:91`).
- **Paire d'accès :** `c1` accède à `Y` au pas 7 (`read3`) ; `c0` y accède au pas 9 en exigeant `Modify`.
- **Pourquoi l'énoncé tombe :** le seul pas intermédiaire, 8 (`acquire`), est un pas de `c0`. Aucun pas de `c1` ne baisse son `cap5` sur `Y` ; il valait déjà `none` au moment de la lecture.

**Correction proposée, non appliquée** (le brief interdit de toucher la définition) : étendre `GuardedExcl` à tout pas dont l'exercice, au sens de §43, passe par un `guarded` vivant dans la chaîne des détenteurs. Équivalent : exiger que l'autorité d'accès soit `Attr5`-exerçable depuis la frame courante. Avec cette extension, `cap5_sound` découlerait directement de la définition. À arbitrer.

## Tâche 5 — S10b (`Corpus/S10b.lean`, corpus v4 § 2 quater)

Le module n'importe que `Ern.MemoryModel.Access.Main`. Contrat `Examples.K0`.

| Pas | Attendu | Obtenu | Clause | Théorème (`Corpus/S10b`) |
|---|---|---|---|---|
| mise en place, dont `store(x, L)` | `ok` | `ok` | O1, O6, O10, O8 | `S10b_setup` (`:45`) |
| `transfer(L, D)` depuis `f1` | `reject` | `reject` ; champs faux : `anchorOrderHeld` (§63.7) et `anchorOrder` (§63.6) ; vrais : §63.1–§63.5, `depsValid` (§63.6), §63.8, §63.9 | §63.7, §63.6 | `S10b_1_reject` (`:54`) |
| jumeau `transfer(L, L2)` | `ok` | `ok` | §63.7, §63.8 | `S10b_2_ok` (`:74`) |

## Écarts

1. **`cap_sound` suppose `FramesC s`.** La frame courante d'un contexte est la tête de sa pile. Si un contexte vivant avait une pile vide, le sommet de sa vue serait la frame d'un autre contexte, et l'énoncé tomberait. `FramesC.nonempty` (WC4 C3) exclut ce cas ; `cap_sound` est donc énoncé sous `FramesC`, qui tient sur les états atteints (T2).
2. **Baisses de `cap` absentes de la table du brief.** Il y en a trois, toutes des pas du contexte qui baisse :
   - W-HO″ : `c0` à son `spawn` et `c1` à son `spawn` ;
   - W-GR : `c0` à `derive(root_M, Observe)`.
3. **`GuardedExcl` et la récursivité de §43.** `GuardedExcl` laisse passer l'exercice de `guarded` comme maillon intermédiaire d'une chaîne de détenteurs. C'est la cause des deux réfutations (tâche 4) ; correction proposée ci-dessus, non appliquée.
4. **`Attr5` coupe les chaînes qui passent par `guarded`.** C'est la lecture littérale de « n'est attribuable à aucun contexte » ; elle est consignée ici.
5. **S10b : pas de mise en place ajouté.** Spec 1 §72 crée les locaux `Uninit`. Pour obtenir `X` `Init` comme le dit le corpus, la mise en place ajoute `write3(X)` via `root_X` (O10). Ce pas ne joue sur aucun verdict.
6. **`CtlExcl` exclut tout `writeShared` brut sur le contrôleur.** Dans le modèle, les opérations de protocole d'`acquire`, `unlock` et `resetLock` n'ont pas de réalisation brute, donc aucun `writeShared` brut n'est « dans le protocole » (WC5 C22.4).
7. **Réfutations prises sur un contrat de test.** Elles portent sur l'énoncé quantifié sur tout contrat `DDSound`, et sont obtenues sur `KM`.

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat à `66d2d4e`.** 1310 théorèmes, dont 990 non internes, contre 1144 (886) à la clôture du jalon 3. Aucun axiome hors `{propext, Quot.sound}`.
- **Modules nouveaux**, théorèmes (non internes) :
  - `Cap` : 9 (8) ;
  - `Encap5` : 39 (10) ;
  - `CapPreserve` : 90 (59) ;
  - `Corpus.GuardedRead` : 5 (5) ;
  - `Corpus.CapValues` : 7 (7) ;
  - `Corpus.Encap5Witness` : 4 (4) ;
  - `Corpus.GuardedChain` : 8 (7) ;
  - `Corpus.S10b` : 4 (4).
- **`Classical.choice` retiré.** Un `omega` fermant un but existentiel l'avait introduit dans `footprint_ne` ; corrigé en `2f5b6bc`.
- **Build.** `lake build` réussit (77 jobs). Les huit modules nouveaux, recompilés seuls par `lake env lean`, ne produisent aucune sortie.
- **Contrôles.**
  - Le `grep` d'`AGENTS.md` est vide.
  - Aucun `noncomputable`, `decide +kernel` ni `ofReduceBool` dans `formal/Ern/Concurrency/`.
  - `git diff b4d18ce` ne retire aucune ligne et ne touche aucun fichier protégé.
  - Aucune ligne ajoutée ne dépasse 100 caractères.
