# Spec 2, jalon 4, première passe — passation d'autorité

Branche `formal/spec2-m4`, créée depuis `b4d18ce` (tête de `formal/spec2-m3` après les commits de clôture). Exploratoire, jamais mergée ; rien n'est poussé, aucune PR.

- **Sources :**
  - `ERN_Concurrency_Model_WC5.md`, candidate non normative ; lus : C16–C18, C22, C43–C46, partie IV, partie VI (jalon 4) ;
  - `corpus-spec2-m3.md` v4, verdicts de référence, lu en entier ;
  - Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md` ; lus : §40, §42–§45, §49–§50, §54, §57, §60–§75.
- **Fichiers non modifiés :** `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md`, `formal/Ern/MemoryModel/`.
- **Définitions existantes :** aucune n'est modifiée (`Encap`, `EncapsulatedTrace`, `SyncInv`, `GrantDiscipline`, `LStep`, `ArenaInvC`, `AdminSep` comprises). Tout est ajouté à côté ; `git diff b4d18ce` ne retire aucune ligne.
- **Périmètre :** machine d'autorités seule. Aucun événement, aucune relation `po`, `rf`, `mo`, `sw`, `hb`, aucun énoncé sur les courses.

Chemins relatifs à `formal/Ern/Concurrency/`. Numéros de ligne à `be8946a`, dernier commit de code.

## Résultats

| Énoncé | Statut |
|---|---|
| W-GR, 5 verdicts | tous obtenus |
| `cap_sound` | prouvé, sous `FramesC` (écart 1) |
| L1 pour `cap` | **réfuté** par W-GR, comme le brief l'attendait |
| `cap5_sound` | **réfuté** |
| `cap5_compat` (L2, état) | **prouvé** |
| `cap5_drop_own` (L1) | **prouvé** pour les 28 sortes d'étiquettes, sous `DDSound` (`cap5_drop_own`, `CapDrop:1332`) |
| `handoff_loss_exists` (L2, trace) | **réfuté** |
| S10b | verdicts obtenus ; échouent `anchorOrderHeld` (§63.7) et `anchorOrder` (§63.6) |
| correction de `GuardedExcl` (`ChainExcl`), testée | sous `Encap5C`, `cap5_sound` et `handoff_loss_exists` sont **prouvés** (`cap5_sound_C`, `Encap5C:276` ; `handoff_loss_exists_C`, `:336`) |

Les deux réfutations ont la même cause : `GuardedExcl` ne porte que sur l'argument d'autorité du pas, alors que la troisième clause de Spec 1 §43 est récursive le long de la chaîne des détenteurs (§ Tâche 4). L1 et la forme d'état de L2 tiennent ; c'est `cap5_sound` qui manque pour en tirer la forme de trace. La correction testée, qui interdit un `guarded` vivant sur la chaîne des détenteurs, rétablit `cap5_sound` et, avec lui, la forme de trace de L2.

## Commits

| Commit | Tâche |
|---|---|
| `a1cfadb` | 1 — témoin W-GR |
| `18a0756` | 2 — `Attr`, `cap`, `cap_sound`, tables de `cap`, contre-exemple L1 pour `cap` |
| `eac4b11` | 3 — `GuardedExcl`, `CtlExcl`, `Encap5`, `Attr5`, `cap5`, témoins, tables de `cap5` |
| `fbc1898`, `2f5b6bc` | 4 — `cap5_compat` ; réfutations de `cap5_sound` et `handoff_loss_exists` ; retrait d'un `Classical.choice` |
| `73b73cd`, `37f4267`, `bd77fa6` | 4 — L1 sur `cap5`, étiquette par étiquette |
| `66d2d4e` | 5 — S10b |
| `50c34fc` | ce rapport, première version |
| `ec2106b` | 4 — L1 sur des traces existantes, étiquettes sans preuve (indice) |
| `8c2d454` | corrections du rapport |
| `281025e` | 4 — L1 : `split`, `alloc`, `enterFrame`, `spawn`, `issue`, `reset` |
| `c6a9b3c` | 4 — L1 : `exitFrame`, `terminate` |
| `6b21df1`, `ad45185` | 4 — L1 : `endUse`, `free` |
| `882ba6e` | 4 — L1 : `spawnVal` ; `cap5_drop_own` sur toutes les étiquettes |
| `4908b35` | ce rapport, mis à jour |
| `6987941` | portée de L1, docstring de `L1Evidence` |
| `6eb93c2` | test de la correction : `Exer5`, `ChainExcl`, `Encap5C`, `cap5_sound_C`, `handoff_loss_exists_C` |
| `be8946a` | témoins de la correction |
| commit suivant | ce rapport, mis à jour |

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
| W-HO, `left` ; `right` identique (`w_ho_cap`, `:26`) | `t0` M — ; `t1` M — ; `t2` — M ; `h1` — M ; `h2` M — ; `h3` M — | `c0` au `spawn` (son pas) ; `c1` à `release(a)` (son pas) |
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

## Tâche 4 — L1 et L2 sur `cap5` (`CapPreserve.lean`, `CapDrop.lean`)

Énoncés en `Prop` (`CapPreserve`) :

- `Cap5Sound` (`CapPreserve:55`), `Cap5DropOwn` (`:70`), `HandoffLossExists` (`:81`) ;
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

### `cap5_drop_own` (L1) — prouvé

`cap5_drop_own : DDSound k → Cap5DropOwn k L` (`CapDrop:1332`). Sous `DDSound`, depuis tout état atteint par une `EncapsulatedTrace5` depuis un état initial, un pas admis par `Encap5` qui fait baisser strictement `cap5` d'un contexte `c` sur une feuille est un pas de `c`. La preuve est une analyse par étiquette ; aucun contre-exemple.

**Lemmes de transport.** `cap5` de `c` ne baisse pas si, du premier état au second :

- les frames de `c` restent vivantes ;
- les empreintes des places existantes ne grandissent pas ;
- chaque autorité attribuable à `c` garde activité, mode propre, détenteur et `NotGuarded`, ainsi qu'un mode effectif suffisant.

Deux versions :

- `cap5_transport` (`CapPreserve:320`) exige ces conditions pour toute autorité attribuable ;
- `cap5_transport_u` (`CapDrop:65`) ne les exige que pour les autorités utiles (`Useful`, `CapDrop:23` : un mode effectif suffisant sur au moins une feuille). Elle sert à `free` : une racine de l'unité libérée peut être attribuable à un autre contexte sans y avoir aucun mode effectif, et `free` la désactive (`above_root_ground`, `CapDrop:932`).

| Étiquette | Argument | Théorème |
|---|---|---|
| `read3`, `write3`, `writeShared`, `depend`, `pin`, `unpin`, `join`, `resetLock`, `newArena` | ni `A`, ni `P`, ni contextes, ni identités `guarded` ne changent | `cap5_drop_own_inert` (`CapPreserve:421`) |
| `derive` | seuls la source et ses ancêtres perdent du mode effectif ; `attr_compat` et `I1` | `cap5_drop_own_derive` (`:520`) |
| `store` | l'autorité stockée est tenue par la frame courante de l'acteur (§65.1) | `cap5_drop_own_store` (`:645`) |
| `transfer` | les détenteurs déplacés sont des parties de la source, sur laquelle l'acteur a `Modify` (§63.1) ; squelettes et empreintes gardés | `cap5_drop_own_transfer` (`:686`) |
| `acquire` | le grant descend du `guarded` vivant, non attribuable ; les ancêtres de `guarded` n'ont pas de mode effectif | `cap5_drop_own_acquire` (`:775`) |
| `deriveSync` brut | aucun pas admis par `Encap5` (C14, C22.2) | `cap5_drop_own_deriveSync` (`:824`) |
| `release` | l'autorité libérée n'est attribuable qu'à l'acteur (§62.2) ; les modes effectifs ne peuvent que monter | `cap5_drop_own_release` (`:948`) |
| `unlock` | comme `release` (C17.2, C17.3) | `cap5_drop_own_unlock` (`:970`) |
| `newMutex` | le nouveau `guarded` n'est attribuable qu'à l'acteur (C13.2, `attr_excl`) | `cap5_drop_own_newMutex` (`:1002`) |
| `split` | comme `derive`, une région à la fois (§61.1) | `cap5_drop_own_split` (`CapDrop:411`) |
| `alloc` | la nouvelle racine n'a pas d'origine ; empreintes anciennes gardées | `cap5_drop_own_alloc` (`:432`) |
| `enterFrame` | idem ; les paramètres sont tenus par la frame courante de l'acteur (§72.1) | `cap5_drop_own_enter` (`:451`) |
| `spawn` | idem ; le nouveau contexte n'avait pas de `cap5` avant le pas | `cap5_drop_own_spawn` (`:474`) |
| `issue` | `split` puis `store`, invariants entre les phases par T2 | `cap5_drop_own_issue` (`:505`) |
| `reset` | `derive` puis `release`, invariants entre les phases par T2 | `cap5_drop_own_reset` (`:537`) |
| `exitFrame`, `terminate` | le réancrage ne garde que d'anciens ancêtres (`exit_ancs_sub`, `:577`) ; les autorités utiles des autres contextes survivent, par `NoDangling` après le pas (`exit_survives`, `:648`) | `cap5_drop_own_exit` (`:740`), `cap5_drop_own_terminate` (`:762`) |
| `endUse` | le pas ne fait que libérer (`releases_cap5_mono`, `:802`) ; les autorités utiles des autres contextes restent actives (`endUse_keeps`, `:830`) | `cap5_drop_own_endUse` (`:878`) |
| `free` | idem, et aucune autorité utile d'un autre contexte ne couvre l'unité libérée : grounding (`attr_excl`), au-dessus du grounding (`above_root_ground`), §70.3, ou racine tenue par le propriétaire de sa place racine et `I1` (`free_keeps`, `:968`) | `cap5_drop_own_free` (`:1097`) |
| `spawnVal` | `spawn` avec paramètres puis les transferts (`create_yield`, `yield_transfers`) ; à chaque phase, le grounding est attribuable au créateur ou au nouveau contexte (`attr_yield`, `:1140`), `KBase` étant porté comme dans `transfers_base` (`transfers_cap5_mono`, `:1206`) | `cap5_drop_own_spawnVal` (`:1255`) |

**Vérification indépendante.** `no_other_drops` (`Corpus/L1Evidence:32`), antérieur à la preuve, évalue par `decide` 15 pas de traces existantes du corpus : aucune baisse pour un autre contexte que l'acteur.

**Non-vacuité.** Sur `cycle_trace5` (`Corpus/Encap5Witness:43`), une `EncapsulatedTrace5` depuis l'état initial, `cap5` du contexte 0 sur `T` passe de `Modify` à `none` à son propre `newMutex` (`w_gr_cap5`, `Corpus/CapValues:103`).

**Ce que les preuves utilisent.** Les preuves de `cap5_compat` et de `cap5_drop_own` ne lisent la trace qu'au travers de `encapsulatedTrace5_imp`. Elles ne lisent l'hypothèse `Encap5` du pas qu'une fois, sous la forme `Encap` (C22.2), pour le `deriveSync` brut. `GuardedExcl` et `CtlExcl` n'y jouent aucun rôle : L1 et la forme d'état de L2 sur `cap5` tiennent déjà sur `EncapsulatedTrace`. Le test de `GuardedExcl` se résume donc ainsi : `GuardedExcl` ne donne pas `cap5_sound`.

**Portée.** L1 est prouvé pour `cap5`, qui sous-estime ce qu'un contexte peut exercer : `cap5` ignore les chaînes qui passent par `guarded`. Sur la trace du contre-exemple, `cap` du contexte 1 sur `Y` passe de `Observe` (`gc_cap5_none`) à `none` au pas `acquire` du contexte 0 (évaluation par `#eval` de `cap gc8 1 4`). `OB-C17` n'est donc pas acquis pour les accès réels sous `Encap5` ; sous `Encap5C`, `cap5_sound` tient et les accès admis sont vus par `cap5` (§ Test de la correction).

### `handoff_loss_exists` — réfuté

`handoff_loss_exists_false : ¬ ∀ k L, DDSound k → HandoffLossExists k L` (`Corpus/GuardedChain:112`).

- **Trace :** la trace précédente, prolongée de `c0 : acquire(e)` et de `c0 : write3(Y)` via `z` (exerçable en `Modify` au travers du grant). L'ensemble est une `EncapsulatedTrace5` (`gc_trace`, `:91`).
- **Paire d'accès :** `c1` accède à `Y` au pas 7 (`read3`) ; `c0` y accède au pas 9 en exigeant `Modify`.
- **Pourquoi l'énoncé tombe :** le seul pas intermédiaire, 8 (`acquire`), est un pas de `c0`. Aucun pas de `c1` ne baisse son `cap5` sur `Y` ; il valait déjà `none` au moment de la lecture.
- **Ce qui manque :** `cap5_sound`. Avec lui, `cap5_compat`, `cap5_drop_own` et l'invariance de `cap5` par un pas d'accès (`inert_effect`), `handoff_loss_exists` se déduit ; la déduction est formalisée sous `Encap5C` (`handoff_loss_exists_C`, ci-dessous).

### Test de la correction (`Encap5C.lean`, `Corpus/GuardedChainC.lean`)

La correction est une proposition de ce rapport, absente de WC5 et du brief ; elle est testée à côté des définitions du brief, qui restent inchangées.

- **`Exer5`** (`Encap5C:24`) : `ExercisableAt` de Spec 1 §43 lu depuis la frame courante du contexte, par une chaîne de détenteurs dont aucune autorité n'est le `guarded` d'une entrée vivante. Décidable (`exer5_iff`, `:108`).
- **`ChainExcl`** (`:142`) : l'argument d'autorité de `derive`, `split`, `read`, `write` et `writeShared` vérifie `Exer5` dans le mode que demande la précondition. Comme `ExercisableAt` est existentiel, c'est exactement « aucun exercice possible de l'argument n'évite un `guarded` vivant ».
- **`Encap5C`** (`:155`) : `Encap ∧ ChainExcl ∧ CtlExcl` ; `EncapsulatedTrace5C` (`:169`), `Run5C` (`:195`).
- **Inclusion :** `ChainExcl` entraîne `GuardedExcl` (`chainExcl_guardedExcl`, `:159`), donc toute `EncapsulatedTrace5C` est une `EncapsulatedTrace5` (`encapsulatedTrace5C_imp`, `:178`). `cap5_compat` et `cap5_drop_own` s'y appliquent sans nouvelle preuve.

| Énoncé | Statut sous `Encap5C` | Théorème |
|---|---|---|
| `cap5_sound` (`Cap5SoundC`, `:214`) | **prouvé** : l'autorité d'accès est attribuable sans `guarded` vivant (`Exer5.attr5`, `:123`) | `cap5_sound_C` (`:276`) |
| `handoff_loss_exists` (`HandoffLossExistsC`, `:227`) | **prouvé** : `cap5_sound_C` à l'accès antérieur, `cap5_compat` à l'accès postérieur, invariance de `cap5` par le pas d'accès, puis `cap5_drop_own` au premier pas de baisse entre les deux (`exists_drop`, `:309`) | `handoff_loss_exists_C` (`:336`) |

**Témoins** (`Corpus/GuardedChainC.lean`), par `decide` :

- **Exclusions :** la lecture du contre-exemple (`gc_read_excluded`, `Corpus/GuardedChainC:22`) et le pas 1 de W-GR (`W_GR_1_excluded`, `:26`) sont exclus.
- **Le même accès, verrou tenu, est admis :** depuis l'état initial, la mise en place, puis `c1 : acquire(e)`, `c1 : read3(Y)` via `z`, `c1 : unlock(e)`, `c0 : acquire(e)`, `c0 : write3(Y)` via `z`, forment une `EncapsulatedTrace5C` (`lc_trace`, `:49`).
- **Le marqueur de perte :** sur cette trace, `cap5` du contexte 1 sur `Y` vaut `Modify` de son `acquire` à son `unlock`, puis `none` (`lc_cap5`, `:75`). Le marqueur que donne `handoff_loss_exists_C` est donc l'`unlock` du contexte 1, un pas du contexte 1.

**Portée de la correction.**

- `ChainExcl` ne porte que sur les cinq opérations dont un argument est exercé. Les opérations dont le droit est `HasRight` (`transfer`, `depend`, `store`, `endUse`, `free`, `pin`, `unpin`, `alloc`, et le droit sur le détenteur de `release`) peuvent encore reposer sur une chaîne qui passe par `guarded`. Exercer `guarded` en `Modify` demande d'avoir `Modify` sur `slot`, donc un mutex non partagé. Ces opérations n'accèdent à aucune donnée et n'entrent ni dans `cap5_sound` ni dans L2. Cette restriction n'est pas testée au-delà.
- Aucune trace des modules existants n'a été rejouée sous `Encap5C`, hormis `lc_trace` et les deux exclusions.

## Tâche 5 — S10b (`Corpus/S10b.lean`, corpus v4 § 2 quater)

Le module n'importe que `Ern.MemoryModel.Access.Main`. Contrat `Examples.K0`.

| Pas | Attendu | Obtenu | Clause | Théorème (`Corpus/S10b`) |
|---|---|---|---|---|
| mise en place, dont `store(x, L)` | `ok` | `ok` | O1, O6, O10, O8 | `S10b_setup` (`:45`) |
| `transfer(L, D)` depuis `f1` | `reject` | `reject` ; champs faux : `anchorOrderHeld` (§63.7) et `anchorOrder` (§63.6) ; vrais : §63.1–§63.5, `depsValid` (§63.6), §63.8, §63.9 | §63.7, §63.6 | `S10b_1_reject` (`:54`) |
| jumeau `transfer(L, L2)` | `ok` | `ok` | §63.7, §63.8 | `S10b_2_ok` (`:74`) |

## Choix de représentation

Aucun ne change un programme accepté ni un verdict ; ils fixent la forme des énoncés.

- **`Run5`** : une trace dont les états sont nommés par une fonction `Nat → état`, reliée à `EncapsulatedTrace5` par `run5_of_trace`.
- **`Label.Access c l m`** : un pas `read3`, `write3` ou `writeShared` du contexte `c` dont la liste de feuilles contient `l`. `writeShared` compte comme un accès en `Observe` (§68.2).
- **`capRank`** : `none < Observe < Modify` ; « baisse » veut dire baisse stricte de ce rang.
- **`DDSound`** : supposé dans les preuves seulement ; les énoncés `Cap5Sound`, `Cap5DropOwn` et `HandoffLossExists` ne le contiennent pas, et les réfutations le prennent en hypothèse de la quantification.
- **`GuardedExcl`** contient aussi `derive` et `split`, déjà exclus par C22.1 dans `Encap` : ils satisfont le critère du brief (argument soumis à `ExercisableAt`).
- **`Label.ctx`** : le contexte exécutant ; pour `join c d`, c'est `c`.

## Lemmes du noyau à remonter ou à dédoublonner

`CapPreserve.lean` et `CapDrop.lean` contiennent des lemmes qui ne parlent que du noyau de la Spec 1. Ils sont signalés ici et non déplacés, pour ne pas décaler les numéros de ligne.

- **Doublons de lemmes existants :**
  - `auth_compat` (`CapPreserve:157`) duplique `effective_exclusive` (`MemoryModel/Access/Lemmas.lean:358`) ;
  - `mem_descModes` (`CapPreserve:148`) est un sens de l'équivalence `mem_descModes` existante (`Lemmas:254`) ;
  - `eff_modify` et `eff_present` (`CapPreserve:118`, `:135`) recoupent `effective_some` et `effOf_cases` ;
  - `footprint_ne` (`CapPreserve:94`) duplique `exists_mem_footprint` (`Lemmas:838`) ;
  - `parents_lt` (`CapDrop:26`) reprend un calcul déjà fait dans plusieurs preuves.
- **Lemmes nouveaux à remonter dans la Spec 1 :**
  - de `CapPreserve` : `effective_of_A`, `exer_mode`, `allows_effOf_obs`, `allows_effOf_sub`, `addModify_keep`, `release_org`, `release_eff_mono`, `store_skel`, `storeEff_P` ;
  - de `CapDrop` : `eff_keep_sub`, `no_eff_below_modify`, `split_get`, `exit_ancs_sub`, `ownedIn_up`, `above_root_ground`.

## Écarts

1. **`cap_sound` suppose `FramesC s`.** La frame courante d'un contexte est la tête de sa pile. Si un contexte vivant avait une pile vide, le sommet de sa vue serait la frame d'un autre contexte, et l'énoncé tomberait. `FramesC.nonempty` (WC4 C3) exclut ce cas ; `cap_sound` est donc énoncé sous `FramesC`, qui tient sur les états atteints (T2).
2. **Baisses de `cap` absentes de la table du brief.** Il y en a trois, toutes des pas du contexte qui baisse :
   - W-HO″ : `c0` à son `spawn` et `c1` à son `spawn` ;
   - W-GR : `c0` à `derive(root_M, Observe)`.
3. **`GuardedExcl` et la récursivité de §43.** `GuardedExcl` laisse passer l'exercice de `guarded` comme maillon intermédiaire d'une chaîne de détenteurs. C'est la cause des deux réfutations (tâche 4) ; la correction proposée est testée à côté (§ Test de la correction), sans modifier `GuardedExcl`.
4. **`Attr5` coupe les chaînes qui passent par `guarded`.** C'est la lecture littérale de « n'est attribuable à aucun contexte » ; elle est consignée ici.
5. **S10b : pas de mise en place ajouté.** Spec 1 §72 crée les locaux `Uninit`. Pour obtenir `X` `Init` comme le dit le corpus, la mise en place ajoute `write3(X)` via `root_X` (O10). Ce pas ne joue sur aucun verdict.
6. **`CtlExcl` exclut tout `writeShared` brut sur le contrôleur.** Dans le modèle, les opérations de protocole d'`acquire`, `unlock` et `resetLock` n'ont pas de réalisation brute, donc aucun `writeShared` brut n'est « dans le protocole » (WC5 C22.4).
7. **Réfutations prises sur un contrat de test.** Elles portent sur l'énoncé quantifié sur tout contrat `DDSound`, et sont obtenues sur `KM`.
8. **`cap5_drop_own` suppose `DDSound`** (Spec 1 §80), comme tous les invariants de trace (T2–T7) dont il se sert ; l'énoncé `Cap5DropOwn` ne le contient pas.
9. **Sources citées dans les docstrings.** Le brief demande de citer WC5, la Spec 1 ou le corpus v4. Les définitions propres au brief (`GuardedExcl`, `Encap5`, `Attr5`, `cap5`, les énoncés de la tâche 4) citent « the brief of milestone 4 », seule source exacte.

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat à `be8946a`.** 1458 théorèmes, dont 1079 non internes, contre 1144 (886) à la clôture du jalon 3. Aucun axiome hors `{propext, Quot.sound}`, `cap5_drop_own`, `cap5_sound_C` et `handoff_loss_exists_C` compris.
- **Modules nouveaux**, théorèmes (non internes) :
  - `Cap` : 9 (8) ;
  - `Encap5` : 39 (10) ;
  - `CapPreserve` : 90 (59) ;
  - `Corpus.GuardedRead` : 5 (5) ;
  - `Corpus.CapValues` : 7 (7) ;
  - `Corpus.Encap5Witness` : 4 (4) ;
  - `Corpus.GuardedChain` : 8 (7) ;
  - `Corpus.S10b` : 4 (4) ;
  - `Corpus.L1Evidence` : 1 (1) ;
  - `CapDrop` : 58 (46) ;
  - `Encap5C` : 85 (38) ;
  - `Corpus.GuardedChainC` : 4 (4).
- **`Classical.choice` retiré.** Un `omega` fermant un but existentiel l'avait introduit dans `footprint_ne` ; corrigé en `2f5b6bc`.
- **Build.** `lake build` réussit (81 jobs). Les douze modules nouveaux, recompilés seuls par `lake env lean`, ne produisent aucune sortie.
- **Contrôles.**
  - Le `grep` d'`AGENTS.md` est vide.
  - Aucun `noncomputable`, `decide +kernel` ni `ofReduceBool` dans `formal/Ern/Concurrency/`.
  - `git diff b4d18ce` ne retire aucune ligne et ne touche aucun fichier protégé.
  - Aucune ligne ajoutée ne dépasse 100 caractères.
