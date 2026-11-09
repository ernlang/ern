# Spec 2, jalon 2 — raffinement du modèle concurrent abstrait

Branche `formal/spec2-m2`, créée depuis `d77f7a6` (tête de `formal/spec2-m1`). Exploratoire, jamais mergée.

Sources :

- `ERN_WC4.md` (« WC4 corrigée », non commitée) ;
- Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md`.

**Fragment couvert.** Tous les énoncés de ce jalon portent sur un seul fragment : les contextes s'entrelacent **au grain des pas abstraits**. La réalisation d'un pas d'un contexte est une séquence de pas bruts de la machine mémoire. Elle s'exécute sans interférence des autres contextes.

Hors périmètre, par construction :

- les accès concurrents aux octets, l'atomicité physique, les ordres mémoire, `happens-before` et l'absence générale de data races (OB-C01 à OB-C06) ;
- la réalisation du mot de verrou (OB-C05).

Aucune région unsafe n'est modélisée. La décision de `DESIGN.md` sur la forme des contrats unsafe sous concurrence (« decided before milestone 4 ») n'est donc pas requise ici.

## Commits

| Commit | Contenu |
|---|---|
| `3c37877` | `Repr.lean` : `ReprC`, `repr_congr`, `repr_frames_congr`, `reprC_view` |
| `546822d` | `Realize.lean` : réalisations, `StepOblC`, R1 |
| `5b59e45` | `Realize.lean` : R5, `SimRunC`, R2, R3, témoin S4 |
| `ea57bf3` | `NonConflict.lean` : R4, R4′, témoin |
| `f79d405` | coupure des lignes de plus de 100 caractères |

Le rapport fait l'objet d'un commit séparé. Aucun fichier du jalon 1 n'est modifié : `git diff --stat d77f7a6` ne montre que `Ern.lean` (trois imports) et les trois nouveaux modules.

## Vérifications à `f79d405`

- `lake build` réussit (58 jobs), sans avertissement.
- Le `grep` d'`AGENTS.md` est vide ; aucun `noncomputable` dans `Ern/Concurrency`.
- Audit `collectAxioms` : 873 théorèmes `Ern.Concurrency*` (675 non internes), dont 75 dans les trois nouveaux modules (49 non internes). Aucun ne dépend d'un axiome hors `{propext, Quot.sound}`.

## Passages lus

- **Spec 1 :** Parties II–III (§§8–20) et XVII (§82) en entier, puis §§21–57 (dont §§39–45, 50, 54, 57 demandés), et §§58–75.
- **WC4 corrigée :** en entier. Comparée par `diff` à la WC4 de la passe précédente (texte reconstruit du transcript), elle ne diffère qu'en trois points :
  - C13 : « (former C13.10) » est retiré ;
  - dernier paragraphe de C22 : la phrase sur `EndUseExcl` « verified separately » est remplacée par un renvoi à C23 ;
  - S17a : le positif est reformulé (« `endUse(ctl)` is permitted by the encapsulation contract when O12's own preconditions hold »).

  Ces trois points répondent aux remarques X1–X3 du rapport `spec2-m1-close.md`.
- **Lean :** `Machine.lean`, `Refinement.lean` et `RefinementArena.lean` en entier ; `formal/DESIGN.md` en entier.

---

## 1. Audit des axiomes de `Refinement.lean`

Fait avant d'écrire du code, comme le demande le brief.

- **Tous les théorèmes `Ern.MemoryModel.Refinement*`** (`Refinement.lean` et `RefinementArena.lean`) : 436, aucun hors `{propext, Quot.sound}`.
- **Théorèmes de `Refinement.lean` réutilisés directement** par les nouveaux modules : 32, relevés par `getUsedConstantsAsSet` sur les déclarations des trois modules. Aucun ne dépend de `Classical.choice`.
  - `[]` : `AllocP.and`, `Dom.refl`, `exec_append`, `exec_of_along`, `run_append`.
  - `[propext]` : `LayoutWF.disjoint`, les projections `Repr.adm`, `Repr.init`, `Repr.inj`, `Repr.live`, `Repr.tokens`, et `along_append`, `copyOps_noDealloc`, `deallocOps_run`, `shapeP_get_lt`.
  - `[propext, Quot.sound]` : `Repr.leaf_live`, `Repr.transport`, `Runs.piOf_ok`, `copyOps_run`, `corr_leaf`, `corr_leaf_back`, `dom_run`, `leaf_of_leafOfUsable`, `live_run`, `mem_exitRoots`, `mem_transferPairs`, `r6`, `range_pairwise`, `repr_extend`, `repr_init`, `usable_old`, `writes_repr`.

Rien n'arrête donc le jalon à ce stade.

## 2. Définitions

| Définition | Module:ligne | Contenu | Source |
|---|---|---|---|
| `ReprC L rtok s m` | `Repr.lean:23` | `Repr L rtok s.flat m`, `Repr` étant celle de `Refinement.lean` | WC4 C2, C25 ; Spec 1 §82.1, §82.3–§82.5 |
| `kopOf` | `Realize.lean:218` | l'opération `Refinement.KOp` d'une `KernelOp`, avec les représentations `w` écrites par `write` et `writeShared` | Spec 1 §10 ¶4, §16 ¶2 |
| `valOps` | `Realize.lean:245` | les phases de transfert du composite : `transferOps` sur la vue du créateur, dans l'ordre déclaré, chaque phase sur l'état et la mémoire produits par les précédentes | WC4 C5.2 ; Spec 1 §63, §82.2, §82.3 |
| `realize π w lbl s m` | `Realize.lean:266` | réalisation de chaque étiquette de `LStep` (détail ci-dessous) | WC4 C2, C4–C8, C13–C18 ; Spec 1 §82.2–§82.5 |
| `StepOblC` | `Realize.lean:296` | obligations d'un pas : `Refinement.StepObl` sur la vue pour une opération héritée ; `OblAlong ∧ NewLayout` pour `spawn` et le composite ; `OblAlong` sinon | Spec 1 §20.3, §15, §16, §82.1, §82.4 |
| `SimRunC` | `Realize.lean:595` | exécutions traduites : état initial de `repr_init` pour `SC.ofS3 (S3.init statics)` et registre vide, puis chaque pas d'une `EncapsulatedTrace` sous `StepOblC`, suivi de sa réalisation ; paramètres fixés une fois | WC4 C22, C23 ; Spec 1 §20.3 ¶3, §82 |
| `NoUB` | `Realize.lean:636` | une opération brute n'a pas d'issue `ub` dans l'état où elle s'exécute | Spec 1 §20.1 ¶2 |
| `OrdinaryCrossContextNonConflict k s` | `NonConflict.lean:29` | énoncé de R4 (§ 3) | Spec 1 §43, §50, §54, §82.8 |

`realize`, étiquette par étiquette :

- **`.kernel c op` (O1–O16 exécutée par `c`) :** `opsOf π (kopOf op w) (s.view c) m`. C'est la réalisation de `Refinement.lean` appliquée à la vue de `c`.
- **`.spawn` :** `allocOps` des locaux racines d'O6. La cession des paramètres n'a pas d'effet mémoire.
- **`.spawnVal` :** concaténation de `allocOps` (création, C5.1) et de `valOps` (transferts, C5.2). La cession (C5.3) est vide.
- **`.terminate c` :** `exitOps` sur la vue de `c`, c'est-à-dire la réalisation d'O7. Le reparentage n'a pas d'effet mémoire.
- **`.join` et `.deriveSync` :** vide.
- **`.newMutex`, `.acquire`, `.unlock`, `.resetLock` :** vide ; registre seulement. La docstring de `realize` et le théorème `realize_sync` (`Realize.lean:284`) citent OB-C05.

Lemmes de `Repr.lean` :

- `repr_congr` (`:28`) : `Repr` ne lit que `P`, `I`, `dead` et la pile, celle-ci par appartenance.
- `repr_frames_congr` (`:38`) : `Repr` ne dépend pas de l'ordre des frames (Spec 1 §39, §9).
- `reprC_view` (`:46`) : `ReprC s m ↔ Repr (s.view c) m` pour tout `c`. `ReprC` ne dépend donc pas du contexte exécutant.
- `reprC_set` (`:52`), `reprC_ofS3` (`:57`).

**Contrôle du brief.** `Repr` dépend-il de `F` autrement que par appartenance ? Non. `Repr` lit `F` seulement à travers `S3.Usable`, dont la clause `frame` exige `f ∈ s.F` (`Access/Basic.lean:379`). La preuve de `repr_congr` passe par `Repr.transport` et `S3.Usable.mono`, sans autre hypothèse sur `F`.

## 3. Théorèmes R1–R5

Les cinq théorèmes sont prouvés. Aucun n'est réfuté, aucun ne reste ouvert. Le fragment est celui annoncé en tête.

### R1 — réalisation pas à pas : prouvé

`r1_lstep` (`Realize.lean:470`) :

```
(hπ : Refinement.ParamsOK C π) (hR : ReprC π.L π.rtok st.1 m) (hk : KInvCA st.1)
(h : LStep k L lbl st st') (hob : StepOblC k C ObR ObW π w lbl st.1 m) :
Machine.Exec C ObR ObW (realize π w lbl st.1 m) m (run m (realize π w lbl st.1 m)) ∧
  ReprC π.L π.rtok st'.1 (run m (realize π w lbl st.1 m))
```

Hypothèses :

- **`LayoutWF` :** c'est le champ `layout` de `ReprC`. La disposition des places nouvelles (`NewLayout`) est une obligation de `StepOblC`.
- **`KInvCA st.1` :** la preuve en utilise `FramesC`, `WF3` et `NoDangling` de la vue. Pour le composite, elle utilise aussi `KInvCA` en entier, via `spawn_base` du jalon 1.
- **`DDSound k` est absent :** la preuve ne l'utilise pas. L'énoncé est donc plus fort que celui du brief. `DDSound` sert en R2, pour propager `KInvCA` le long de la trace (`lstep_kInvCA`, à cause de `split`).

Preuve par étiquette :

- **Opérations héritées lues sur la vue** (`derive`, `split`, `release`, `read`, `write`, `writeShared`, `pin`, `unpin`, `endUse`, `free`, `alloc`) : `Refinement.r6` sur `s.view c`, puis transport (`r1_viewStep`, `:326`).
- **Opérations héritées à préconditions réindexées sur `ancestorC`** (`transfer`, `depend`, `store`, `enterFrame`, `exitFrameC`) : `Refinement.r6_*` demande l'`OpStep` de la Spec 1 sur `S3`. Sa précondition n'est pas disponible : par exemple, §63.6 lit `ancestor` sur la pile de la vue, et non `ancestorC`. Les lemmes `realize_transfer`, `realize_store`, `realize_enter` et `realize_exit` (`:49`, `:92`, `:119`, `:142`) reprennent donc les preuves de `r6_transfer`, `r6_store`, `r6_enter` et `r6_exit`, avec pour hypothèses les seules clauses que ces preuves lisent :
  - `transfer` : §63.1 (usabilité), §63.2, §63.3 (feuilles source `Init`) ;
  - `store` : §65.2 ;
  - `enterFrame` : §72.2 ;
  - `exitFrameC` : une pile non vide.

  Aucun énoncé de `Refinement.lean` n'est modifié.
- **`spawn` :** `realize_enter` sur la vue, puis `Push.mem` (jalon 1) pour les frames.
- **`exitFrameC` et `terminate` :** `realize_exit` sur la vue, puis `Pop.view_tail` (jalon 1).
- **Composite :** `realize_enter` pour la création ; `realize_vals` (`:429`) pour les transferts ; `reprC_yield` pour la cession. Les transferts sont prouvés sur les états **cédés** `yieldEff t ps f`, où `KBase` est établi phase par phase par `transfers_base` (jalon 1). Ce passage est licite pour deux raisons :
  - `Repr` ne lit pas `A` ;
  - `transferOps` ne lit que `P`.
- **`join`, `deriveSync`, `newMutex`, `acquire`, `unlock`, `resetLock` :** exécution vide. `ReprC` est conservée car ni `P`, ni `I`, ni `dead`, ni les frames ne changent (`reprC_set_same`).

### R2 — simulation : prouvé

`simulationC` (`Realize.lean:616`) : sous `DDSound k` et `Refinement.ParamsOK C π`, pour tout `SimRunC … st m`, on a :

- `∃ ops, Machine.Exec C ObR ObW ops Machine.State.empty m` ;
- `ReprC π.L π.rtok st.1 m` ;
- `∃ lbls, EncapsulatedTrace k L (SC.ofS3 (S3.init statics), []) lbls st`.

Les paramètres sont fixés une fois par exécution, comme dans `Refinement.SimRun`. Les représentations écrites `w` sont une donnée de chaque pas. La preuve est une récurrence qui porte `KInvCA` : `init_inv` au départ, `lstep_kInvCA` à chaque pas.

Non-vacuité : `s4_simRun` et `s4_realized` (`:735`, `:756`). La trace S4 du jalon 1 (`Traces.s4_trace`) est une `SimRunC` sous les paramètres de test `piOf q6.P []`. Ses pas sont `enterFrame`, deux `write`, `alloc`, le composite par valeur et `exitFrameC`. La mémoire finale vérifie :

- `ReprC` ;
- les allocations de `v` et `p` (locaux de la frame sortie) sont mortes ;
- celle de `d` (local du contexte 1) est vivante ;
- les octets de `d` sont ceux écrits dans `v` avant le composite.

### R3 — sûreté concrète : prouvé

- **Forme générale :** `exec_noUB` (`:645`). Aucun pas d'une exécution n'a d'issue `ub` là où il s'exécute. La preuve combine deux faits : une exécution n'est faite que de pas `ok`, et un pas brut a au plus une issue (`*_det`).
- **Par pas :** `r3_step` (`:666`). Sous les hypothèses de R1, aucune opération brute de `realize π w lbl st.1 m` n'est `ub`.
- **Sur une exécution :** `concrete_safety` (`:680`). Pour tout `SimRunC`, la mémoire est atteinte par une exécution dont aucun pas n'est `ub`.

Les docstrings nomment le fragment couvert. R3 vaut **sous les obligations paramétriques** `ObR` et `ObW` de chaque lecture et écriture, qui comprennent §15.7 et §16.6 (« concurrency rules are satisfied »), voir § 4.

### R4 — `OrdinaryCrossContextNonConflict` : prouvé

`r4_nonConflict` (`NonConflict.lean:141`) : `KInvC s → OrdinaryCrossContextNonConflict k s`.

L'énoncé, dans les mots du brief : pour tous contextes vivants `c ≠ c′`, toutes autorités `a`, `b` et toutes listes de feuilles `L`, `L′`, si `Write3Pre (s.view c) a L` et `Read3Pre (s.view c′) b L′ ∨ Write3Pre (s.view c′) b L′`, alors toute feuille de `L` et de `L′` est `K.SharedMutable`.

La preuve passe par `cross_context_disjoint` (`:117`), qui donne la conclusion plus forte `∀ l ∈ L, l ∉ L′`. Elle n'utilise que `FramesC`, `WF3` et `I1` de `KInvC`.

- **`a ≠ b` :** I1 (§50) et le calcul des modes effectifs (§43.3–4), via `effective_exclusive`.
- **`a = b` :** `no_double_exercise` (`:55`), par récurrence sur la dérivation de `ExercisableAt` (§43). C'est la clause récursive :
  - une autorité tenue par une frame n'est exerçable que depuis cette frame, et les frames courantes de deux contextes distincts diffèrent (`view_tops_ne`, `:93`, par l'unicité des frames, WC4 C3) ;
  - une autorité tenue par une place `p` n'est exerçable en `Modify` depuis `c` qu'à travers une autorité `b` de mode effectif `Modify` sur une feuille de `p`. Elle n'est exerçable depuis `c′` qu'à travers une autorité `b′` de mode effectif présent sur la même feuille. I1 force `b = b′`, et la question se repose un cran plus bas.

  La chaîne est finie parce que `ExercisableAt` est un inductif. `NoOrphan` (§54), que le brief anticipait, n'est pas utilisé.

Non-vacuité : `r4_nonvacuous` (`:185`). Dans l'état final `q6` de S4, qui vérifie `KInvC`, les contextes 0 et 1 sont vivants. De plus :

- `Write3Pre (q6.view 0) 0 [0]` est vraie ;
- `Read3Pre (q6.view 1) 4 [4]` et `Write3Pre (q6.view 1) 4 [4]` sont vraies.

**Remarque sur l'énoncé.** La conclusion « `SharedMutable` » n'est jamais utilisée. Pour les hypothèses de R4, l'intersection `L ∩ L′` est toujours vide, qu'une feuille soit `SharedMutable` ou non. La raison : O10 exige un mode effectif `Modify` sur chaque feuille écrite (§67.1, `Write3Pre.effectiveModify`), et un mode effectif `Modify` exclut tout autre mode effectif sur la feuille (§43, §50). L'exception `SharedMutable` du brief (« O9 admet une lecture ordinaire … pendant un `writeShared` ») ne joue qu'avec O11, qui n'exige qu'un mode effectif présent (§68.2) ; or O11 n'est pas une hypothèse de R4. R4 est donc vrai, mais sa clause `SharedMutable` est vide. Un énoncé avec `writeShared` d'un côté serait un autre théorème : il n'est pas formalisé.

### Frontière de R4

R4 est l'absence de conflit au sens de l'adjacence dans un entrelacement de pas abstraits : deux pas ordinaires habilités dans deux contextes distincts ne touchent aucune feuille commune non `SharedMutable`.

Reste pour OB-C06 : chaque ordre que la machine d'autorités impose entre deux accès conflictuels doit être réalisé par une relation d'ordre mémoire. Exemples d'ordres imposés :

- la libération d'un grant avant sa ré-acquisition ;
- `terminate` avant `join`.

Les relations attendues sont `LockOrder` (OB-C04) et l'ordre de complétion (OB-C11). R4 n'est pas une preuve d'absence de data races.

### R4′ — corollaire d'octets : prouvé

`r4_bytes` (`NonConflict.lean:150`). Sous `KInvC s` et `LayoutWF Lm s.flat m`, avec les mêmes hypothèses d'habilitation que R4, on a :

```
ByteDisjoint Lm (L.filter fun l => !decide (k.SharedMutable l))
  (L'.filter fun l => !decide (k.SharedMutable l))
```

La preuve combine R4 et `LayoutWF.disjoint` (§23, §82.8). Le brief demande `LayoutWF` et `ReprC` ; seul `LayoutWF` est pris, qui est une partie de `ReprC`. La liste filtrée exige une instance `DecidablePred k.SharedMutable`.

### R5 — conservativité des réalisations : prouvé

`r5_realize` (`Realize.lean:561`). Pour `s.Single` et toute `op : KernelOp` :

- `realize π w (.kernel 0 op) s m = opsOf π (kopOf op w) s.toS3 m` ;
- `StepOblC … (.kernel 0 op) s m ↔ StepObl … (kopOf op w) s.toS3 m` ;
- `ReprC π.L π.rtok s m ↔ Repr π.L π.rtok s.toS3 m`.

La preuve s'appuie sur `single_view` et `single_flat` (jalon 1).

## 4. Obligations paramétriques laissées en hypothèses

Aucune n'est remplacée par `True`.

| Obligation | Où | Origine |
|---|---|---|
| `ObR.dec`, `ObR.stat` de chaque lecture brute : §15.4 (représentation valide), §15.6 (alignement), §15.7 (règles de concurrence) | `StepOblC` → `OblAlong` | Spec 1 §15 ¶5, §20.3 |
| `ObW.dec`, `ObW.stat` de chaque écriture brute : §16.4, §16.5, §16.6 (règles de concurrence) | idem | Spec 1 §16 ¶4, §20.3 |
| `C` : compatibilité de désallocation, avec chaque jeton compatible avec lui-même | `Refinement.ParamsOK` | Spec 1 §17, §73 |
| placement et géométrie des allocations nouvelles | `Refinement.ParamsOK` | Spec 1 §9 ¶11 |
| disposition des places nouvelles | `StepOblC` (`NewLayout`) pour `enterFrame`, `alloc`, `spawn`, composite | Spec 1 §82.1, §23 |
| instanciation de `K.FreeCompat` | `StepObl` pour `free` | Spec 1 §80, §70.2, §82.4 |
| types des feuilles `π.ty`, encodage des références `π.pe` | `Refinement.Params` | Spec 4, Spec 11 (§81) |
| `DDSound(K)` | R2, R3 | Spec 1 §80 |
| `KInvCA` de l'état de départ | R1, R3 par pas | WC4 C20 ; Spec 1 §57. Établi sur les états atteints par R2 |

Point essentiel : §15.7 et §16.6 sont des **hypothèses** de chaque pas brut. R1–R3 ne les établissent pas. Les établir est exactement OB-C01 à OB-C06.

## 5. Problèmes de WC4 ou de la Spec 1

Aucun bloquant. Pas de silence ni de contradiction qui aurait exigé un arrêt.

- **WC4 C5 et réalisation du composite.** Passage : C5, « This is a **single composite candidate transition** … not an ordinary sequential execution of O6 followed by O4 ». Le pas abstrait reste unique. Sa réalisation (prescrite par le brief) est une séquence : créations, puis copies. Les états mémoire intermédiaires correspondent aux états de phase (`spawnCreate`, préfixes de `transfersEff`), qui ne sont pas des états de `S_C` atteints par un pas étiqueté. Au grain des pas abstraits, aucun autre contexte ne les observe. Exemple : dans S4, entre la création de `d` et la copie de `v` dans `d`, la mémoire contient `d` alloué et non initialisé. C'est hors fragment (OB-C14, OB-C01).
- **Citation périmée dans le jalon 1.** La WC4 corrigée retire « (former C13.10) » de C13. La docstring de `NewMutexPre` (`SyncLib.lean:228-231`) cite toujours « former C13.10 ». Elle n'est pas modifiée : le brief interdit de toucher au jalon 1.
- **Contrôleur et registre (WC4 C13, C17, C25).** Les opérations de verrou n'ont pas de réalisation. La feuille `ctl` est une feuille ordinaire : `ReprC` exige seulement que ses octets soient initialisés quand elle est `Init`. Rien ne relie ses octets à l'état du registre, alors que C13 exige « the initial physical controller state must correspond to the newly available abstract registry entry ». Ce n'est pas un défaut : WC4 le classe sous OB-C05.

## 6. Décisions de représentation

1. **`ReprC`** est défini sur `s.flat`, comme le demande le brief. `reprC_view` montre l'équivalence avec `Repr` sur toute vue.
2. **Représentations écrites.** `Label.kernel c op` porte une `KernelOp`, sans les représentations que `Refinement.KOp.write` porte. `realize` prend donc un paramètre `w`. R1 vaut pour tout `w` ; `SimRunC.step` choisit `w` par pas. `kopOf` relie les deux types d'opérations.
3. **Réalisation unique.** Une opération héritée se réalise par `opsOf` sur la vue, y compris les opérations réindexées. Pour ces dernières, la preuve passe par des lemmes `realize_*` qui reprennent les preuves de `r6_*` avec les seules clauses lues (§ 3, R1).
4. **Composite.** La réalisation suit les états de phase non cédés. La preuve passe par les états cédés, où le jalon 1 établit `KBase`. Le passage est licite car `Repr` ne lit pas `A` et `transferOps` ne lit que `P`.
5. **`StepOblC`** réutilise `Refinement.StepObl` sur la vue pour les opérations héritées. Pour `spawn` et le composite, il ajoute `NewLayout` des locaux.
6. **`SimRunC`** reprend le schéma de `Refinement.SimRun` : obligations par pas, paramètres fixés une fois. L'état initial est l'état de la Spec 1 §47 en contexte unique, avec un registre vide, comme `init_inv` du jalon 1.
7. **R3** est exprimé par `NoUB`, l'absence d'issue `ub` là où l'opération s'exécute.
8. **R4** porte sur des listes de feuilles, car `Write3Pre` et `Read3Pre` prennent des listes. « État atteignable » est rendu par `KInvC`, que `encapsulated_inv` établit sur toute trace encapsulée depuis l'état initial.
9. **R4′** utilise `ByteDisjoint` de `Refinement.lean` sur les listes filtrées. Ses hypothèses sont `LayoutWF` et `KInvC`, sans `ReprC` complète.
10. **Noms.** Le brief écrit `LStep k L` et `LayoutWF` avec le même `L`. Dans le code, la disposition mémoire est `π.L : Layout` (ou `Lm`) et la disposition du mutex est `L : MutexLayout`.

Hypothèses du brief retirées, chacune parce qu'elle n'est pas utilisée (l'énoncé n'en est que plus fort) :

- `DDSound` en R1 ;
- `ReprC` en R4′, remplacée par sa partie `LayoutWF`.

## 7. Écarts avec la Spec 1

Aucun. Les réalisations des opérations héritées sont celles de `Refinement.lean`. R5 montre qu'elles coïncident avec elles en contexte unique.

## 8. OB-C05 et OB-C12

**OB-C05 (réalisation atomique de l'acquisition, du déverrouillage, de la reprise) : entièrement ouvert.**

- `newMutex`, `acquire`, `unlock` et `resetLock` ont une réalisation vide. R1 et R2 tiennent pour cette réalisation parce que le registre est un état de bibliothèque hors `S_C` et que `ReprC` ne le lit pas.
- Le jalon 2 ne dit donc rien de la correspondance entre registre et contrôleur physique (C13, C17, C18, C25), ni de l'atomicité.
- Une écriture ordinaire de `ctl` (C22.4, S12) se réalise comme toute écriture ordinaire. R1 la couvre comme pas mémoire sûr, mais le protocole du contrôleur reste une obligation d'interface.

**OB-C12 (correspondance concrète de la Spec 1 §82) : déchargée sur le fragment des pas abstraits, pour :**

- §82.1 : `ReprC` ; les frames n'ont pas de représentation (`repr_frames_congr`) ;
- §82.2–§82.5 : R1 et R2, pour toutes les étiquettes de `LStep`, composite compris ;
- §82.8 : R4′.

**Non couvert :**

- §82.6 (adresses épinglées) : `pinned_address_stable` n'est pas transporté au cas concurrent ;
- §82.7 (arènes) : `LStep` n'a pas d'étiquette d'arène ;
- §82.3 (adresse et provenance écrites par `store`) : `pointer_sound_store` n'est pas transporté ; R1 ne donne que `ReprC`.

Ces extensions n'étaient pas demandées.

## Ce qui n'est pas vérifié

- Aucune revue adversariale n'a été faite.
- Le témoin S4 n'exerce pas `spawn` sans valeur, `terminate`, `join`, ni les opérations de verrou. R1 et R2 les couvrent par preuve, sans exécution concrète.
