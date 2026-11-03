# ERN — Vérification exploratoire : dérivabilité des arènes et faisabilité de `DataStack`

Branche `formal/derivability_0.1`, créée depuis `formal/validation_0.1`. Brouillon : pas de fusion, pas de PR. Spécification de référence : `ERN_Spec1_Memory_Model_specification_normative_candidate_corrigee.md` (Spec 1 candidate, non validée, non copiée dans le dépôt). Les modules existants (`Ern/MM02.lean`, `Ern/MM03.lean`, `Ern/MM23.lean`, `Ern/HandlePool.lean`, `Ern/MM03/Horrors.lean`, `Ern/MM23/Horrors.lean`, `Ern/MM03/LockOptions.lean`) sont inchangés. Nouveaux modules : `Ern/Derived/Arena.lean` (question 1), `Ern/Lib/DataStack.lean` (question 2).

## État de vérification

| Étape | Commit | Module |
|---|---|---|
| Question 1 | 6b7cf20 | `Ern/Derived/Arena.lean` |
| Question 2 | 59c276f | `Ern/Lib/DataStack.lean` |
| Revue adverse, corrections, rapport | voir l'historique de la branche | les deux modules et ce rapport |

- `lake build` : réussi, sans avertissement.
- La recherche de `sorry`, `admit`, `native_decide` et `axiom` est vide ; aucun `noncomputable`.
- Parcours `collectAxioms` de **toutes** les constantes des deux modules : rien hors de `propext` et `Quot.sound` (pas même `Classical.choice`).
  - `Derived.Arena` : 159 constantes, dont 86 théorèmes ;
  - `Lib.DataStack` : 360 constantes, dont 156 théorèmes.

**Passages de la spécification lus et formalisés.** §36, §42 à §47, §54 à §58, §60 (O1), §61 (O2), §62 (O3), §65 (O8), §76 (O17), §77 (O18), §78 (O19), §86, §88, §89. Chaque définition et théorème cite son passage dans sa docstring.

**Méthode.** Les équivalences sont énoncées pour tout état atteint (`Reachable k statics s`, sous `DDSound k`) et prouvées dans les deux sens ; chaque écart est accompagné d'un contre-exemple sur un état atteint, décidé par `decide`. Les contre-exemples sont conservés comme théorèmes `ce_*`.

**Objets comparés.** Le noyau (`Ern.MM03`) formalise un texte antérieur ; `issue` et `reset` y diffèrent de la Spec 1 candidate. Le module définit donc les opérations restreintes à partir du texte candidat :

- `MetaRightM` : `MetaRight` réduit à sa première branche (`Modify` exerçable sur la valeur arène), conformément à l'hypothèse de la tâche ;
- `IssueR` : §77 avec `MetaRightM`, sur une entrée donnée.
  - Il reprend les clauses statiques du noyau (`issueStaticR_iff`).
  - Il y ajoute deux points du texte candidat absents du noyau : la destination hors de la région (§77.2, « prévention locale de l'auto-blocage ») et l'ancre du bloc ajoutée à `D(destination)` (§77, effet : « qui reçoit l'ancre correspondante »).
  - `ArrivalR` regroupe les contrôles sur l'état d'arrivée : `AnchorOrder` de la nouvelle ancre (§77.3) et `AnchorOrderHeld` (§77.6).
  - `IssueAtR` ajoute la recherche de l'entrée dans l'état (§77.1, « L'entrée `arena` existe ») et réécrit ses métadonnées, comme `IssueAt` du noyau.
  - La disponibilité est le `Avail` du noyau, lu feuille par feuille ; c'est une ambiguïté du texte, voir (c) 8 et (f) 2.
- `ResetPreR` : §78 avec `MetaRightM`. Il comprend la vivacité de l'entrée (§78.1) et reprend les clauses de `ResetAtPre` et `ResetPre` du noyau (`resetPreR_iff`). `ResetAtPreR` ajoute la recherche de l'entrée.

## (a) Statut de `issue_as_kernel`, `reset_as_kernel`, `newArena_as_library`

### `issue_as_kernel` — prouvé, avec deux clauses d'écart identifiées

Séquence noyau : `split` de `internal` sur `[région]` (O2 à une région, c'est-à-dire une dérivation `Modify` sur une liste de feuilles), puis `store` (O8) du bloc dans la destination. Lorsque la région est l'empreinte d'un emplacement `q`, `split` coïncide avec `derive` (O1) de `internal` sur `q`, avec le même effet (`derive_iff_split`).

| Théorème | Énoncé |
|---|---|
| `issue_to_seq` | `IssueR … (ok s' ar')` et `HasRight s' Modify dst` ⟹ `split` puis `store` sont `ok`, avec l'état d'arrivée `s'` |
| `seq_to_issue` | `split` puis `store` `ok`, région disponible, destination non `Init` ⟹ `IssueR … (ok s₂ _)`, même état d'arrivée |
| `issue_as_kernel_split` | équivalence des deux, pour toute région |
| `issue_as_kernel` | même équivalence avec `derive` sur un emplacement `q` (région = empreinte de `q`) |
| `issueR_fail_iff`, `issueR_reject_iff`, `issueR_total`, `issueR_det` | `fail` ⟺ clauses statiques et région indisponible (§77.4) ; `reject` ⟺ ni `ok` ni `fail` |

Forme exacte (`issue_as_kernel_split`), pour tout état atteint `s` et toute entrée `ar ∈ s.arenas` :

```
IssueR ar r dst s (ok s' ar') ∧ HasRight s' Modify dst
  ⟺ Avail ar r ∧ (dst non Init) ∧ split(internal, [r]) ok ∧ store(bloc, dst) ok vers s' ∧ ar' = métadonnées de §77
```

- **État d'arrivée.** La partie noyau de l'état d'arrivée de `issue` (avec l'ancre ajoutée à `D(dst)` par le texte candidat) est l'état d'arrivée de `store`. C'est une égalité de structures (`issueEffR_eq`), pas une simple correspondance.
- **Clauses qui coïncident.**
  - `MetaRightM` est exactement l'exercice de `internal` en `Modify` exigé par O1.1 et O2.1 (`metaRightM_iff`).
  - Le droit effectif de §77.5 est celui de O1.2 et O2.1.
  - La destination hors région (§77.2) est la première moitié de O8.3.
  - Les contrôles d'arrivée de §77.3 et §77.6 sont ceux de O8.4 et O8.5 (`AnchorOrderHeld`). `AnchorOrderHeld` ne dépend pas de `D`.
  - La seconde moitié de O8.3 (stockage possédé transitivement par la destination) n'introduit **aucun** rejet de plus dans un état atteint. Une destination qui posséderait un emplacement utilisable détiendrait l'autorité racine de cet emplacement (`RootLive`), ce que §77.2 exclut déjà (`ownedIn_holds`).
- **Clauses qui diffèrent** : voir (c), écarts 1 et 2.
- **Disponibilité.** Une région émise puis libérée sans `reset` est indisponible dans les métadonnées, mais `internal` y a retrouvé son droit effectif. `issue` y échoue (`fail`) alors que la séquence est `ok` (`ce_avail`). C'est le rôle attendu des métadonnées : `fail` ⟺ clauses statiques ∧ région indisponible.

### `reset_as_kernel` — prouvé, avec deux clauses d'écart ; la seconde clause ne découle pas de `release`

Séquence noyau : `derive` de `internal` en `Modify` sur le stockage (O1), puis `release` (O3) de l'autorité dérivée.

| Théorème | Énoncé |
|---|---|
| `reset_to_seq` | `ResetPreR` (entrée vivante comprise) ⟹ `derive` puis `release` `ok` |
| `seq_to_reset` | `derive` puis `release` `ok`, aucune dérivation active d'empreinte vide, `internal` ancre d'aucun emplacement utilisable ⟹ `ResetPreR` |
| `reset_as_kernel` | équivalence des deux |
| `reset_seq_arrival` | l'état d'arrivée de la séquence est l'état de départ plus une autorité inactive ; `reset` ne change pas la partie noyau |
| `reset_clause3_strict` | sous la lecture stricte de §78.3, la clause découle de §78.2 et de I3 |

Provenance des clauses de `ResetPre` :

- **§78.1.** `MetaRightM` est l'exercice exigé par O1.1 (`metaRightM_iff`).
- **§78.2** (« aucune autorité dérivée de `internal` ne reste active »). Elle découle de O1.2 (droit effectif `Modify` sur tout le stockage) pour toute dérivation qui couvre une feuille. Une dérivation active d'**empreinte vide** (`split` de `internal` sur `[[]]`) bloque `reset` sans bloquer la séquence (`ce_reset_empty`).
- **§78.3.** Elle **ne découle pas** des préconditions de `release`. `release` d'une autorité fraîche ne contrôle que ses propres ancres (O3.3), et la séquence ne libère que cette autorité fraîche.
  - Pour les dérivées strictes de `internal`, la clause découle de §78.2 et de I3 : une ancre d'un emplacement utilisable est active (`reset_clause3_strict`).
  - Pour `internal` lui-même, elle ne découle de rien. Le noyau lit « sous-arbre d'origines de `internal` » en y incluant `internal`. Une valeur arène qui a reçu `internal` par `store` porte `internal` dans `D` (O8, effet). `reset` y est alors rejeté tant que la valeur arène est utilisable, et la séquence est `ok` (`ce_reset_anchor`, `reset_blocked_by_stored_internal`).

### `newArena_as_library` — prouvé : aucune propriété de sûreté ne dépend de la garde

- **Inscription.** Elle ne touche aucune composante du noyau (`newArena_kernel_noop`).
- **Atteignabilité sans garde.** `ReachableNG` contient tous les pas de `Reachable` plus l'inscription sans la garde de §56 (`NewArenaPreNG`, et `newArenaPre_iff` : la précondition du noyau est `NewArenaPreNG` plus la garde).
- **Invariants.** Sur tout état de `ReachableNG`, sous `DDSound`, valent tous les invariants de §57 (`newArena_as_library`) : `WF3`, `Inv3` (I1 à I4, `AnchorOrder`, `NoDangling`), `AnchorOrderHeld`, `NoOrphan` et `ArenaInv` de chaque arène vivante.
  - Preuve : chaque pas de `Reachable` préserve ces invariants **et** `RootLive` sur tout état qui les vérifie (`step_inv57`, reprise des cas de `reachable_invariants`, `reachable_anchorOrderHeld`, `reachable_rootLive`).
  - L'inscription sans garde les préserve aussi (`newArenaNG_inv57`). La preuve du noyau, `newArena_preserves`, n'utilise d'ailleurs pas la garde.
- **I1.** Il rejette la double émission par deux administrations du même `internal`. Un bloc actif dérivé de `internal` ôte à `internal` le droit effectif sur ses feuilles. Ni l'`issue` du noyau, ni `IssueR`, ni `split` ne passent alors, quelle que soit l'entrée (`issue_blocked_by_block`).
  - Exemple : `ce_two_admins`. Deux entrées partagent `internal` 4. L'émission de `[5]` par l'entrée 0 est `ok`. Celle de `[5]` par l'entrée 1 est rejetée, alors que ses métadonnées tiennent 5 pour disponible.
- **Seul effet observable de la garde.** Il porte sur le classement des issues : avec deux administrations, une région émise par l'autre donne `reject` au lieu de `fail`. Même avec la garde, les métadonnées ne sont pas exactes. Un cadre qui exerce `internal` peut dériver directement depuis lui, et une région disponible est alors rejetée (`ce_avail_reject`).

## (b) Contre-exemple de la branche `writeShared` (conservé)

`ce_writeShared`, sur l'état `a6` du cas 16 du noyau (`a6_reachable`), sous `KA` (feuille 0 `SharedMutable`) :

| Élément | Valeur |
|---|---|
| Cadre courant | appelé ; seule autorité sur la valeur arène 0 : l'autorité 4, en `Observe` |
| Arène | entrée `ar7` (stockage 3, `internal` 3), `issued = []` (aucune émission active) |
| `issue` du noyau, `[4]` vers 6 | `ok` (`IssueAt KA 0 4 [4] 6 a6 (ok a7)`), par la branche `writeShared` de `MetaRight` |
| `reset` du noyau | `ok` (`ResetAtStep KA 0 4 a6 (ok _)`) |
| `MetaRightM` | faux |
| `derive` de `internal` sur 4 (la région) et sur 3 (le stockage), `split` sur `[4]` | `reject` : `internal` n'est exerçable en `Modify` par aucun lien |
| `IssueR`, `ResetPreR` | `reject` |

## (c) Écarts dans les deux sens

| # | Sens | Clause | Contre-exemple | Nature |
|---|---|---|---|---|
| 1 | `issue` accepte, la séquence rejette | O8.5 (`store` : « dans l'état d'arrivée, `target` reste sous `Modify` exerçable »), sans équivalent dans §77 | `ce_g2` | spécification |
| 2 | la séquence accepte, `issue` rejette | §77.2 (« non `Init` ») contre O8.2 (« Le fait que ses données soient déjà `Init` n'interdit pas à lui seul l'opération ») | `ce_init` | spécification |
| 3 | `reset` rejette, la séquence accepte | §78.3 lu avec `internal` inclus ; `internal` placé par `store` est ancre de la valeur arène | `ce_reset_anchor` | spécification (ambiguïté, (f) 1) |
| 4 | `reset` rejette, la séquence accepte | §78.2 et une dérivation active d'empreinte vide | `ce_reset_empty` | spécification |
| 5 | `issue` et `reset` du noyau acceptent, les séquences rejettent | branche `writeShared` de `MetaRight` (§78.1) | `ce_writeShared` | attendu par la tâche |
| 6 | `issue` accepte, `derive` ne peut pas | région qui n'est l'empreinte d'aucun emplacement, région vide comprise : le `derive` du noyau prend un emplacement | `ce_empty_region` | noyau (représentation) ; `split` à une région couvre le cas |
| 7 | — | `issue` du noyau : n'exige pas la destination hors région, n'ajoute pas l'ancre à `D(dst)` | `issueStaticR_iff`, `issueEffR` ; `H50_options` (jalon 3) | noyau antérieur au texte candidat |
| 8 | `issue` échoue où une autre lecture rejetterait | §46 (`available: Set<Region>`), §77.4 (« `region` n'appartient plus à `available` ») : le noyau lit la disponibilité feuille par feuille | `ce_avail_leaf` | spécification (ambiguïté, (f) 2) |

Détail de l'écart 1 (`ce_g2`) :

- **Construction.** Une autorité 5, dérivée de la racine de la destination 2, est rangée dans la feuille de stockage 1. La destination n'est alors exerçable en `Modify` que par 5, donc par `internal` sur 1.
- **Issue.** `IssueR` et l'`issue` du noyau sont `ok` pour la région `[1]` vers 2.
- **Arrivée.** Le bloc sur 1, détenu par 2, et 5, détenu par 1, se bloquent mutuellement ; 2 n'est plus exerçable.
- **Séquence.** `split` est `ok` ; `store` est rejeté par O8.5.

C'est un blocage indirect que §88 admet (« des blocages indirects compatibles avec la sûreté peuvent subsister »). Option 2 (destination hors région) et O8.3 coïncident ; seul O8.5 sépare.

Détail de l'écart 8 (`ce_avail_leaf`). Après l'émission de `[5]`, bloc actif :

- **Lecture du noyau** (feuille par feuille). La région `[5, 6]`, qui chevauche l'émission en partie, est indisponible : `issue` échoue (`fail`, §77.4).
- **Lecture « ensemble de régions »** (§46). Seule `[5]` quitte `available`, donc `[5, 6]` resterait disponible et §77.5 la rejetterait (`reject`), `internal` n'ayant plus le droit effectif sur 5.
- **Conséquences de la lecture du noyau.** La phrase de §77.5 « La région ne peut chevaucher une région émise encore active » n'est jamais atteinte dans un état atteint. La région vide est toujours disponible.

L'équivalence de (a) vaut pour l'une ou l'autre lecture : la disponibilité n'y figure que comme hypothèse sur les métadonnées.

## (d) Statut des théorèmes de `DataStack`

`DataStack` est une instance de bibliothèque. Son état contient l'état du noyau, les piles (stockage, `internal`, cellules ordonnées, sommet, blocs émis, marques vivantes) et le prochain identifiant de marque. Ses opérations n'effectuent que des pas du noyau :

| Opération | Pas du noyau | Issues |
|---|---|---|
| `push` | clauses statiques de l'`issue` restreint (§77.1, §77.2) avant la place, puis `split` et `store` | `fail` sans place |
| `rewind` | `split` puis `release` (`reset` dérivé) sur les cellules au-dessus de la marque | `fail` pour une marque non vivante de la pile |
| `grow` | clauses statiques (dont `MetaRightM`) avant la place, puis `release` du dernier bloc et `issue` dérivé de même base et de taille plus grande vers la même destination, déjà `Init` | `fail` sans place |
| `mark` | aucun (métadonnées) | toujours `ok` |
| `newStack` | aucun (inscription) | garde de §56 sur les deux registres |

Un `newArena` du noyau consulte aussi le registre des piles (`KGuard`, §56). Tout pas `ok` de la bibliothèque est une suite de pas de `Reachable` (`dexec_reach`, `drun_reach`).

| Théorème | Statut | Énoncé |
|---|---|---|
| `rewind_rejects_live_above` | prouvé | marque vivante, autorité active dérivée de `internal` couvrant une cellule au-dessus de la marque ⟹ `rewind` = `reject` ; réciproque `rewind_ok_no_live_above` |
| `mark_no_aba` | prouvé | **toute** marque retirée par `rewind m` (`m` et les marques postérieures de la pile) n'est plus vivante dans aucune pile après toute suite d'opérations, et son `rewind` échoue (`fail`), même quand le sommet revient à sa position. Hypothèse `MarksWF` (marques deux à deux distinctes, nommant leur pile, d'identifiants donnés), établie pour tout état atteint par la bibliothèque (`drun_init_marksWF`) |
| `rewind_removes` | prouvé | sous `MarksWF` : après `rewind m`, les marques de la pile sont exactement celles antérieures à `m` ; `m` et les postérieures sont retirées |
| `rewind_keeps_older_marks` | prouvé | après `rewind m` : marques = celles antérieures à `m`, sommet = sommet de `m`, autres piles inchangées, initialisation inchangée |
| `grow_same_base` | prouvé | dernier bloc de même base, de taille `size + extra`, de même destination enregistrée ; dans l'état d'arrivée, l'autorité nouvelle couvre les cellules depuis la même base et est détenue par cette destination, et l'ancien bloc est inactif ; anciennes cellules préfixe des nouvelles |
| `grow_keeps_prefix_init` | prouvé | aucune cellule de l'ancien bloc ne change d'initialisation |
| `grow_keeps_prefix_bytes` | prouvé, via `Ern.MM23` inchangé | voir ci-dessous |

Détail de `grow_keeps_prefix_bytes`. `release` et `split` sont des pas sans pas MM-02 (`NoStep`, K4, dont `r6_noStep` conserve `Repr`). `store` correspond à une écriture de la plage de la destination (`storeOps`, L6). Pour toute disposition `LayoutWF`, cette écriture laisse inchangés les octets **et provenances** (`rangeBytes`) de chaque cellule de l'ancien bloc.

Cas (`decide`, chaque exécution étant d'abord établie `ok`) :

| Cas | Théorème | Contenu |
|---|---|---|
| plusieurs piles | `case_stacks` | piles indépendantes ; marque d'une autre pile : `fail` ; garde de §56 sur `newStack` et sur le `newArena` du noyau (que le noyau seul accepterait) |
| `rewind` refusé puis accepté | `case_rewind` | refusé tant que le bloc 7 vit, accepté après sa libération |
| ABA | `case_aba` | sommet revenu à 2 ; la marque retirée `⟨0, 1, 2⟩` échoue ; la nouvelle `⟨0, 2, 2⟩` est acceptée |
| `grow` | `case_grow` | accepté en place ; sans place : `fail` ; bloc qui n'est plus le dernier : `reject` |
| cadre | `case_frame` | marque à l'entrée de l'appelé, `push` dans un local ; `rewind` refusé tant que le bloc vit ; après `endUse` du local, `rewind` et `exitFrame` acceptés, pile vide |
| lecture de `rewind` | `case_rewind_reading` | une autorité dérivée active couvrant la partie d'une région émise après `m` qui est sous `m` (bloc agrandi) ou au-dessus du sommet courant ne bloque pas `rewind` ; un bloc vide (`push` de taille 0) non plus |
| statique avant `fail` | `case_static_before_fail` | sans droit sur la valeur pile, `grow` est rejeté avec ou sans place ; `push` vers une destination `Init`, ou intérieure aux cellules demandées, est rejeté même sans place |
| atteignabilité | `cases_reachable` | les états noyau des cas sont atteints |

Constat utile pour la question 1 : `grow` réémet dans une destination déjà `Init`, celle du bloc libéré. Il n'est exprimable qu'avec l'`issue` dérivé, `store` acceptant une cible `Init` ; `IssueR` le rejetterait (écart 2). `push`, que la tâche définit par l'`issue` restreint, en suit les clauses statiques ; réalisé par `split` et `store`, il en diffère seulement par O8.5 (écart 1, `issue_as_kernel_split`).

## (e) Amendements de texte de la Spec 1 qui découlent des résultats

Chaque amendement porte sur une clause. Lorsque les résultats laissent deux formulations, les deux sont données et le choix est renvoyé à l'arbitrage ((f)).

1. **§77.1 et §78.1 (`MetaRight`).** Si la dérivabilité est retenue, retirer la branche `writeShared`.
   - §78.1 : « La mise à jour des métadonnées de l'arène est autorisée par `MetaRight(s,arena)` : `Modify` exerçable sur la valeur arène. » La suite « **ou** mutation `writeShared` légale sur ses métadonnées `SharedMutable` » est supprimée.
   - §36 : remplacer « L'arène des opérations O17–O19 en est une illustration » par une phrase qui exclut l'arène de l'administration depuis une autorité partagée, puisque l'administration d'une arène exige l'exercice de `internal` en `Modify` (`ce_writeShared`, `metaRightM_iff`).
2. **§77.2 (destination non `Init`) contre O8.2.** Deux formulations :
   - (A) supprimer « non `Init` (elle peut notamment être `Uninit` ou `Moved`) » de §77.2. `issue` coïncide alors avec la séquence (`issue_as_kernel_split`), et `grow` en place est exprimable ;
   - (B) conserver §77.2. Ajouter à §77 : « Cette clause est une précondition propre de l'abstraction ; elle n'a pas d'équivalent dans O8 (O8.2). » L'équivalence porte alors la précondition « non `Init` » du côté de la séquence.
3. **§77.6 contre O8.5.** Deux formulations :
   - (A) ajouter à §77.6 : « Dans l'état d'arrivée, `destination` reste sous `Modify` exerçable pour le cadre courant ; cette clause est une vraie précondition supplémentaire, comme O8.5. » `issue` rejette alors `ce_g2`, comme `store`. §88 devient : « … `issue` ne peut émettre dans une feuille appartenant à la région émise, ni vers une destination qui ne serait plus exerçable dans l'état d'arrivée. »
   - (B) conserver §77 et retirer O8.5. `store` accepte alors les blocages indirects que §88 admet. Cette option modifie O8 ; ses effets sur les autres propriétés ne sont pas mesurés ici.
4. **§78.3 (« sous-arbre d'origines de `internal` »).** Deux formulations :
   - (A) « … d'une ancre située dans le sous-arbre **strict** d'origines de `internal` (les autorités dérivées de `internal`, `internal` exclu). » La clause découle alors de §78.2 et de I3 (`reset_clause3_strict`). Elle peut être maintenue comme conséquence, avec une note.
   - (B) conserver la lecture inclusive (celle du noyau). Ajouter : « Une valeur arène qui a reçu `internal` par `store` dépend de `internal` ; `reset` est rejeté tant qu'elle est utilisable. » Cela rend `reset` inutilisable pour les arènes construites ainsi (`ce_reset_anchor`).
5. **§78.2 et les dérivations d'empreinte vide.** Deux formulations :
   - (A) « Aucune autorité active dérivée de `internal` ne **couvre une feuille du stockage administré**. » `reset` coïncide alors avec la séquence pour cette clause ;
   - (B) conserver §78.2. Ajouter que la séquence `derive` puis `release` ne la contrôle pas pour les dérivations d'empreinte vide (`ce_reset_empty`), que §61 permet (« sous-régions de taille nulle »).
6. **§46 et §77.4 (disponibilité).** Deux formulations :
   - (A) lecture par feuilles : « `region` est disponible si chacune de ses feuilles appartient à `available` ». Supprimer alors la phrase de §77.5 « La région ne peut chevaucher une région émise encore active », qui n'est plus atteignable, et préciser que la région vide est toujours disponible (`ce_avail_leaf`) ;
   - (B) lecture par régions : `available: Set<Region>` et « `region` ∈ `available` ». Préciser alors ce que devient une région qui chevauche une région émise (rejet par §77.5) et ce que `reset` rend disponible (« la totalité des régions du stockage »).
7. **§56 et O17.4 (garde d'administration unifiée).** Ajouter à §56 : « Cette garde ne conditionne aucune propriété de sûreté de la section 57 : I1 rejette déjà une seconde émission d'une région par une autre administration du même `internal`. Son absence change seulement l'issue (`reject` au lieu de `fail`) d'une émission dont l'autre administration détient la région. » (`newArena_as_library`, `ce_two_admins`).
   - Si l'arbitrage veut la conserver comme règle, préciser à §56 que la création d'une arène par le noyau doit consulter les registres de bibliothèque, ce que `NewArenaPre` ne fait pas (voir `KGuard`).
8. **§58 et §XIV, si les arènes deviennent dérivées.** §58 dit que « seules `alloc` et `issue` peuvent émettre [`fail`] dans ce noyau ». Si O17–O19 sont des opérations de bibliothèque, remplacer par « seule `alloc` … ; les opérations de bibliothèque (§36) peuvent définir leurs propres échecs ». Adapter de même §46, §47, §55 et §57, qui placent l'entrée d'arène et `ArenaInv` dans l'état et l'invariant du noyau. Cet amendement découle de l'hypothèse de la tâche, pas d'un théorème : il est à confirmer.
9. **§60 (O1).** Aucun amendement. O1 prend une région ; c'est le noyau formalisé qui prend un emplacement (écart 6). Si une formalisation conserve un `derive` sur emplacements, `split` à une région tient lieu de `derive` sur région (`issue_as_kernel_split`).

## (f) Questions et décisions non dictées

### Questions pour arbitrage

1. **§78.3.** Lecture inclusive ou stricte du « sous-arbre d'origines de `internal` » ? Voir (e) 4 et l'exemple `ce_reset_anchor`. Ce passage est ambigu au sens d'`AGENTS.md`. La formalisation reprend la lecture du noyau sans la trancher.
2. **§46 et §77.4 (disponibilité).** Lecture par feuilles (celle du noyau, reprise ici) ou par régions ? Voir (e) 6 et `ce_avail_leaf` : les deux lectures classent différemment une région qui chevauche en partie une émission active (`fail` ou `reject`).
3. **§77.2 contre O8.2 (`Init`)** et **§77.6 contre O8.5 (exerçabilité d'arrivée)** : quelle formulation, (A) ou (B), de (e) 2 et (e) 3 ?
4. **§78.2 et l'empreinte vide** : (e) 5, (A) ou (B) ?
5. **§56** : la garde reste-t-elle une règle de la spécification, et doit-elle alors s'imposer au `newArena` du noyau envers les registres de bibliothèque ?
6. **`DataStack.push` et `grow`.** La tâche définit `push` par l'`issue` restreint, et `grow` par une émission de même base, sans dire laquelle. C'est un choix sémantique : il change les programmes acceptés.
   - `push` suit ici les clauses statiques de l'`issue` restreint : destination non `Init`, hors des cellules demandées, droit sur la valeur pile, tous contrôlés avant la place.
   - `grow` utilise l'`issue` dérivé : sa destination est `Init`, et l'`issue` restreint la rejetterait toujours.
   - Si la formulation (A) de (e) 2 est retenue, les deux coïncident.
7. **`DataStack.rewind`.** « Couvre une région émise après `m` » est lu sur les cellules que `rewind` rend (`above`, du sommet de `m` au sommet courant). Ce n'est pas exactement « les régions émises après `m` » (`case_rewind_reading`) :
   - un bloc agrandi après `m` commence sous `m`, et une dérivation active sur sa partie basse ne bloque pas `rewind` ;
   - une région émise après `m` puis rendue par un `rewind` intermédiaire est au-dessus du sommet courant ;
   - un bloc vide émis après `m` ne bloque pas `rewind`.

   Aucun de ces cas ne rend disponible une cellule couverte. Une lecture « couvre la région entière » laisserait `rewind` passer quand une dérivation en couvre une partie seulement, puis rejetterait le `push` suivant (I1). Quelle lecture est voulue ?

### Décisions de représentation prises ici (à confirmer)

- **`IssueR` suit le texte candidat** : destination hors région, ancre ajoutée à `D(dst)`. L'`issue` du noyau en diffère (écart 7). L'équivalence est donc établie pour le texte candidat ; pour l'`issue` du noyau, l'option 2 manque (`H50_options`, jalon 3).
- **Lecture inclusive de §78.3 pour `ResetPreR`**, celle du noyau ((f) 1). **Lecture par feuilles de la disponibilité**, celle du noyau ((f) 2).
- **Clauses statiques avant `fail`** (§58), par analogie avec §77 :
  - `push` : clauses de `IssueStaticR` (pile vivante, `MetaRightM`, destination feuille utilisable, sous `Modify`, non `Init`, sans autorité active, hors des cellules) ;
  - `grow` : `0 < extra`, `b` dernier bloc et au sommet, `b` libérable, pile vivante, `MetaRightM`.

  La tâche dit seulement « `fail` si pas de place ». `0 < extra` traduit « taille plus grande ».
- **`push` de taille 0** est accepté, comme l'`issue` restreint de la région vide (`ce_empty_region`). Le bloc vide ne bloque aucun `rewind` (`case_rewind_reading`).
- **`grow` stocke dans la destination enregistrée** pour le bloc (`Blk.dst`), qui peut ne plus être le détenteur du bloc après un `transfer` (cible `Moved`, permise par §77.2).
- **`mark` n'exige aucun droit**, la tâche disant « `mark : ok` ». Il ne modifie que des métadonnées. Une pile inexistante donne `reject`.
- **`rewind`** :
  - les blocs conservés sont ceux dont la base est sous le sommet de `m` ; un bloc agrandi qui chevauche ce sommet est conservé, et il est nécessairement inactif ;
  - une marque est vivante par appartenance à la liste de la pile ;
  - une pile inexistante donne `reject`.
- **Garde de §56 de `newStack`** : les arènes du noyau et les piles. Les pools de `HandlePool` ne sont pas combinés ici.

## Revue adverse

Méthode : quatre relecteurs indépendants, en lecture seule :
- `issue` ;
- `reset`, `newArena` et `writeShared` ;
- `DataStack` : marques et `rewind` ;
- `DataStack` : `grow`, octets, atteignabilité et cas.

Chacun est suivi d'un vérificateur chargé de réfuter ses constats en les reproduisant (exécutions `#eval` et `decide` sur des états atteints, fichiers de travail hors dépôt). Sur 16 constats, 12 sont confirmés (1 bloquant, 1 majeur, 10 mineurs) et 4 réfutés.

Les relecteurs n'ont trouvé aucun écart supplémentaire entre l'opération et la séquence. Les équivalences sont des `iff` vérifiés par la machine : dans un état atteint, seuls O8.5, la disponibilité et `Init` séparent `IssueR` de la séquence.

| Constat | Gravité retenue | Objet | Suite donnée |
|---|---|---|---|
| DS-1 | bloquant | `mark_no_aba` ne couvrait que la marque passée à `rewind`, pas les marques postérieures retirées avec elle ; l'unicité des marques n'était pas prouvée | `MarksWF` inclut l'unicité (`Nodup`), préservée par chaque pas ; `mark_no_aba` vaut pour toute marque de `m :: post` ; ajout de `rewind_removes` |
| Q1I-1 | majeur | disponibilité lue feuille par feuille (`Avail` du noyau), alors que §46 type `available` comme ensemble de régions ; lecture non signalée | docstrings de `IssueR` et `ce_empty_region` ; contre-exemple `ce_avail_leaf` ; écart 8, (e) 6, (f) 2 |
| Q1I-2 | mineur | l'existence de l'entrée (§77.1) n'était pas une clause | ajout de `IssueAtR` (recherche et réécriture de l'entrée) ; docstring de `IssueStaticR` |
| F1 | mineur | `ResetPreR` omettait la vivacité de l'entrée (§78.1) | vivacité ajoutée à `ResetPreR` ; l'hypothèse `hact` disparaît des théorèmes (`DerivePre` l'implique) ; ajout de `ResetAtPreR` |
| DS-2 | mineur | `above` ne contient pas toutes « les régions émises après `m` » : bloc agrandi, `rewind` intermédiaire | docstrings corrigées ; cas `case_rewind_reading` ; (f) 7 |
| DS-3 | mineur | `push` de taille 0 : bloc vide actif qui ne bloque pas `rewind` | docstring de `push` ; cas `case_rewind_reading` ; (f) |
| DS-4, Q2-DERIVED-NOT-RESTRICTED | mineur | `push` et `grow` utilisaient l'`issue` dérivé (destination `Init` acceptée), classé à tort parmi les décisions de représentation | `push` suit désormais les clauses statiques de l'`issue` restreint ; `grow` garde l'`issue` dérivé, nécessaire ; question (f) 6 |
| DS-5 | mineur | `PushStatic` omettait « destination hors région » avant `fail` | ajouté (avec « non `Init` ») ; cas `case_static_before_fail` |
| Q2-GROW-ORDER | mineur | `grow` rendait `fail` avant de contrôler `MetaRightM` | `MetaRightM` et la vivacité contrôlés avant la place ; cas `case_static_before_fail` |
| DS-6 | mineur | docstring de `rewind` incomplète (rejet faute d'exercice de `internal`) ; « réciproque » au lieu de contraposée | docstrings corrigées |
| Q2-GROW-SAME-BASE-WORDING | mineur | « ancien bloc inactif » et « même destination » n'étaient prouvés que pour l'état intermédiaire ou les métadonnées | `grow_same_base` énonce désormais, dans l'état d'arrivée, `b` inactif et l'autorité nouvelle détenue par la destination |
| Q1I-3 | réfuté | partie statique de §77.3 sans contrepartie | la lecture est documentée ; `NoEscape` est trivial pour un bloc d'origine `internal` |
| F2 | réfuté | équivalence non énoncée sous la lecture stricte de §78.3 | lecture documentée ; `reset_clause3_strict` |
| DS-7 | réfuté | blocs conservés par le filtre | règle documentée ; un bloc conservé qui chevauche est inactif |
| DS-8 | réfuté | destination de `grow` après `transfer` | comportement documenté ; décision ajoutée en (f) |

Une revue ciblée des corrections a suivi ; voir l'historique de la branche.
