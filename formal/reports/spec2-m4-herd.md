# Spec 2, jalon 4 — premiers tests herdtools7

Travail exploratoire, branche `formal/spec2-m4`, jamais mergé. Sources lues : le brief « premiers tests herdtools7 » et `ERN_Concurrency_Model_WC5.1.md`, clauses C31–C34, C39, C40, C42, C44, C48 et C53. Les tests, le script et les sorties brutes sont dans `formal/herd/`.

Ces tests portent sur le modèle de référence RC11, pas sur le fragment ERN : c'est le niveau « RC11 de référence » de WC5.1 C53. L'attendu vient du brief ; un écart est rapporté, pas corrigé.

## Outil

- **Version.** `herd7 -version` affiche `7.58, Rev: exported`. herdtools7 est installé par opam ; `herd7` n'est pas dans le `PATH`, d'où la variable `HERD7` de `run.sh`.
- **Répertoire des modèles.** `herd7 -libdir` affiche `~/.opam/default/share/herdtools7/herd`.
- **`rc11.cat`.** Présent. Ses contrôles sont ceux qu'attend le brief :
  - `irreflexive hb; eco? as coherence1` ;
  - `irreflexive (myrmw; eco) as coherencermw` ;
  - `empty (myrmw & (rb; mo)) as atomicity` ;
  - `acyclic psc as SC` ;
  - `acyclic (sb | rf) as no-thin-air` ;
  - courses : `undefined_unless empty dr as Dr`.
- **Options retenues.**
  - `-model rc11.cat` choisit le modèle. Il faut le donner : le modèle C par défaut de herd7 est `c11_partialSC.cat`.
  - `-skipcheck <nom>` saute un contrôle nommé (`-skipchecks` pour une liste). Aucune copie locale du modèle n'est faite.
- **Signal de course.** herd7 signale une exécution indéfinie par une ligne `Undef` et une ligne `Flag *undef*`, et sinon par `Ok` ou `No`. Pour vérifier que c'est le contrôle `Dr`, `MP+rlx+rlx` a été relancé avec `-skipcheck Dr` : `Undef` devient `Ok`, l'observation reste `Sometimes 1 2`.

La tâche 1 ne produit aucun fichier : rien n'a été commité pour elle.

## Résultats

Les lignes citées sont celles de `formal/herd/results/`. `Positive` et `Negative` comptent des exécutions (des témoins), pas des états : dans B1, un seul état satisfait la condition, mais deux exécutions y mènent.

| Test | Attendu (brief) | Obtenu | Verdict |
|---|---|---|---|
| A1 `MP+rel+acq` | `r0 = 1 ∧ r1 = 0` jamais ; aucune course | `No` ; `Observation MP+rel+acq Never 0 2` ; états `1:r0=0; 1:r1=-1;` et `1:r0=1; 1:r1=1;` | conforme |
| A2 `MP+rlx+rlx` | course signalée | `Undef`, `Flag *undef*` ; `Observation MP+rlx+rlx Sometimes 1 2` | conforme ; l'issue `1:r0=1; 1:r1=0;` est aussi observée |
| A3 `MP+sc+sc` | comme A1 | `No` ; `Observation MP+sc+sc Never 0 2` | conforme |
| A4 `LB+rlx` sous `rc11.cat` | `r0 = 1` dans les deux threads jamais | `No` ; `Observation LB+rlx Never 0 3` | conforme |
| A4 sans `no-thin-air` | cette issue observée | `Ok` ; état `0:r0=1; 1:r0=1;` ; `Observation LB+rlx Sometimes 1 3` | conforme |
| B1 `LOCK+xchg-acq+rel` | prise exclusive ; aucune course | `Ok` ; état `0:r0=0; 1:r0=0;` ; `Observation LOCK+xchg-acq+rel Sometimes 2 2` | course : conforme ; exclusivité : écart 1 |
| B2 `LOCK+xchg-acq+rlx` | prise toujours exclusive ; course | `Undef`, `Flag *undef*` ; `Observation LOCK+xchg-acq+rlx Sometimes 4 2` | course : conforme ; exclusivité : écart 1 |
| B3 `LOCK+xchg-rlx+rel` | prise toujours exclusive ; course | `Undef`, `Flag *undef*` ; `Observation LOCK+xchg-rlx+rel Sometimes 4 2` | course : conforme ; exclusivité : écart 1 |
| B4 `LOCK+sc+sc` | prise exclusive ; aucune course | `Ok` ; `Observation LOCK+sc+sc Sometimes 2 2` | course : conforme ; exclusivité : écart 1 |
| B5 `LOCK+cas-acq+rel` | comme B1 | `Ok` ; état `0:r0=1; 1:r0=1;` (ici `r0 = 1` veut dire « pris ») ; `Observation LOCK+cas-acq+rel Sometimes 2 2` | course : conforme ; exclusivité : écart 1 ; test adapté (écart 2) |
| B6 `LOCK3+xchg-acq+rel` | prise exclusive deux à deux ; aucune course | `Ok` ; 15 états ; `Observation LOCK3+xchg-acq+rel Sometimes 18 6` ; 388 s | course : conforme ; exclusivité : écart 1 |
| C1 `MIX+store-rlx+read` | course signalée | `Undef`, `Flag *undef*` ; `Observation MIX+store-rlx+read Sometimes 1 1` | conforme |
| C2 `AT+store+store` | aucune course | `Ok` ; `Observation AT+store+store Sometimes 1 1` | conforme |
| C3 `NA+write+write` | course signalée | `Undef`, `Flag *undef*` ; `Observation NA+write+write Sometimes 1 1` | conforme |

Les trois questions du brief :

1. **`release` et `acquire` ordonnent une donnée ordinaire à travers une lecture atomique ; `relaxed` non.** A1 et A3 n'ont ni l'issue interdite ni course ; A2 a les deux (WC5.1 C32 point 1, C40).
2. **Le mutex de référence ordonne deux sections critiques, et chacun des deux ordres est nécessaire.** B1, B4, B5 et B6 n'ont pas de course ; B2 (libération `relaxed`) et B3 (prise `relaxed`) en ont une (WC5.1 C48). L'exclusivité de la prise n'est pas mesurée par la condition du brief (écart 1).
3. **`no-thin-air` est ce qui exclut l'issue de *load buffering*.** Sous `rc11.cat` elle n'est jamais observée ; sans ce seul contrôle, elle l'est (WC5.1 C34).

## Groupe B : les trois propriétés

| Test | Exclusivité de la prise | Synchronisation mémoire | Absence de course |
|---|---|---|---|
| B1 | condition du brief observée (2 témoins), voir écart 1 ; contrôle annexe : chevauchement exclu par `atomicity` ou `coherencermw` | inférée de l'absence de course | oui (`Ok`) |
| B2 | condition observée (4 témoins) ; contrôle annexe : idem B1 | non : course | non (`Undef`) |
| B3 | condition observée (4 témoins) ; contrôle annexe : idem B1 | non : course | non (`Undef`) |
| B4 | condition observée (2 témoins) ; contrôle annexe : chevauchement exclu par `atomicity`, `coherencermw` ou `SC` | inférée de l'absence de course | oui (`Ok`) |
| B5 | condition observée (2 témoins, `r0 = 1`) ; contrôle annexe : idem B1 | inférée de l'absence de course | oui (`Ok`) |
| B6 | condition observée (18 témoins) ; contrôle annexe non lancé (388 s par exécution) | oui, observée sur les lectures de `d` | oui (`Ok`) |

**Exclusivité.** La condition du brief est observée partout, pour une raison qui ne tient pas à RC11 (écart 1). Un état final ne distingue pas deux prises successives de deux prises qui se chevauchent : dans les deux cas, chaque échange lit `0` et `l` finit à `0`.

Le contrôle annexe, hors brief, saute des contrôles de `rc11.cat` sans toucher aux tests. Les commandes sont `herd7 -model rc11.cat -skipchecks <liste> <test>.litmus`, lancées depuis `formal/herd/litmus/` ; les sorties ne sont pas commitées.

| Test | `-skipchecks` | Résultat |
|---|---|---|
| B1 | `atomicity` | `Ok`, `Sometimes 2 2` |
| B1 | `coherencermw` | `Ok`, `Sometimes 2 2` |
| B1 | `atomicity,coherencermw` | `Undef`, `Sometimes 10 6` |
| B2 | `atomicity,coherencermw` | `Undef`, `Sometimes 16 6` |
| B3 | `atomicity,coherencermw` | `Undef`, `Sometimes 16 6` |
| B4 | `atomicity,coherencermw` | `Ok`, `Sometimes 2 2` |
| B4 | `atomicity,coherencermw,SC` | `Undef`, `Sometimes 10 4` |
| B5 | `atomicity` | `Ok`, `Sometimes 2 2` |
| B5 | `coherencermw` | `Ok`, `Sometimes 2 2` |
| B5 | `atomicity,coherencermw` | `Undef`, `Sometimes 10 2` |

Lecture, raisonnement non formalisé : les témoins en plus sont les exécutions où les deux RMW lisent l'écriture initiale de `l`, donc où les deux sections critiques se chevauchent. La course qui apparaît sur `d` va dans ce sens : dans B1, elle n'existe que si aucune section n'est `hb`-avant l'autre. Sous `rc11.cat`, l'exclusivité tient donc à l'atomicité du RMW (`atomicity`, `coherencermw`), et pour `seq_cst` aussi à `SC`. Elle ne tient pas à l'ordre mémoire : pour B2 et B3 comme pour B1, sauter ces deux contrôles ajoute des témoins (16 au lieu de 4). C'est ce que dit le brief, mais herd7 ne le montre qu'à travers ces comptes ; les contrôles sautés un par un n'ont été essayés que sur B1 et B5.

**Synchronisation.** Dans B1 à B5, la seule case ordinaire est `d` : l'absence de course y équivaut à un `hb` entre les deux écritures de `d` quand les deux threads prennent le verrou. La colonne n'y est donc pas indépendante de la suivante. Une observation de plus, raisonnement non formalisé : B2 et B3 ont 4 témoins de la condition contre 2 pour B1. Sans `hb`, l'ordre de modification des deux écritures de `d` n'est plus contraint par la cohérence, d'où deux exécutions par ordre de prise.

B6 donne une observation indépendante, par les lectures de `d` dans les threads 1 et 2. Parmi les 15 états, aucun n'a les deux lecteurs qui prennent le verrou et lisent tous deux la valeur initiale `0` : quand les deux prennent le verrou, l'un des deux voit toujours une écriture faite dans une section critique. L'état final ne dit pas lequel a pris le verrou en premier.

## Écarts et tests refusés

1. **La condition d'exclusivité du brief n'est pas l'exclusion mutuelle.** Le brief la définit par « deux threads n'obtiennent jamais tous les deux `r0 = 0` », et attend « prise exclusive » pour B1, B4, B5 et B6, et « toujours exclusive » pour B2 et B3. Or un verrou libéré peut être repris : l'exécution où le thread 0 prend, écrit `d`, libère, puis où le thread 1 prend, donne `r0 = 0` aux deux. C'est l'exécution normale du protocole, et c'est sur elle que porte la question de la course. La condition est donc observée dans les six tests. Le test n'a pas été retouché ; la condition est encodée telle quelle. Proposition, à votre décision : un test sans libération (deux `exchange` seuls), où « les deux `r0 = 0` » mesure directement l'exclusivité ; ou bien retirer la colonne et s'appuyer sur le contrôle annexe.
2. **B5 : `&e` refusé.** La forme du brief, avec l'adresse d'une variable locale comme valeur attendue, est refusée :
   `Warning: File "cas.litmus", line 7, characters 54-55: unexpected '&' (in prog) (User error)`
   (sonde hors dépôt). Le test commité passe à la place un pointeur vers une case partagée ordinaire, une par thread (`e0`, `e1`), initialisée à `0`. Deux différences avec B1 : `r0` est le booléen rendu par la comparaison-échange, et vaut `1` quand le verrou est pris ; en cas d'échec, la comparaison-échange écrit la valeur lue dans `e0` ou `e1`, une écriture ordinaire que seul son thread fait, donc sans course possible. Aucun autre test n'a été refusé.
3. **Initialisation de `r1` à `-1` dans A1–A3 et B6**, pour que `r1` ait une valeur quand la lecture gardée ne s'exécute pas.
4. **C1 déclare `x` comme `atomic_int*` dans le thread 0 et `int*` dans le thread 1.** herd7 accepte ce mélange. Dans son dialecte C, `*x` est un accès non atomique quel que soit le type déclaré : une sonde avec `atomic_int*` dans les deux threads donne aussi `Undef`.
5. **Temps.** B6 prend 388 s, le reste moins d'une seconde.

## Ce que ces tests ne couvrent pas

- `spawn` et `join` : un test litmus lance tous ses threads ensemble, sans création ni attente. Les arêtes `sw` de WC5.1 C32 points 2 et 3 n'ont pas d'équivalent ici.
- Les autorités, `cap5`, `Encap5R` et tout ce qui relève de la machine d'autorités : herd7 ne voit que des accès mémoire.
- Le fragment ERN de WC5.1 C34 (`po`, `rf`, `mo`, `sw` par `rf` direct, `hb`) : seul RC11 est exécuté. Aucune inclusion ni équivalence avec ce fragment n'est testée (WC5.1 C53).
- Les séquences de libération (`rs` dans `rc11.cat`) : aucun test n'en dépend. Une prise réussie lit toujours `0`, écrit par une libération ou par l'initialisation, jamais par un `exchange`, qui écrit `1` (raisonnement non formalisé).
- Les barrières (`atomic_thread_fence`) : aucun test.
- Les accès multi-feuilles, les unités atomiques de taille différente d'un `int`, et la correspondance avec une cible (x86-TSO, ARM, POWER).
- `acq_rel` : aucun RMW du brief ne l'utilise.
- La reprise d'un mutex abandonné (`resetLock`, WC5.1 C49).

## Commits

| Commit | Tâche |
|---|---|
| — | 1 : relevé de l'installation, aucun fichier |
| `3b5e7ce` | 2 : les treize tests |
| `6f2b26e` | 3 : `run.sh` et les sorties brutes |
| `2682dfc` | 4 : `README.md` |
