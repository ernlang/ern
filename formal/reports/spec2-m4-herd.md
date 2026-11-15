# Spec 2, jalon 4 — tests herdtools7

Travail exploratoire, branche `formal/spec2-m4`, jamais mergé. Sources lues : les briefs « premiers tests herdtools7 » et « complément herdtools7 », et `ERN_Concurrency_Model_WC5.1.md`, clauses C31–C34, C39, C40, C42, C44, C48 et C53. Les tests, le script et les sorties brutes sont dans `formal/herd/`. Les écarts 1 à 5 de la première version de ce rapport sont acceptés. Le complément ajoute le groupe D (exclusivité de la prise, mesurée directement), le groupe E (séquence de libération) et rend le contrôle annexe reproductible.

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

Les lignes citées sont celles de `formal/herd/results/`, à `9ae6d9d`. `Positive` et `Negative` comptent des exécutions (des témoins), pas des états : dans B1, un seul état satisfait la condition, mais deux exécutions y mènent.

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
| B6 `LOCK3+xchg-acq+rel` | prise exclusive deux à deux ; aucune course | `Ok` ; 15 états ; `Observation LOCK3+xchg-acq+rel Sometimes 18 6` ; 382 s | course : conforme ; exclusivité : écart 1 |
| C1 `MIX+store-rlx+read` | course signalée | `Undef`, `Flag *undef*` ; `Observation MIX+store-rlx+read Sometimes 1 1` | conforme |
| C2 `AT+store+store` | aucune course | `Ok` ; `Observation AT+store+store Sometimes 1 1` | conforme |
| C3 `NA+write+write` | course signalée | `Undef`, `Flag *undef*` ; `Observation NA+write+write Sometimes 1 1` | conforme |
| E1 `RS+rel+rlx` | aucune course ; `r0 = 2 ∧ r1 = 0` jamais | `No` ; états `1:r0=0; 1:r1=-1;`, `1:r0=1; 1:r1=-1;`, `1:r0=2; 1:r1=1;` ; `Observation RS+rel+rlx Never 0 3` | conforme |

Le groupe D a sa propre table, plus bas.

Les trois questions du brief :

1. **`release` et `acquire` ordonnent une donnée ordinaire à travers une lecture atomique ; `relaxed` non.** A1 et A3 n'ont ni l'issue interdite ni course ; A2 a les deux (WC5.1 C32 point 1, C40).
2. **Le mutex de référence ordonne deux sections critiques, et chacun des deux ordres est nécessaire.** B1, B4, B5 et B6 n'ont pas de course ; B2 (libération `relaxed`) et B3 (prise `relaxed`) en ont une (WC5.1 C48). L'exclusivité de la prise n'est pas mesurée par la condition du premier brief (écart 1) ; le groupe D la mesure : elle tient sous `rc11.cat`.
3. **`no-thin-air` est ce qui exclut l'issue de *load buffering*.** Sous `rc11.cat` elle n'est jamais observée ; sans ce seul contrôle, elle l'est (WC5.1 C34).

## Groupe B : les trois propriétés

| Test | Exclusivité de la prise | Synchronisation mémoire | Absence de course |
|---|---|---|---|
| B1 | voir le groupe D (`XCHG+acq`) ; condition du premier brief observée (2 témoins), écart 1 | inférée de l'absence de course | oui (`Ok`) |
| B2 | voir le groupe D (`XCHG+acq`) ; condition observée (4 témoins) | non : course | non (`Undef`) |
| B3 | voir le groupe D (`XCHG+rlx`) ; condition observée (4 témoins) | non : course | non (`Undef`) |
| B4 | voir le groupe D (`XCHG+sc`) ; condition observée (2 témoins) | inférée de l'absence de course | oui (`Ok`) |
| B5 | voir le groupe D ; condition observée (2 témoins, `r0 = 1`) | inférée de l'absence de course | oui (`Ok`) |
| B6 | voir le groupe D ; condition observée (18 témoins) | oui, observée sur les lectures de `d` | oui (`Ok`) |

Le groupe D teste l'échange seul, sans libération : il porte sur la prise de B1 et B2 (`acquire`), de B3 (`relaxed`) et de B4 (`seq_cst`). B5 prend le verrou par comparaison-échange, que le groupe D ne teste pas.

**Exclusivité.** Dans B1 à B6, la condition du brief est observée, pour une raison qui ne tient pas à RC11 (écart 1). Un état final ne distingue pas deux prises successives de deux prises qui se chevauchent : dans les deux cas, chaque échange lit `0` et `l` finit à `0`.

Le contrôle annexe saute des contrôles de `rc11.cat` sans toucher aux tests. Il fait maintenant partie de `run.sh`, et ses sorties sont commitées sous `results/<test>+skip-<contrôles>.txt`. B6 en reste exclu, à cause de sa durée.

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

Lecture, raisonnement non formalisé : les témoins en plus sont les exécutions où les deux RMW lisent l'écriture initiale de `l`, donc où les deux sections critiques se chevauchent. La course qui apparaît sur `d` va dans ce sens : dans B1, elle n'existe que si aucune section n'est `hb`-avant l'autre. Sous `rc11.cat`, l'exclusivité tient donc à l'atomicité du RMW (`atomicity`, `coherencermw`), et pour `seq_cst` aussi à `SC`. Elle ne tient pas à l'ordre mémoire : pour B2 et B3 comme pour B1, sauter ces deux contrôles ajoute des témoins (16 au lieu de 4). Le groupe D le montre directement.

**Synchronisation.** Dans B1 à B5, la seule case ordinaire est `d` : l'absence de course y équivaut à un `hb` entre les deux écritures de `d` quand les deux threads prennent le verrou. La colonne n'y est donc pas indépendante de la suivante. Une observation de plus, raisonnement non formalisé : B2 et B3 ont 4 témoins de la condition contre 2 pour B1. Sans `hb`, l'ordre de modification des deux écritures de `d` n'est plus contraint par la cohérence, d'où deux exécutions par ordre de prise.

B6 donne une observation indépendante, par les lectures de `d` dans les threads 1 et 2. Parmi les 15 états, aucun n'a les deux lecteurs qui prennent le verrou et lisent tous deux la valeur initiale `0` : quand les deux prennent le verrou, l'un des deux voit toujours une écriture faite dans une section critique. L'état final ne dit pas lequel a pris le verrou en premier.

## Groupe D : exclusivité de la prise

Deux threads, un seul échange chacun, ni libération ni donnée. Sans libération, `l` ne revient jamais à `0` : « les deux `r0 = 0` » veut dire que les deux échanges lisent l'écriture initiale, donc deux prises qui se chevauchent. Chaque case donne l'attendu du brief, puis l'obtenu (`Observation`).

| Test | `rc11.cat` | sans `atomicity` | sans `coherencermw` | sans `atomicity` ni `coherencermw` | sans ces deux ni `SC` |
|---|---|---|---|---|---|
| D1 `XCHG+acq` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | observée ; `Sometimes 2 4` | — |
| D2 `XCHG+rlx` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | observée ; `Sometimes 2 4` | — |
| D3 `XCHG+sc` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | jamais ; `Never 0 2` | observée ; `Sometimes 2 2` |

Verdict : conforme dans les treize cases où le brief donne un attendu. Quand la condition est observée, l'état listé est `0:r0=0; 1:r0=0;`.

- **Ce que le groupe D établit.** Sous `rc11.cat`, deux échanges ne prennent jamais le verrou ensemble, quel que soit l'ordre mémoire. L'exclusivité tient à l'atomicité du RMW : chacun des contrôles `atomicity` et `coherencermw` suffit seul à l'assurer. Pour `seq_cst`, `SC` l'assure aussi. `D1` et `D2` donnent les mêmes sorties : l'ordre `acquire` n'y joue aucun rôle.
- **D1 est l'ancien B7.** Le test `LOCK+xchg-acq+norel`, ajouté sur votre accord avant ce complément, est exactement D1. Il a été renommé `XCHG+acq` au lieu d'être dupliqué (`5c27f9b`), et ses anciennes sorties ont été retirées.

## Divergence : séquence de libération

E1 (`RS+rel+rlx`) : le thread 0 écrit `d`, puis fait `store(f, 1, release)`, puis une écriture atomique non-RMW `store(f, 2, relaxed)`. Le thread 1 lit `f` en `acquire` et, s'il lit `2`, lit `d`.

- **Sous `rc11.cat`.** Aucune course, et la lecture de `d` voit toujours `1` quand `r0 = 2` (`Never 0 3`). La séquence de libération de `rc11.cat` est `rs = [W]; (sb & loc)?; [W & …]; (rf; myrmw)*`. Le facteur `(sb & loc)?` y fait entrer l'écriture atomique non-RMW suivante du même thread sur la même case. La lecture `acquire` de `2` synchronise donc avec l'écriture `release`.
- **Sous la forme retenue par WC5.1 C48.** C48 prend la forme C++20, où seuls les RMW intermédiaires prolongent une séquence de libération, et pas une écriture atomique non-RMW du même thread. Sous cette forme, aucune arête `sw` ne relie l'écriture `release` à la lecture de `2`, et la lecture de `d` est en course avec l'écriture de `d`. Le fragment Lean initial, qui ne retient que l'arête par `rf` direct (C32 point 1, C48), donne la même course : la lecture `acquire` de `2` lit une écriture `relaxed`. Raisonnement non formalisé : aucun modèle de cette forme n'a été exécuté, et `rc11.cat` n'a pas été modifié. **Mise à jour :** cette forme a depuis été exécutée (`rc11-rs20.cat`), voir « Contrôles ciblés avant validation ».
- **Ce que C48 demande.** Que cette différence avec `rc11.cat` soit dite lors de la comparaison. Elle l'est ici ; rien n'est corrigé.

## Écarts et tests refusés

1. **La condition d'exclusivité du brief n'est pas l'exclusion mutuelle.** Le brief la définit par « deux threads n'obtiennent jamais tous les deux `r0 = 0` », et attend « prise exclusive » pour B1, B4, B5 et B6, et « toujours exclusive » pour B2 et B3. Or un verrou libéré peut être repris : l'exécution où le thread 0 prend, écrit `d`, libère, puis où le thread 1 prend, donne `r0 = 0` aux deux. C'est l'exécution normale du protocole, et c'est sur elle que porte la question de la course. La condition est donc observée dans les six tests. Le test n'a pas été retouché ; la condition est encodée telle quelle. Écart accepté : c'est une erreur du premier brief. B1 à B6 restent tels quels ; le groupe D mesure l'exclusivité directement.
2. **B5 : `&e` refusé.** La forme du brief, avec l'adresse d'une variable locale comme valeur attendue, est refusée :
   `Warning: File "cas.litmus", line 7, characters 54-55: unexpected '&' (in prog) (User error)`
   (sonde hors dépôt). Le test commité passe à la place un pointeur vers une case partagée ordinaire, une par thread (`e0`, `e1`), initialisée à `0`. Deux différences avec B1 : `r0` est le booléen rendu par la comparaison-échange, et vaut `1` quand le verrou est pris ; en cas d'échec, la comparaison-échange écrit la valeur lue dans `e0` ou `e1`, une écriture ordinaire que seul son thread fait, donc sans course possible. Aucun autre test n'a été refusé.
3. **Initialisation de `r1` à `-1` dans A1–A3, B6 et E1**, pour que `r1` ait une valeur quand la lecture gardée ne s'exécute pas.
4. **C1 déclare `x` comme `atomic_int*` dans le thread 0 et `int*` dans le thread 1.** herd7 accepte ce mélange. Dans son dialecte C, `*x` est un accès non atomique quel que soit le type déclaré : une sonde avec `atomic_int*` dans les deux threads donne aussi `Undef`.
5. **Temps.** B6 prend 382 s, chaque autre exécution moins d'une seconde.

Aucun écart nouveau dans les groupes D et E : tous les attendus du complément sont obtenus.

## Ce que ces tests ne couvrent pas

- `spawn` et `join` : un test litmus lance tous ses threads ensemble, sans création ni attente. Les arêtes `sw` de WC5.1 C32 points 2 et 3 n'ont pas d'équivalent ici.
- Les autorités, `cap5`, `Encap5R` et tout ce qui relève de la machine d'autorités : herd7 ne voit que des accès mémoire.
- Le fragment ERN de WC5.1 C34 (`po`, `rf`, `mo`, `sw` par `rf` direct, `hb`) : seuls RC11 et sa variante `rc11-rs20.cat` sont exécutés. Aucune inclusion ni équivalence avec ce fragment n'est testée (WC5.1 C53).
- Les barrières (`atomic_thread_fence`) : aucun test.
- Les accès multi-feuilles, les unités atomiques de taille différente d'un `int`, et la correspondance avec une cible (x86-TSO, ARM, POWER) : les tests d'architecture des contrôles ciblés sont des exemples sur des modèles, pas une correspondance.
- `acq_rel` : aucun RMW des briefs ne l'utilise.
- La comparaison-échange sans libération : le groupe D ne teste que l'échange.
- La reprise d'un mutex abandonné (`resetLock`, WC5.1 C49).

## Contrôles ciblés avant validation

Brief « contrôles ciblés avant validation de la candidate ». Document de référence, non commité : `ERN_Concurrency_Model_WC6.2_Review_Candidate.md`, sha256 `71a15b26e1772546ba4db1b0159d493c6bbe2b59bee2a2e5f2271021e5c4537a` (vérifiée). Son titre interne dit encore « Working Candidate 6.1 ». Clauses lues : C32, C33, C34, C40, C48, C49 et C50, et les lignes `OB-C02`, `OB-C22`, `OB-C23`, `OB-C26`, `OB-C27`.

Aucun travail Lean. Aucun fichier hors de `formal/herd/` et de ce rapport n'est modifié. L'attendu vient du brief ; un écart est rapporté, pas corrigé.

| Question | Obligation | Réponse obtenue |
|---|---|---|
| 1. Sous la séquence de release de C48, quels verdicts changent ? | `OB-C23`, `OB-C02` | E1 seul : course signalée, condition observée. Les 19 autres tests gardent leurs lignes d'état et d'observation. |
| 2. `SCConsistent` (le `psc` de RC11) permet-il le résultat x86 qui mêle `release` et `seq_cst` ? | `OB-C23`, `OB-C26` | Oui sous `rc11.cat` : F2 observé, sans course. F1, tout en `seq_cst`, reste interdit par `SC`. |
| 3. *Load buffering* sur les modèles d'architecture ? | `OB-C22` | AArch64 et PPC : permis sans dépendance, interdit avec une dépendance de contrôle constatée. x86 : interdit. |

### Modèle `rc11-rs20.cat`

`formal/herd/models/rc11-rs20.cat` est une copie du `rc11.cat` installé. L'en-tête d'attribution est conservé. La ligne `rs` du fichier installé (ligne 18) est exactement celle du brief. Le `diff`, commité dans `formal/herd/results/rc11-rs20.diff` :

```
--- rc11.cat
+++ rc11-rs20.cat
@@ -1,3 +1,4 @@
+(* ERN change: C++20-form release sequence, (sb & loc)? removed from rs (ERN WC6.2 C48). *)
 C RC11
 
 (*
@@ -15,7 +16,7 @@
 
 let rb = (rf^-1; mo) \ id
 let eco = (rf | mo | rb)+
-let rs = [W]; (sb & loc)?; [W & (RLX | REL | ACQ_REL | ACQ | SC)]; (rf; myrmw)*
+let rs = [W]; [W & (RLX | REL | ACQ_REL | ACQ | SC)]; (rf; myrmw)*
 let sw = [(REL | ACQ_REL | SC)]; ([F]; sb)?; rs; rf; [R & (RLX | REL | ACQ | ACQ_REL | SC)]; (sb; [F])?; [(ACQ | ACQ_REL | SC)]
 let hb = (sb | sw)+
 
```

`scb`, `psc` et les contrôles sont inchangés. Le chargement a été vérifié par `herd7 -debug files -model formal/herd/models/rc11-rs20.cat …` :

```
Found and opened: './formal/herd/models/rc11-rs20.cat'
Found and opened: '~/.opam/default/share/herdtools7/herd/stdlib.cat'
Found and opened: '~/.opam/default/share/herdtools7/herd/cos.cat'
```

`include "cos.cat"` est donc résolu dans le répertoire d'installation. La licence de herdtools7 (CeCILL-B, `LICENSE.txt` de la distribution) est notée dans le README.

**Lien avec C34.** Sans barrière, le `psc` de `rc11.cat` (lignes 24 à 27) se réduit à `[SC]; scb; [SC]`, avec `scb = sb | sbl; hb; sbl | hbl | mo | rb`. C'est la forme sans barrière que C34 définit. Les tests ne contiennent aucune barrière.

### Tests en C sous les deux modèles

Les sorties sont celles de `formal/herd/results/` : `<test>.txt` sous `rc11.cat`, `<test>+rs20.txt` sous `rc11-rs20.cat`. Pour les 16 tests des groupes A à D, les deux sorties sont identiques ligne à ligne, ligne `Time` exceptée (vérifié par `diff` en excluant cette ligne). La ligne d'état est `Ok`, `No` ou `Undef` ; une course ajoute `Flag *undef*`.

| Test | `rc11.cat` : attendu | `rc11.cat` : obtenu | `rc11-rs20.cat` : attendu | `rc11-rs20.cat` : obtenu | Verdict |
|---|---|---|---|---|---|
| A1 `MP+rel+acq` | déjà obtenu | `No` ; `Never 0 2` | même ligne d'état et d'observation | `No` ; `Never 0 2` | conforme |
| A2 `MP+rlx+rlx` | déjà obtenu | `Undef` ; `Sometimes 1 2` | idem | `Undef` ; `Sometimes 1 2` | conforme |
| A3 `MP+sc+sc` | déjà obtenu | `No` ; `Never 0 2` | idem | `No` ; `Never 0 2` | conforme |
| A4 `LB+rlx` | déjà obtenu | `No` ; `Never 0 3` | idem | `No` ; `Never 0 3` | conforme |
| B1 `LOCK+xchg-acq+rel` | déjà obtenu | `Ok` ; `Sometimes 2 2` | idem | `Ok` ; `Sometimes 2 2` | conforme |
| B2 `LOCK+xchg-acq+rlx` | déjà obtenu | `Undef` ; `Sometimes 4 2` | idem | `Undef` ; `Sometimes 4 2` | conforme |
| B3 `LOCK+xchg-rlx+rel` | déjà obtenu | `Undef` ; `Sometimes 4 2` | idem | `Undef` ; `Sometimes 4 2` | conforme |
| B4 `LOCK+sc+sc` | déjà obtenu | `Ok` ; `Sometimes 2 2` | idem | `Ok` ; `Sometimes 2 2` | conforme |
| B5 `LOCK+cas-acq+rel` | déjà obtenu | `Ok` ; `Sometimes 2 2` | idem | `Ok` ; `Sometimes 2 2` | conforme |
| B6 `LOCK3+xchg-acq+rel` | déjà obtenu | `Ok` ; `Sometimes 18 6` | idem | `Ok` ; `Sometimes 18 6` ; 376 s | conforme |
| C1 `MIX+store-rlx+read` | déjà obtenu | `Undef` ; `Sometimes 1 1` | idem | `Undef` ; `Sometimes 1 1` | conforme |
| C2 `AT+store+store` | déjà obtenu | `Ok` ; `Sometimes 1 1` | idem | `Ok` ; `Sometimes 1 1` | conforme |
| C3 `NA+write+write` | déjà obtenu | `Undef` ; `Sometimes 1 1` | idem | `Undef` ; `Sometimes 1 1` | conforme |
| D1 `XCHG+acq` | déjà obtenu | `No` ; `Never 0 2` | idem | `No` ; `Never 0 2` | conforme |
| D2 `XCHG+rlx` | déjà obtenu | `No` ; `Never 0 2` | idem | `No` ; `Never 0 2` | conforme |
| D3 `XCHG+sc` | déjà obtenu | `No` ; `Never 0 2` | idem | `No` ; `Never 0 2` | conforme |
| E1 `RS+rel+rlx` | aucune course ; condition jamais observée | `No` ; `Never 0 3` | course signalée ; `1:r0=2 /\ 1:r1=0` observée | `Undef`, `Flag *undef*` ; état `1:r0=2; 1:r1=0;` ; `Sometimes 1 3` | conforme |
| E2 `RS+rel+rmw` | aucune course ; condition jamais observée | `No` ; états `2:r0=0; 2:r1=-1;`, `2:r0=1; 2:r1=-1;`, `2:r0=2; 2:r1=1;` ; `Never 0 6` | comme sous `rc11.cat` | `No` ; mêmes états ; `Never 0 6` | conforme |
| F1 `SB+rfi+sc+sc` | condition jamais observée | `No` ; `Never 0 3` | condition jamais observée | `No` ; `Never 0 3` | conforme |
| F1 avec `-skipcheck SC` | condition observée | `Ok` ; état `0:r1=1; 0:r2=0; 1:r1=1; 1:r2=0;` ; `Sometimes 1 3` | — | — | conforme |
| F2 `SB+rfi+rel+sc` | condition observée ; aucune course | `Ok`, aucun `Flag` ; état `0:r1=1; 0:r2=0; 1:r1=1; 1:r2=0;` ; `Sometimes 1 3` | comme sous `rc11.cat` | `Ok`, aucun `Flag` ; `Sometimes 1 3` | conforme |

Les 20 tests et la passe de F1 sans `SC` donnent l'attendu du brief, sans écart.

- **Question 1.** Sous la séquence de release de C48, seul E1 change. L'issue où la lecture `acquire` lit `2`, écrit par `store(f, 2, relaxed)`, puis lit `d = 0` devient possible, et la lecture de `d` est en course avec son écriture. C'est la divergence décrite plus haut, cette fois exécutée. E2 montre que le prolongement par un RMW (`(rf; myrmw)*`) est conservé : quand `r0 = 2`, `r1 = 1` dans les deux modèles.
- **Question 2.** Sous `rc11.cat`, `SC` interdit F1 (l'issue apparaît dès que ce seul contrôle est sauté) mais permet F2, sans course. Le `psc` de RC11, qui est la règle `SCConsistent` de C34, admet donc le résultat de l'exemple de l'issue LWG 3941, où les écritures sont `release` et les lectures `seq_cst`. `SB+rfi-X86` montre la même issue permise par `x86tso-mixed.cat`, sous l'hypothèse de traduction des tests d'architecture (écriture `release` et lecture `seq_cst` traduites par des accès simples). Ce n'est pas une preuve de correction de la compilation vers x86.

### Tests d'architecture

**Modèles.** Ceux que herd7 prend par défaut : `herd7 -help` affiche « defaults X86=x86tso.cat, X86_64=x86tso-mixed.cat, PPC=ppc.cat, ARM=arm.cat, AArch64=aarch64.cat, … », et `-debug files` le confirme sur chaque test. Ils sont passés explicitement par `-model` dans `run.sh`.

**Hypothèse de traduction de ces tests.** C'est la traduction usuelle, pas une décision d'ERN : une lecture ou une écriture `relaxed` ou `release` devient une lecture ou une écriture machine simple ; sur x86, une lecture `seq_cst` devient une lecture simple.

**Formes.** Les formes AArch64 et PPC du brief sont acceptées telles quelles. Le brief ne donnait pas de forme x86 : `LB-X86` et `SB+rfi-X86` sont écrits en `X86_64`, syntaxe AT&T (`movl (x),%eax`, `movl $1,(y)`), registres `rax` et `rbx` dans la condition.

| Test | Modèle | Attendu | Obtenu | Verdict | Ligne du modèle qui justifie |
|---|---|---|---|---|---|
| `LB-A64` | `aarch64.cat` | observée | `Ok` ; état `0:X0=1; 1:X0=1;` ; `Sometimes 1 3` | conforme | rien n'ordonne la lecture avant l'écriture. Les arêtes de `dob` (`aarch64hwreqs.cat:93-99`) passent par `addr`, `data` ou `ctrl` : `ctrl` est absente (sonde), et l'écriture ne dépend de la lecture ni par son adresse ni par sa valeur (raisonnement). Les deux dernières (:100-101) partent de lectures implicites (`Imp & TTD`, `Imp & Tag`). Le test n'a ni barrière ni accès `acquire` ou `release`. |
| `LB+ctrls-A64` | `aarch64.cat` | jamais | `No` ; `Never 0 3` | conforme | `aarch64hwreqs.cat:96` `\| ctrl; [Exp & W \| HU \| TLBI \| DC.CVAU \| IC]` dans `dob` (:93) ; `dob` dans `lob` (:166) ; `lob` dans `local-hw-reqs` (:175-176) ; `aarch64.cat:95` `let hw-reqs = local-hw-reqs \| haz-ob` ; `:154-155` `ob` ; `:160` `irreflexive ob as external` |
| `LB-PPC` | `ppc.cat` | observée | `Ok` ; état `0:r1=1; 1:r1=1;` ; `Sometimes 1 3` | conforme | `ppc.cat:26-28` : aucun de `ci0`, `ii0`, `cc0` ne relie une lecture à une écriture d'une autre case sans dépendance ; aucune barrière |
| `LB+ctrls-PPC` | `ppc.cat` | jamais | `No` ; `Never 0 3` | conforme | `ppc.cat:28` `let cc0 = dd \| po-loc \| ctrl \| addrpo` ; `ppo.cat:7` `cc` contient `cc0`, `:8` `ic` contient `cc`, `:12` `ppoW = ic & (R * W)` ; `ppc-checks.cat:7` `let hb = ppo \| fence \| rfe`, `:8` `acyclic hb as thinair` |
| `LB-X86` | `x86tso-mixed.cat` | jamais | `No` ; `Never 0 3` | conforme | `x86tso-mixed.cat:13` `let rec lob = po \ ([W]; po; [R])` garde lecture → écriture ; `:31` `irreflexive ob as external` |
| `SB+rfi-X86` | `x86tso-mixed.cat` | observée | `Ok` ; état `0:rax=1; 0:rbx=0; 1:rax=1; 1:rbx=0;` ; `Sometimes 1 3` | conforme | `:13` retire écriture → lecture de `lob` ; `:10` `let obs = rfe \| fre \| coe` ne contient pas `rfi` |

Le brief donnait de mémoire trois raisons. Elles existent sous la forme dite, avec ces précisions :

- AArch64 : l'arête est `ctrl; [Exp & W …]` dans `dob`, définie dans `aarch64hwreqs.cat`, inclus par `aarch64.cat`.
- PPC : `ctrl` entre dans `cc0`, et `ppo` en tire la paire lecture → écriture par `ic`. Le contrôle qui exclut le cycle s'appelle `thinair`.
- x86 : TSO n'est pas une ligne unique. Ce sont `lob` (`po` moins écriture → lecture) et l'absence de `rfi` dans `obs`.

### Constat de la relation `ctrl`

**Moyen retenu : deux modèles de sonde**, réduits à deux drapeaux et sans contrainte. Leurs sorties sont commitées sous `formal/herd/results/<test>+probe-ctrl.txt`.

- `CtrlToWrite` : `flag ~empty (ctrl & (R * W))`.
- `ReadWriteWithoutCtrl` : `flag ~empty (((R * W) & po) \ ctrl)`.

Il en faut deux, un par architecture :

- **`probe-ctrl.cat`, pour PPC.** `ppc.cat` lit la relation `ctrl` que calcule herd7, sans la redéfinir (seule occurrence : `ppc.cat:28`).
- **`probe-ctrl-a64.cat`, pour AArch64.** `aarch64.cat` commence par `catdep` (« the cat file computes dependencies ») et définit sa propre relation : `aarch64deps.cat:70` `let ctrl = [Exp & R]; basic-dep; [BCC]; po`. La sonde inclut ce fichier et commence elle aussi par `catdep`.

Dans chaque test, chaque thread a une lecture mémoire et une écriture mémoire qui la suit en `po`. `ReadWriteWithoutCtrl` jamais levé veut donc dire que la paire de **chaque** thread est en `ctrl`, dans toutes les exécutions.

| Test | Sonde | Attendu | Obtenu | Verdict |
|---|---|---|---|---|
| `LB+ctrls-A64` | `probe-ctrl-a64.cat` | `ctrl` présente dans chaque thread | `Flag CtrlToWrite` ; `ReadWriteWithoutCtrl` jamais levé | conforme |
| `LB+ctrls-PPC` | `probe-ctrl.cat` | `ctrl` présente dans chaque thread | `Flag CtrlToWrite` ; `ReadWriteWithoutCtrl` jamais levé | conforme |
| `LB-A64` | `probe-ctrl-a64.cat` | `ctrl` absente | `Flag ReadWriteWithoutCtrl` ; `CtrlToWrite` jamais levé | conforme |
| `LB-PPC` | `probe-ctrl.cat` | `ctrl` absente | `Flag ReadWriteWithoutCtrl` ; `CtrlToWrite` jamais levé | conforme |

La dépendance est constatée dans les deux tests `LB+ctrls`. Leurs verdicts comptent donc.

**Première forme de la sonde AArch64, refusée.** Elle n'avait `catdep` que dans le fichier inclus. Sur `LB+ctrls-A64`, elle levait `ReadWriteWithoutCtrl` et jamais `CtrlToWrite` : la relation `ctrl` était vide. Le défaut venait de la sonde, pas du test. herd7 ne calcule les dépendances au niveau des registres que si `catdep` figure dans le fichier de modèle principal. Une sonde qui inclut `aarch64.cat` tout entier depuis un autre fichier perd de même l'interdiction : `LB+ctrls-A64` y devient `Sometimes 1 3`. Ces sondes de diagnostic sont restées hors dépôt. Les tests n'ont pas été modifiés.

### Conséquence pour `OB-C22` et `OB-C27`

- C34 interdit le résultat de *load buffering*, avec ou sans dépendance, par `acyclic(po ∪ rf)`. A4 le montre sous `rc11.cat` (`Never 0 3`), et l'issue apparaît quand ce seul contrôle est sauté. Sous `rc11-rs20.cat`, A4 est inchangé.
- `LB-A64` et `LB-PPC` sont observés. Sous l'hypothèse de traduction de ces tests, une traduction des accès `relaxed` par des accès machine simples ne respecte pas C34 selon `aarch64.cat` et selon `ppc.cat`. C'est un constat sur ces modèles, pas une mesure sur du matériel.
- `LB+ctrls-A64` et `LB+ctrls-PPC` ne sont jamais observés, la dépendance étant constatée. Ces deux programmes machine sont interdits par leur modèle, et rien de plus. Cela ne montre pas :
  - qu'un schéma de compilation existe pour tous les programmes ;
  - qu'il est correct ;
  - qu'un compilateur conserve la dépendance à travers ses optimisations ;
  - ce qu'il coûte.
- `LB-X86` et `SB+rfi-X86` sont des exemples sur un modèle, pas une preuve de correction de la compilation vers x86.
- `OB-C22` et `OB-C27` restent ouvertes.

### Écarts et tests refusés

- **Aucun test refusé par herd7.** `atomic_fetch_add_explicit` est accepté sous forme d'instruction, sans résultat lu ; la comparaison-échange de repli n'a pas servi.
- **Forme x86.** Le brief ne la donnait pas ; elle est écrite en syntaxe AT&T (voir « Formes »).
- **Deux sondes au lieu d'une.** `probe-ctrl.cat` sert pour PPC, `probe-ctrl-a64.cat` pour AArch64 ; la raison est donnée plus haut. La première forme de la sonde AArch64 est rapportée ci-dessus.
- **Relance des tests existants.** `run.sh` a été exécuté en entier deux fois, aux tâches 3 et 4, et relance aussi les sorties déjà commitées. Seules les lignes `Time` ont changé : B5 sous `rc11.cat` (0,04 s puis 0,03 s), B6 sous `rc11.cat` (382,49 s, puis 383,10 s et 386,68 s) et, à la seconde exécution, B6 sous `rc11-rs20.cat` (375,67 s puis 376,18 s). Les sorties commitées ont été restaurées à chaque fois.
- **Durée.** Une exécution complète de `run.sh` prend environ 13 minutes, dont deux fois B6.

**Test proposé, non ajouté.** Le brief ne demande pas de passer F1 sur x86. Pour compléter la question 2, on pourrait le faire sous la traduction usuelle des écritures `seq_cst`, `xchg` ou `mov` suivi de `mfence`.

### Ce que ces contrôles ne couvrent pas

- Aucun modèle ERN n'est exécuté. `rc11-rs20.cat` est RC11 avec la séquence de release de C48, pas le modèle de WC6.2. L'inclusion attendue des exécutions RC11 dans les exécutions ERN reste une hypothèse non prouvée (C34, `OB-C23`, `OB-C26`).
- Aucune mesure sur du matériel ; aucun compilateur.
- L'existence, la correction et le coût d'une traduction qui garde une dépendance.
- Le coût du no-thin-air en code généré (hors du brief).
- Les barrières `seq_cst`, absentes de C34 comme des tests.

## Commits

| Commit | Tâche |
|---|---|
| — | 1 : relevé de l'installation, aucun fichier |
| `3b5e7ce` | 2 : les treize tests |
| `6f2b26e` | 3 : `run.sh` et les sorties brutes |
| `2682dfc` | 4 : `README.md` |
| `c4c5d15` | rapport |
| `e28df67` | B7, ses deux exécutions dans `run.sh` et ses sorties |
| `af9ebf3` | README et rapport pour B7 |
| `5c27f9b` | complément, 1 : groupe D, B7 devenu `XCHG+acq` |
| `7503368` | complément, 2 : groupe E |
| `9ae6d9d` | complément, 3 : exécutions avec contrôles sautés dans `run.sh`, sorties |
| `63d6f21` | contrôles ciblés, 1 : `rc11-rs20.cat`, son `diff`, note de licence dans le README |
| `e558189` | contrôles ciblés, 2 : E2, F1, F2 |
| `e989941` | contrôles ciblés, 3 : `run.sh`, exécutions sous les deux modèles, sorties |
| `f781284` | contrôles ciblés, 4 : tests d'architecture, sondes `ctrl`, `run.sh`, sorties |
| ce commit | contrôles ciblés, 5 : README et rapport |
