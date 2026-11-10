# Spec 2, jalon 3 — passe de clôture

Branche `formal/spec2-m3`. Exploratoire, jamais mergée ; rien n'est poussé, aucune PR.

- **Sources :** `ERN_WC4.md` (WC4 corrigée, celle du jalon 3) ; `corpus-spec2-m3.md` v3, verdicts de référence ; Spec 1 `specs/ERN_Memory_Model_Specification_v0.1.md`.
- **Fichiers non modifiés :** `specs/`, `AGENTS.md`, `CLAUDE.md`, `formal/DESIGN.md`, `formal/Ern/MemoryModel/`.
- **Invariants inchangés :** rien n'est ajouté à `Encap`, `SyncInv`, `ArenaInvC` ni `AdminSep`.
- **Hors périmètre :** P1 et P3 restent des choix du modèle exploratoire. P7 reste ouvert.
- **Index consolidé :** `spec2-m3.md`, partie B, mis à jour en place.

Chemins relatifs à `formal/Ern/Concurrency/`. Numéros de ligne à `bf36d25`.

## Commits

| Commit | Tâche |
|---|---|
| `d007962` | 1 — S10 dans le noyau séquentiel |
| `faa2a0f` | 2 — exécution de S3 réalisée jusqu'à `issue` |
| `eb017a5` | 3 — `ArenaReg.unique` |
| `8903979` | 4 — témoins de passation |
| `bf36d25` | 5 — docstrings du corpus v3, suite concurrente de S10, `W_C22_2_cycle` |
| commit suivant | rapports : `spec2-m3.md` en place, ce fichier |

## Tâche 1 — S10 séquentiel (`Corpus/S10Seq.lean`)

Le module n'importe que `Ern.MemoryModel.Access.Main`. La configuration S10 est montée sans mutex : `M = {slot}` possède `T` ; `guarded` est rangée dans `slot` ; `g := derive(guarded, Modify)` est tenue par `f0`. Contrat `Examples.K0`. Mise en place : `s10seq_setup` (`:52`).

| Pas | Attendu | Obtenu | Clause | Théorème |
|---|---|---|---|---|
| 1. `transfer(M, M′)` depuis `f1` | `ok` | `ok` | Spec 1 §63.1, §63.4, §63.7 | `S10Seq_1_ok` (`Corpus/S10Seq:62`) |
| 2. `exitFrame` | `reject` | `reject` | §73.4 | `S10Seq_2_reject` (`:66`) |
| 3. `EffAnchorOK … g (some f0)` | faux | faux | ni §44 ni §63.7 ne contraignent `g` | `S10Seq_anchor_misplaced` (`:74`) |
| 4. `transfer(M′, M)` | `ok` | `ok` | §63.3 | `S10Seq_3_ok` (`:78`) |
| 5. `exitFrame` | `ok` | `ok` | §73.4, §73.5 | `S10Seq_4_ok` (`:82`) |

Les états des pas 2 et 5 sont atteignables depuis `S3.init s10st` sous `K0` (`s10seq_reachable`, `:87`). Aucun verdict ne diffère.

## Tâche 2 — S3 réalisé jusqu'à `issue` (`Corpus/ARRealize.lean`)

- **`SimRunC` concrète.** `ar_sim0` … `ar_sim10` (`:55`–`114`) : de l'état initial du bloc AR au pas 3 de S3 (`acquire(e2)`, puis `issue(arena, R1, d1)`). Chaque pas porte son `StepOblC`, par `decide`. Paramètres : `πA := piOf a8.P []` ; `ParamsOK` par `piOf_ok`.
- **`s3_realized`** (`:123`). L'exécution est réalisée depuis la mémoire vide par des pas bruts `ok`, sans `ub`. `ReprC` tient aux 11 états. Les étiquettes forment une `EncapsulatedTrace` depuis l'état initial.
- **`s3_issue_hyps`** (`:152`). Les hypothèses d'`issue_pointer_soundC` tiennent ensemble avant `issue` : `ReprC`, `FramesC`, `WF3`, `NoDangling`, le pas `ok` `S3_3_ok`, l'entrée d'arène, la taille de la feuille et `PtrEncAt`.
- **`s3_issue_pointer`** (`:164`). Les octets de `d1` décodent l'adresse `adA`, avec la provenance de l'allocation de l'ancre effective ; `adA = 48`.
- **Verdicts et clauses.** Pas 2 et 3 attendus `ok`, obtenus `ok` et réalisés. Clauses : Spec 1 §77, §82.2, §82.3 ; WC4 C19, C25.

## Tâche 3 — `ArenaReg.unique`

- **(a) impossible.** `ArenaInvC` n'entraîne pas l'unicité : `arenaInvC_not_unique` (`Corpus/AR:201`) établit `ArenaInvC a6 (arA ++ arA) ∧ ¬ ArenaReg.unique (arA ++ arA) a6`.
- **(b) fait**, comme invariant de trace séparé :
  - `ArenaReg.unique` (`ArenaPreserve:488`), Spec 1 §56, première phrase ;
  - `lstep_arenaUnique` (`ArenaPreserve:522`) : tout `LStep` la préserve. Hypothèses : l'unicité avant, et la borne des `internal` enregistrés (fournie par `ArenaInvC` le long d'une trace) ;
  - `trace_arenaUnique`, `encapsulated_arenaUnique` (`Reachable:155`, `:168`) : forme trace, puis depuis l'état initial ;
  - `ar_unique` (`Corpus/AR:208`) : non-vacuité sur le registre de S3.
- **Énoncés non touchés.** L'unicité n'entre ni dans `LibInv`, ni dans les hypothèses de T4 (`lstep_preserves`) ou de T7 (`lstep_arenaInv`). Ces énoncés sont inchangés.

## Tâche 4 — témoins de passation (`Corpus/Handoff.lean`, corpus § 2 bis)

Chaque trace est une `EncapsulatedTrace` depuis un état initial `SC.ofS3 (S3.init …)`. `KInvC` tient à l'état final par `encapsulated_inv`. Les docstrings citent le corpus et n'affirment ni ordre ni absence de course.

| Témoin, pas | Attendu | Obtenu | Clause | Théorème (`Corpus/Handoff`) |
|---|---|---|---|---|
| W-HO, mise en place | S13 | réutilise `S13_1_reject` | — | `w_ho_trace` (`:44`) |
| W-HO 1, 2, 3 | `ok`, `ok`, `ok` (`c1` vivant au pas 3) | idem | O10.1 ; O3.1–O3.3 ; O10.1, §40, §43.2 | `W_HO_1_ok` (`:29`), `W_HO_2_ok` (`:33`), `W_HO_3_ok` (`:39`) ; jumeau `S13_2_ok` (`Corpus/Frames:149`) cité |
| W-HO′, mise en place, `spawn` cédant `a`, `b` gardée par `f0` | `ok` | `ok` | WC4 C4.3, C4.5, O6.3 | `W_HO2_0_ok` (`Corpus/Handoff:76`) |
| W-HO′ 1 | `reject` | `reject` ; mode effectif de `a` absent | O10.1, §43.3 | `W_HO2_1_reject` (`:83`) |
| W-HO′ 2, 3, 4 | `ok`, `ok`, `ok` | idem | O10.1 ; O3 ; §43.2 | `W_HO2_2_ok` (`:87`), `W_HO2_3_ok` (`:91`), `W_HO2_4_ok` (`:95`), `w_ho2_trace` (`:100`) |
| W-HO″, mise en place | `ok` | `ok` ; parent de la frame initiale de `c2` : frame 1 | O1, C4 | `w_ho3_setup` (`:137`) |
| W-HO″ 1, 2, 3 | `ok`, `ok`, `ok` | idem | O10.1 ; O3 ; O3.3 | `W_HO3_1_ok` (`:144`), `W_HO3_2_ok` (`:148`), `W_HO3_3_ok` (`:153`) |
| W-HO″ 4, `terminate` avec `c2` vivant | `ok` ; reparentage sur `f0` | `ok` ; `c2` vivant ; **parent obtenu : frame 0** (frame 1 avant) | WC4 C7, C6 | `W_HO3_4_ok` (`:159`) |
| W-HO″ 5, 6 | `ok`, `ok` (`c2` vivant) | idem | C8 ; O10.1, §43.2 | `W_HO3_5_ok` (`:164`), `W_HO3_6_ok` (`:168`), `w_ho3_trace` (`:178`) |
| W-HO″, négatif : `release(a)` avant `release(a₂)` | `reject` | `reject` ; `a₂` active | O3.3 | `W_HO3_7_reject` (`:173`) |

Aucun verdict ne diffère. Le `spawn` de W-HO′ est `ok`.

## Tâche 5 — synchronisation documentaire

- **Docstrings alignées sur la v3** (`bf36d25`) :
  - S10 : module, `S10_1_ok` ;
  - S11 : `S11_setup_wait`, `S11_1_ok` ;
  - W-C22.2 : `W_C22_2_encap`, `W_C22_2_reenable` ;
  - S3 négatif : `S3_3b_reject`, §60.2 en premier ;
  - S16 (c) : `ctl_transfer_breaks_ctlInit`.
- **S12.** Aucune docstring ne disait « déjà encodé » ; rien à changer.
- **S16 (c) n'est pas renommé en `Z`.** Le témoin utilise la place `Y`, place 7 des statiques `est`, aussi destination de S16 (a). Un `Z` distinct demanderait une place de plus dans `est`, donc d'autres états pour tout `EncapTraces.lean` : docstring seule.
- **`spec2-m3.md`.** Table de § A.3 mise à jour (S3 négatif, S9, S10, S11, S12, S16, S17, S18, W-C22.2). Une ligne de clôture est ajoutée à P1–P4, P6–P9. Partie B : modules, théorèmes, corpus de clôture, obligations OB-C08, OB-C12 et OB-C16, audit, et « Ce qui n'est pas vérifié ». Les numéros de ligne ont été relevés à `bf36d25` par un script qui ne fait que signaler, puis corrigés à la main.

## Écarts

1. **Ajouts au-delà des docstrings (tâche 5).** Ils encodent des verdicts de la v3 absents du module concurrent :
   - `S10_2_ok` (`Corpus/S10:73`) et `S10_3_ok` (`:79`) : suite concurrente de S10, `transfer(M′, M)` `ok` admis par `Encap`, puis `exitFrameC(f1)` `ok` ;
   - `W_C22_2_cycle` (`Corpus/MX:379`) : fondement renforcé de C22.2. Le cycle `acquire`/`unlock` du contexte 1 depuis `MX₄` atteint `(x5r, regX)`, l'état et le registre atteints par le `deriveSync` brut suivi du `release`.
2. **Base de la branche.** Après `fe2f4ee` viennent les trois commits de la revue : `8e2bccf`, `33b672f`, `e645f62`. La passe part de `e645f62`.
3. **P7 : deux verdicts du corpus et son critère § 0.** Le critère dit qu'une clause d'autorité ou de la Spec 1 défaillante donne `reject`. Or le corpus donne `non habilité` dans deux cas où la clause défaillante est de ce type :
   - **Mise en place de S11 sans la cession d'`o1′`** (`S11_setup_wait`, `Corpus/MX:259`). Le corpus : « sans elle C14.3/§68.2 échoue et `acquire` n'est pas habilité ». C14.3 renvoie à §68.2, une clause d'accès.
   - **W-C22.2** (`W_C22_2_encap`, `Corpus/MX:349`). Le corpus : `acquire(e)` « non habilitée tant que la dérivée sauvage est active (C13.9/C14) ». Dans `x5`, pour les contextes 0 et 1, `SyncAuthorized` est vrai (faits C14.1–C14.3). Ce qui échoue est `modeOK` (C15.4, Spec 1 §60.2) et `exclusive` (C15.5, §60.3), évalués par `#eval` sur `DeriveSyncPre`.
   - Le modèle ne distingue pas les deux verdicts pour `acquire`, qui ne définit que `ok`. Les encodages restent tels quels, comme le demande le brief ; l'arbitrage appartient au critère P7.

## Audit final des axiomes

- **Méthode.** `collectAxioms` sur toutes les constantes `thmInfo` `Ern.Concurrency*` et `_private.Ern.Concurrency*`, après `import Ern`.
- **Résultat à `bf36d25`.** 1144 théorèmes, dont 886 non internes, contre 1092 (835) au jalon 3. Aucun axiome hors `{propext, Quot.sound}`, y compris pour les théorèmes des tâches 1 à 5.
- **Build.** `lake build` réussit (69 jobs), sans avertissement.
- **Recherches vides.** Le `grep` d'`AGENTS.md` est vide. Aucun `noncomputable`, `decide +kernel` ni `ofReduceBool` dans `formal/Ern/Concurrency/`.
- **Fichiers intouchés.** `git diff e645f62 --stat` ne touche ni `formal/Ern/MemoryModel/` ni les fichiers protégés.
- **Lignes longues.** Aucune ligne ajoutée ne dépasse 100 caractères.
