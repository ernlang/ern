# AGENTS.md

Claude Code implements. Codex reviews. Both follow this file.

## Source of truth

- `specs/` is normative and the only source of semantics. Before acting, read the spec text the task depends on. Never rely on memory, summaries, comments or earlier sessions.
- Never restate spec content in code comments or agent files. Point to its location.
- Spec beats code. If the spec is ambiguous, contradictory or silent on something the task needs: stop and report the exact passage with a concrete example of the problem. Never pick an interpretation yourself.
- Representation choices (structure or inductive type, function or relation) are yours when they change no accepted program and no behavior. A choice that does is a semantic question: stop and report.

## Scope

- Do exactly the task. No unrequested features, generalization, refactoring or "robustness" additions. Put suggestions in the report.
- Do not edit `specs/`, `AGENTS.md`, `CLAUDE.md` or `formal/DESIGN.md` unless the task says so.

## Lean

- The Lake project is in `formal/`. `formal/DESIGN.md` governs how to formalize, never what the semantics is. Propose design decisions it does not settle in your report; never take them silently.
- Every definition or theorem that encodes a spec rule cites the rule's location in its docstring.
- A definition says what its rule says. Never make a definition more permissive, add an unjustified hypothesis or narrow a theorem's domain to obtain a proof.
- Never change a theorem statement, or a definition it depends on, to make a proof go through. If stuck, stop and report the goal state.
- Never use `sorry`, `admit`, `axiom` or `native_decide`.
- Every `.lean` file under `formal/` is part of the build target.
- Done means:
  - `lake build` (in `formal/`) succeeds;
  - this prints nothing: `grep -rnE '\b(sorry|admit|native_decide)\b|^\s*axiom\b' --include='*.lean' --exclude-dir=.lake .`
  - for each theorem completed by the task, `#print axioms` lists nothing beyond `propext`, `Classical.choice` and `Quot.sound`.

## Report

Spec passages implemented (by location), what changed, what is unproven or open, spec problems found.

## Review (Codex)

Adversarial and read-only. For each change, check:

- It says exactly what the spec says: not stronger, not weaker. Read definitions, hypotheses and quantifiers, not only proofs. A theorem that holds because a definition is too permissive or its hypotheses are unsatisfiable is blocking.
- Each formalized rule cites its spec location.
- No theorem statement or dependency was changed without the task allowing it.
- No interpretation was chosen silently where the spec is unclear.
- Nothing outside the task was added.

When a milestone is declared complete, compare the rules in its announced scope with the spec locations cited in `formal/`, and list every rule left without a definition or theorem.

Every finding needs evidence: a spec quote, a counterexample or command output. No evidence, no finding. Never ask for additions beyond the task.

Output: verdict (block / changes / ok), then each finding with severity, location, cause (formalization error, missing coverage or spec defect) and evidence.
