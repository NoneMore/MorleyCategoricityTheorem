# Repository Instructions

## Scope

These instructions apply to the entire repository. More specific instructions
under a subdirectory take precedence for files in that subtree.

## Project

This repository formalizes Morley's categoricity theorem in Lean 4 using
Mathlib.

- Lean source lives under `MorleyCategoricityTheorem/`.
- `MorleyCategoricityTheorem.lean` is the root import file.
- `lakefile.toml` and `lean-toolchain` define the project configuration and
  toolchain.

Treat compiled Lean declarations as the authority for what is currently
implemented. Never describe a declaration as fully proved while it or a local
dependency still contains `sorry`.

## Lean 4 Workflow

For Lean proofs, theorem statements, formalization, proof repair, diagnostics,
Mathlib search, or Lake build work, use the discovered `lean4` skill and follow
its relevant workflow when that skill is available in the active harness.

When available, use the configured `lean-lsp` MCP server for interactive
feedback. The applicable repository validation commands below remain the final
completion gate.

User instructions and repository-specific rules in this file take precedence
if the skill gives conflicting guidance.

## Lean Development

- Search the current Mathlib dependency for an existing declaration before
  adding a local replacement.
- Keep declarations in the narrowest appropriate namespace and follow the
  naming and argument conventions of nearby Mathlib model-theory code.
- The project disables automatic implicit variables. Declare variables and
  assumptions explicitly so changes remain compatible with
  `autoImplicit = false` and `relaxedAutoImplicit = false`.
- Add module and declaration documentation for public definitions and
  non-obvious results. Explain the mathematical role rather than narrating the
  tactic script.
- Do not introduce new `sorry` placeholders unless the task explicitly permits
  scaffolding. Never describe a declaration as fully proved while it or a local
  dependency still contains `sorry`.
- Keep imports minimal and acyclic. When adding, removing, or renaming a module,
  keep `MorleyCategoricityTheorem.lean` synchronized.
- Do not edit dependency sources under `.lake/packages/` or build artifacts
  under `.lake/build/`.

## Blueprint Boundary

Unless the user explicitly requests blueprint work, do not modify files under
`blueprint/`, do not synchronize Lean changes into the blueprint, and do not run
blueprint-related validation.

If the user explicitly requests blueprint work, follow the user-invoked skill or
instructions for both blueprint editing and blueprint validation instead of
relying on repository-default blueprint rules.

## Blueprint Progress

`scripts/blueprint_status.py` answers "what can be formalized next, and which
node first?" by parsing the dependency graph of `blueprint/src/content.tex`. It
is read-only: it never writes to `blueprint/` and does not replace the blueprint
validation build.

```bash
python3 scripts/blueprint_status.py              # frontier, ranked by priority
python3 scripts/blueprint_status.py --all        # every pending node, in order
python3 scripts/blueprint_status.py --sort reach # rank by one metric
python3 scripts/blueprint_status.py --json       # machine-readable output
```

Conventions the report relies on:

- A node counts as formalized when its environment is marked `\leanok` (proved
  in this repository) or `\mathlibok` (supplied by Mathlib).
- Dependencies are the labels of every `\uses{...}` command, both in the node's
  statement and in the proof attached to it, because proof-level `\uses` list
  the lemmas the proof actually invokes.
- The *frontier* is the pending nodes whose dependencies are all formalized.
  Nodes held up only by a missing definition are listed separately, since the
  definition is usually the immediate next step.

Frontier nodes are ranked by how much formalizing them would advance the
blueprint:

    score = (unlocks + reach + new_ready + critical) / effort

- `unlocks` counts the pending nodes that directly depend on the node, `reach`
  those that depend on it transitively, and `new_ready` the currently blocked
  nodes that become frontier as soon as it is done.
- `critical` is the longest remaining chain of pending nodes from it to the goal
  (default `cor:morley-categoricity`; `--goal` changes it and an empty string
  disables critical paths). A node on no path to the goal is reported as
  off-goal.
- `effort` is a coarse cost proxy: 1 for a definition, 2 for a lemma,
  proposition or corollary, 3 for a theorem. It is a heuristic, not a
  measurement.

The composite is a default, not a verdict: `--sort` ranks by any single metric
(`score`, `unlocks`, `reach`, `new`, `critical`, `effort`) and the component
columns are always printed. Prefer a definition with high `reach` when the goal
is to unblock the largest part of the blueprint; prefer `critical` when the goal
is the shortest route to Morley's theorem.

Use the report to pick the next blueprint node; it is a planning aid, not a
completion gate, so it does not replace `lake build MorleyCategoricityTheorem`,
`lake exe mk_all --check`, or a blueprint build. The script locates the
repository from its own path, so it may be invoked from any working directory;
pass `--tex PATH` to analyse a different document.

## Generated Files

- Do not hand-edit `lake-manifest.json`. Update it only through Lake dependency
  commands when the task calls for a dependency change.
- Preserve unrelated working-tree changes. Do not remove or overwrite user
  work in order to obtain a clean build.

## Validation

Run the checks that match the files changed, from the repository root.

| Files changed | Command |
|---|---|
| Only `.lean` files, no new imports | `lake build MorleyCategoricityTheorem` |
| `.lean` files with new or removed imports | above + `lake exe mk_all --check` |

If no blueprint files were changed, do not run blueprint-related validation. If
the user explicitly requested blueprint changes, use the validation workflow
specified by the user-invoked blueprint skill or instructions.

If an applicable validation cannot be run, state exactly which command was
omitted and why.

## Definition of Done

- Relevant Lean targets build successfully.
- No unintended `sorry` placeholders or unrelated changes were introduced.
- Root imports reflect the current module set.
- Blueprint files remain untouched unless the user explicitly requested
  blueprint work.
- The final report lists the files changed and the validation performed.
