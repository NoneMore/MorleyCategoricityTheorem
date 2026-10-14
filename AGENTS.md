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

`scripts/blueprint_status.py` is the read-only planning tool for the mathematical
blueprint. It validates the dependency graph, reports the formalization frontier,
and ranks next steps relative to a selected proof goal. It never writes to
`blueprint/` and does not replace the blueprint validation build.

```bash
python3 scripts/blueprint_status.py                         # goal-aware frontier
python3 scripts/blueprint_status.py --all                   # every pending node
python3 scripts/blueprint_status.py --milestones            # milestone progress
python3 scripts/blueprint_status.py --milestone omega_stability --top 5
python3 scripts/blueprint_status.py --why thm:two-cardinal-transfer
python3 scripts/blueprint_status.py --unlocks lem:pair-relativization
python3 scripts/blueprint_status.py --plan morley
python3 scripts/blueprint_status.py --sort reach
python3 scripts/blueprint_status.py --json
```

Conventions the planner relies on:

- A node counts as formalized when its environment is marked `\leanok` (proved
  in this repository) or `\mathlibok` (supplied by Mathlib).
- Dependencies are every `\uses{...}` command in the node statement and its
  attached proof.
- The planner treats duplicate labels, self-dependencies, dependency cycles,
  and dangling `\uses` references as structural errors. Pass `--allow-dangling`
  only when intentionally inspecting an incomplete graph.
- The *frontier* is the pending nodes whose dependencies are all formalized.
  Nodes held up only by pending definitions are listed separately.
- Named milestones and per-node planning metadata live in
  `scripts/blueprint_status.toml`. Keep labels in that file synchronized with
  the blueprint.

The default ranking is lexicographic rather than a single composite score. It
prefers nodes on a path to the selected goal, then nodes that make blocked work
immediately ready, then nodes with larger goal-path reach, with estimated effort
as a tiebreaker. The report also exposes:

- `new`: blocked nodes that become frontier-ready after completing the node;
- `g-reach`: pending downstream nodes that lie on a path to the selected goal;
- `dist`: shortest number of pending nodes to the goal;
- `crit`: longest pending chain to the goal;
- `eff`: effort estimate from `scripts/blueprint_status.toml`, falling back to
  1 for definitions, 2 for lemmas/propositions/corollaries, and 3 for theorems;
- `risk`: optional qualitative planning metadata from the TOML configuration.

`--sort` may rank by `plan`, `score`, `unlocks`, `reach`, `goal-reach`, `new`,
`distance`, `critical`, or `effort`. The displayed `score` is only a secondary
heuristic: `(new_ready + goal_reach + on_goal_path) / effort`; it intentionally
does not add total reach and direct unlocks again, avoiding the previous
double-counting of downstream benefit.

Use `--milestone NAME` to restrict the frontier to work that can contribute to a
named milestone, `--why LABEL` to recursively explain blockers, `--unlocks
LABEL` to inspect downstream impact, and `--plan TARGET` for a dependency-safe
topological worklist. Use `--goal LABEL` for an ad-hoc goal outside the named
milestones.

The parser remains intentionally lightweight and currently reads one TeX entry
file. If the blueprint is physically split with `\input`, extend the parser and
its tests before relying on the planner across files.

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
| Blueprint planner files | `python3 -m unittest discover -s scripts/tests -v` + `python3 scripts/blueprint_status.py --milestones` |

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
