# Repository Instructions

## Scope

These instructions apply to the entire repository. More specific instructions
under a subdirectory take precedence for files in that subtree. In particular,
follow `blueprint/src/AGENTS.md` when editing the mathematical blueprint.

## Project

This repository formalizes Morley's categoricity theorem in Lean 4 using
Mathlib and a Leanblueprint dependency graph.

- Lean source lives under `MorleyCategoricityTheorem/`.
- `MorleyCategoricityTheorem.lean` is the root import file.
- Mathematical blueprint source lives under `blueprint/src/`.
- `lakefile.toml` and `lean-toolchain` define the project configuration and
  toolchain.

Treat compiled Lean declarations as the authority for formalization status.
Treat the blueprint as the authority for the intended mathematical statements
and dependency structure. If they disagree, do not hide the discrepancy by
changing only a status marker; either align the requested artifacts or report
the mismatch.

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

## Blueprint Synchronization

- When a Lean declaration implements a blueprint node, keep its fully qualified
  name and formalization status accurate in the blueprint.
- Do not add aspirational declaration names to `\lean{...}`. A referenced name
  must exist in the current project or Mathlib and pass declaration checking.
- A mathematical change is not complete merely because Lean compiles: check
  whether the corresponding blueprint statement or dependency also needs to be
  updated.

## Generated Files

- Edit blueprint sources, not generated HTML, PDF, or LaTeX auxiliary output.
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
| Blueprint source, declaration links, or status markers | `leanblueprint all` |
| Both Lean and blueprint files | all three commands |

If a full validation cannot be run, state exactly which command was omitted and
why.

## Definition of Done

- Relevant Lean targets build successfully.
- No unintended `sorry` placeholders or unrelated changes were introduced.
- Root imports reflect the current module set.
- Blueprint labels, dependencies, Lean links, and status markers are accurate.
- Generated artifacts were changed only by the appropriate generation command.
- The final report lists the files changed and the validation performed.
