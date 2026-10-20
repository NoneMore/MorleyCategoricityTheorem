# Repository Instructions

## Scope

These instructions apply to the entire repository. More specific applicable
project instructions under a subdirectory take precedence for files in that
subtree.

## Project

This repository formalizes Morley's categoricity theorem in Lean 4 using
Mathlib.

Treat compiled Lean declarations as the authority for what is currently
implemented. Do not describe a declaration as fully proved while it or a local
dependency still contains `sorry`.

## Contribution Norms

`CONTRIBUTING.md` owns the shared contribution workflow, project-wide style,
validation triggers, dependency and planning rules, commit/branch/merge
conventions, and pull request expectations. Follow it for anything it covers,
including its ban on AI authorship trailers; add repository- and agent-specific
rules below rather than restating it.

## Lean Development

- Declare variables and assumptions explicitly; the project builds with
  automatic implicit variables disabled.
- Keep declarations in the narrowest appropriate namespace and follow the
  naming and argument conventions of nearby Mathlib and project model-theory
  code.
- Add module and declaration documentation for public definitions and
  non-obvious results. Explain mathematical purpose rather than narrating the
  tactic script.
- Keep imports minimal and acyclic. When adding, removing, or renaming a module,
  synchronize `MorleyCategoricityTheorem.lean` and run
  `lake exe mk_all --check`.
- Prefer `lean-lsp-mcp` over edit-build cycles for proof exploration.
- Defer mechanical formatting until proofs stabilize; prefer automated fixes over
  manual line-by-line adjustments.

## Blueprint Boundary

Unless the user explicitly requests blueprint work, do not modify files under
`blueprint/` and do not synchronize Lean changes into the blueprint.

Read-only consistency checks against blueprint data are allowed when their
normal validation trigger applies. In particular, changes to Lean declarations
referenced by the blueprint may require
`lake exe checkdecls blueprint/lean_decls`; running that check does not
authorize blueprint edits.

When the user does request blueprint work, `blueprint/` becomes editable and the
blueprint validation described in `CONTRIBUTING.md` applies.

## Blueprint Status Tool

`scripts/blueprint_status.py` is a read-only dependency-graph validator and
goal-aware frontier reporter. Use
`python3 scripts/blueprint_status.py --help` for CLI usage.

When milestone theorem labels change, keep the script's `MILESTONES` mapping
synchronized with the blueprint labels.

## Version Control

- Do not commit, push, open pull requests, or rewrite existing history unless
  the task asks for it.
- Preserve unrelated working-tree changes. Do not use `git restore`,
  `git reset --hard`, `git stash`, or `git checkout --` to remove or overwrite
  user work, including incomplete work that looks like scratch.
- Stage files explicitly instead of using `git add -A` or `git add .`, so
  unrelated work in the tree cannot slip into a commit.

## Validation

Use the validation rules in `CONTRIBUTING.md` for the files and interfaces
changed. In particular:

- Lean changes: `lake build MorleyCategoricityTheorem`.
- Added, removed, or renamed Lean modules: also
  `lake exe mk_all --check`.
- Changed, renamed, or removed Lean declarations referenced by the blueprint:
  also `lake exe checkdecls blueprint/lean_decls`.
- Changes to `scripts/blueprint_status.py` or its tests:
  `python3 -m unittest discover -s scripts/tests -v` and
  `python3 scripts/blueprint_status.py --milestones`.

Do not run unrelated blueprint build or synchronization work merely because a
Lean file changed.

If an applicable validation cannot be run, state exactly which command was
omitted and why.

## Definition of Done

- Applicable validation passes. A clean LSP or diagnostic report, without the
  build and applicable checks, is not completion evidence.
- No unintended `sorry` placeholders or unrelated changes were introduced.
- The root import file reflects the module set when modules changed.
- Blueprint files remain untouched unless blueprint work was explicitly
  requested.
- The final report lists files changed, validation performed, and any applicable
  validation that could not be run.
