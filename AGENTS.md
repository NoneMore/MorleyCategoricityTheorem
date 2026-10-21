# Repository Agent Instructions

This repository formalizes Morley's categoricity theorem in Lean 4 using Mathlib.
Follow `CONTRIBUTING.md` for contribution workflow and validation.

## Lean Development

- Treat compiled Lean declarations as the source of truth. Do not report a result
  as fully proved while it or a dependency contains `sorry`.
- Declare variables explicitly (`autoImplicit` is disabled).
- Follow nearby Mathlib naming and namespaces; keep imports minimal and acyclic.
- Document public definitions and non-obvious results by mathematical purpose.
  Prefer short declaration docstrings (usually one sentence, 1–3 lines);
  explain subtle hypotheses or proof ideas only when they help readers.
  Do not restate the theorem signature or narrate routine proof steps.
- Keep module docstrings focused on scope and key results. Do not repeat
  detailed design rationale already recorded in `docs/plan/`.
- Prefer `lean-lsp-mcp` over edit-build cycles for proof exploration.

## Project Boundaries

- Do not modify `blueprint/` unless the user requests blueprint work. Read-only
  status and declaration-reference checks remain allowed.
- For blueprint status tools, use `python3 scripts/blueprint_status.py --help`.
  Update its `MILESTONES` mapping if milestone labels change.
- Preserve unrelated working-tree changes. Never discard user work with
  `git restore`, `git reset --hard`, `git stash`, or `git checkout --`.
- Do not commit, push, open PRs, or rewrite history unless requested. Stage only
  the intended files.

## Pull Requests

- Keep PR descriptions brief: what changed and why, validation, and only
  essential caveats. Link to plans or issues instead of copying design notes,
  exhaustive declaration lists, or proof walkthroughs.

## Completion

- Run applicable checks from `CONTRIBUTING.md`; LSP diagnostics alone are not
  a substitute for required build checks.
- Report what changed, which checks ran, and which checks could not run and why.
