# Repository Agent Instructions

This repository formalizes Morley's categoricity theorem in Lean 4 using Mathlib.
Follow `CONTRIBUTING.md` for contribution workflow and validation.

## Lean Development

- Treat compiled Lean declarations as the source of truth. Do not report a result
  as fully proved while it or a dependency contains `sorry`.
- Declare variables explicitly (`autoImplicit` is disabled).
- Follow nearby Mathlib naming and namespaces; keep imports minimal and acyclic.
- Document public definitions and non-obvious results by mathematical purpose.
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

## Completion

- Run applicable checks from `CONTRIBUTING.md`; LSP diagnostics alone are not
  a substitute for required build checks.
- Before claiming a requested Lean change is complete, confirm the intended
  declarations or edits are present in the final source and covered by the
  verification performed. A passing build of unchanged or unrelated code is not
  evidence of completion.
- Report what changed, which checks ran, and which checks could not run and why.
