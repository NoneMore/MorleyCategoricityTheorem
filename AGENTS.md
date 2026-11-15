# Repository Agent Instructions

This repository formalizes Morley's categoricity theorem in Lean 4 using Mathlib.
When changing repository files, consult `CONTRIBUTING.md` for the
applicable contribution workflow and validation checks.

## Lean Development

- Treat compiled Lean declarations as the source of truth. Before reporting
  a result as fully proved, inspect its axioms (e.g. with `#print axioms`)
  for `sorryAx` in the result or its dependencies; a successful build alone
  is insufficient.
- Declare variables explicitly (`autoImplicit` is disabled).
- Follow nearby Mathlib naming and namespaces; keep imports minimal and acyclic.
- Document public definitions and non-obvious results by mathematical purpose.
- Prefer `lean-lsp-mcp` over edit-build cycles for proof exploration.

## Project Boundaries

- Do not modify `blueprint/` unless the user requests blueprint work. Read-only
  status and declaration-reference checks remain allowed.
- If a Lean change leaves blueprint declaration references outdated and
  blueprint edits are not authorized, report the mismatch instead of modifying
  `blueprint/`.
- For blueprint status tools, use `python3 scripts/blueprint_status.py --help`.
  Update its `MILESTONES` mapping if milestone labels change.
- Preserve unrelated working-tree changes. Never discard user work with
  `git restore`, `git reset --hard`, `git stash`, or `git checkout --`.
- Do not commit, push, open PRs, or rewrite history unless requested. Stage only
  the intended files.

## Completion

- Run applicable checks from `CONTRIBUTING.md`; LSP diagnostics alone are not
  a substitute for required build checks.
- Report what changed, which checks ran, and which checks could not run and why.
