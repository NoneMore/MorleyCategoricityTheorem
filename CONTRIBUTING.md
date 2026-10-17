# Contributing to MorleyCategoricityTheorem

Thank you for your interest in contributing. This repository welcomes improvements to the Lean
formalization, project documentation, and repository infrastructure.

## Before starting

- Check existing issues and pull requests to avoid duplicating work.
- For mathematical work, consult the blueprint and its dependency graph before choosing a target.
- Keep pull requests focused. Large or cross-cutting changes are easier to review when split into
  coherent pieces.
- Keep handwritten source and documentation lines within 100 columns. The `.vscode` editor ruler
  reflects this project convention; CI does not enforce it.

## Local setup

Install Lean 4 using the
[Lean installation guide](https://leanprover-community.github.io/get_started.html), then clone the
repository:

```bash
git clone https://github.com/NoneMore/MorleyCategoricityTheorem.git
cd MorleyCategoricityTheorem
```

Fetching the Mathlib cache is recommended before the first build:

```bash
lake exe cache get
```

Build the project with:

```bash
lake build MorleyCategoricityTheorem
```

## Lean changes

Lean source files live under [`MorleyCategoricityTheorem/`](MorleyCategoricityTheorem). The root
file [`MorleyCategoricityTheorem.lean`](MorleyCategoricityTheorem.lean) imports the project modules.

When making Lean changes:

- Prefer existing Mathlib declarations over local replacements when possible.
- Keep imports minimal and follow the naming and namespace conventions of nearby code.
- For reusable Lean/formalization infrastructure discovered during proof development, follow the
  TODO, active-plan, and archival lifecycle in [`docs/plan/README.md`](docs/plan/README.md).
- Do not introduce new `sorry` placeholders unless the change is explicitly intended as
  scaffolding and the pull request clearly says so.
- Do not edit files under `.lake/packages/` or `.lake/build/`.
- Do not edit `lake-manifest.json` by hand; update dependencies through Lake instead.

If modules are added, removed, or renamed, synchronize the root import file and verify it with:

```bash
lake exe mk_all --check
```

If Lean declarations referenced by the blueprint are renamed, removed, or otherwise changed, also
check the declaration references with:

```bash
lake exe checkdecls blueprint/lean_decls
```

## Blueprint changes

Keep blueprint edits separate from unrelated Lean or infrastructure changes whenever practical.
If a pull request intentionally changes the blueprint, describe which nodes or dependencies were
updated. The documentation CI builds the blueprint and checks its Lean declaration references on
relevant pull requests.

A Lean-only or repository-infrastructure pull request does not need to modify the blueprint.

## Validation

Run the checks relevant to the files you changed from the repository root:

- Lean changes: `lake build MorleyCategoricityTheorem`
- Added, removed, or renamed Lean modules: also run `lake exe mk_all --check`
- Lean declarations referenced by the blueprint: also run `lake exe checkdecls blueprint/lean_decls`
- Changes to `scripts/blueprint_status.py` or its tests: run
  `python3 -m unittest discover -s scripts/tests -v` and
  `python3 scripts/blueprint_status.py --milestones`
- Blueprint or `home_page/` changes: ensure the documentation validation workflow passes
- Documentation-only Markdown changes: review rendered Markdown and verify links where applicable

If you cannot run an applicable local check, mention that explicitly in the pull request
description. CI remains the final validation gate for checks configured in the repository.

## Commits, branches, and merges

Changes reach `main` through a pull request. Project policy requires squash merges. `main` requires
the `Validate repository` status check with "require branches to be up to date" enabled, requires
review conversations to be resolved, and rejects force pushes and deletion. GitHub deletes the head
branch on merge.

- Name branches `<type>/<slug>` in lower case, using the commit types listed below. Blueprint work
  also uses `blueprint/` and `planning/`. Keep `wip/` branches local, and delete draft branches
  whose work has been abandoned.
- Write commit subjects as `<type>(<scope>): <imperative summary>`, for example
  `feat(semantics): prove the realization-set skeleton` or `docs: refine AGENTS.md validation
  guidance`. Use the lowercase types `feat`, `fix`, `docs`, `refactor`, `chore`, `ci`, `build`, and
  `test`. Preserve canonical capitalization for repository paths, Lean identifiers, and module
  names. The optional `scope` names a repository area (`blueprint`, `deps`) or the Lean module
  changed. Dependency updates keep the `build(deps): bump <dependency> from <old> to <new>` form.
- Write the pull request title in the same format. With this repository's squash settings, a
  single-commit pull request takes its merged subject from the branch commit, and a multi-commit
  pull request takes it from the pull request title; the merged body is built from the branch
  commits. Keep one logical change per pull request and prefer a single commit.
- Describe why the change is needed, what it deliberately leaves unchanged, and the validation
  commands you ran, for example with a final `Validation: lake build MorleyCategoricityTheorem`
  line.
- Do not add authorship or co-authorship trailers for AI assistance. Commits are attributed to the
  people who directed the work.
- Update the branch to the current `main` before merging. Never force push `main` or a branch
  someone else is working on, and rewrite history only on local, unpushed commits.
- Release tags are created automatically from `lean-toolchain` changes on `main`; do not create
  them by hand.

## Pull requests

A useful pull request description should explain:

- what changed and why;
- which part of the project is affected;
- which validation commands were run;
- any remaining limitations, follow-up work, or intentional placeholders;
- relevant issues or blueprint nodes, when applicable.

Please keep unrelated formatting or cleanup out of a functional change unless it is necessary for
the change itself.
