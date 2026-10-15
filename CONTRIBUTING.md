# Contributing to MorleyCategoricityTheorem

Thank you for your interest in contributing. This repository welcomes improvements to the Lean
formalization, project documentation, and repository infrastructure.

## Before starting

- Check existing issues and pull requests to avoid duplicating work.
- For mathematical work, consult the blueprint and its dependency graph before choosing a target.
- Keep pull requests focused. Large or cross-cutting changes are easier to review when split into
  coherent pieces.

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

## Pull requests

A useful pull request description should explain:

- what changed and why;
- which part of the project is affected;
- which validation commands were run;
- any remaining limitations, follow-up work, or intentional placeholders;
- relevant issues or blueprint nodes, when applicable.

Please keep unrelated formatting or cleanup out of a functional change unless it is necessary for
the change itself.
