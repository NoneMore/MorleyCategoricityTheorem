# Contributing to MorleyCategoricityTheorem

Contributions to the Lean formalization, documentation, and project tooling are
welcome. Keep changes focused and consult the blueprint for mathematical work.

## Setup

Install Lean 4 using the
[Lean installation guide](https://leanprover-community.github.io/get_started.html),
then clone the repository and fetch the Mathlib cache:

```bash
git clone https://github.com/NoneMore/MorleyCategoricityTheorem.git
cd MorleyCategoricityTheorem
lake exe cache get
lake build MorleyCategoricityTheorem
```

## Lean and Blueprint Changes

- Prefer existing Mathlib declarations and nearby naming conventions. Keep
  imports minimal.
- Do not introduce `sorry` unless explicitly scaffolding and documented in the PR.
- Do not edit `.lake/packages/`, `.lake/build/`, or `lake-manifest.json` by hand.
- For substantial reusable Lean infrastructure, see [docs/plan/README.md](docs/plan/README.md).
  Small investigations and TODOs do not require separate plans.
- Only change `blueprint/` when the work intentionally includes blueprint changes;
  describe the affected nodes or dependencies in the PR.

## Lean Documentation

- Write docstrings for public definitions and non-obvious results to explain
  mathematical meaning or useful proof ideas. A single sentence (typically
  1–3 lines) is the default; expand only when complexity warrants it.
- Keep module documentation to its scope and main results. Avoid restating
  declaration signatures, listing every helper, or narrating proof steps.
- Use `docs/plan/` for detailed design discussions during planning. Move
  only durable, reader-relevant information into Lean documentation, without
  duplicating the plan.

## Validation

Run the checks relevant to your changes from the repository root:

- Lean code: `lake build MorleyCategoricityTheorem`.
- Added, removed, or renamed Lean modules: synchronize
  `MorleyCategoricityTheorem.lean` and run `lake exe mk_all --check`.
- Changed, renamed, or removed blueprint-referenced Lean declarations:
  `lake exe checkdecls blueprint/lean_decls`.
- `scripts/blueprint_status.py` or its tests:
  `python3 -m unittest discover -s scripts/tests -v` and
  `python3 scripts/blueprint_status.py --milestones`.
- Blueprint or `home_page/` changes: ensure the documentation CI passes.
- Documentation-only changes: review rendering and relevant links.

If a relevant check cannot run, state which check was skipped and why.
CI remains the final gate.

## Git and Pull Requests

- Changes reach `main` through focused PRs and squash merges; honor branch
  protections and preserve others' work.
- Use descriptive lowercase branches such as `feat/...`, `fix/...`, or
  `planning/...`. Use `<type>: <summary>` or `<type>(<scope>): <summary>`
  for commit subjects and PR titles.
- Keep dependency-update subjects in the `build(deps): bump ...` form.
- Release tags are automated; do not create them manually.
- Do not add AI authorship or co-authorship trailers.
- Keep PR descriptions short: summarize what changed and why, report
  validation performed or skipped, and note only relevant limitations or
  blueprint changes. Prefer a few bullets over file-by-file inventories or
  proof walkthroughs; link plans, issues, or blueprint nodes for details.
  Expand only when needed for review.
