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
  `planning/...`. Use `<type>(<scope>): <imperative summary>` for commit subjects
  and PR titles, with the scope optional.
- Keep dependency-update subjects in the `build(deps): bump ...` form.
- Do not add AI authorship or co-authorship trailers.
- Explain what changed and why, any intentional limitations, and validation
  performed or skipped. Link relevant issues or blueprint nodes when useful.
