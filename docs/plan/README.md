# Lean Infrastructure Plans

Use `docs/plan/` for substantial, reusable Lean/formalization infrastructure
whose design benefits from a shared plan. Small fixes, investigations, and TODOs
can stay in the relevant Lean module; a separate plan is not required.

This directory does not govern CI, blueprint tooling, or website work.

## Lifecycle

When a complex capability needs a shared design, create
`docs/plan/<capability>.md` and link to it from the module if useful. Avoid
duplicating the design in both places.

Keep active plans updated when important design decisions change, not as a work
log. When work is complete, put durable knowledge in the Lean documentation and
archive the plan under `docs/plan/archive/` if retaining its history is useful.

## Suggested Content

Describe the motivation, relevant Mathlib/API facts, chosen design, important
constraints, implementation steps, and verification. Use whatever headings
make the plan clear; no fixed five-section format or status metadata is required.

The files in `docs/plan/` serve as the index; do not maintain a separate one.
