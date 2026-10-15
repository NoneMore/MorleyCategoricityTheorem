# Infrastructure Plans

This directory holds active implementation plans for project infrastructure. Plans are promoted from
lightweight module-local TODOs only when the project decides to implement the underlying capability.
The capability itself is the identity of a plan; blueprint nodes and downstream proofs are
motivation or consumers, not plan owners.

## Lifecycle

Infrastructure ideas begin as natural-language bullets under `## TODO` in the documentation header
of the most relevant Lean module. A TODO may describe a candidate improvement, an investigation, or
an open design question. Recording it does not mean that the need is validated, the design is
settled, or implementation is committed.

When the project decides to implement an item, promote it to an active plan in `docs/plan/`, named
after the infrastructure capability. Replace the originating TODO with a short pointer to the plan;
do not keep a second summary of the design in the module header. The active plan is the single
detailed source of truth for that work and should be updated when implementation materially changes
the design. It is not a work log.

A plan is complete when the capability described by its design and constraints has been implemented
and the plan's verification requirements have passed. Completion does not wait for every motivating
blueprint node or downstream consumer to be implemented.

Before archiving a completed plan, move any durable knowledge that still describes the current
system into the relevant module documentation, then remove the module pointer. Move the plan to
`docs/plan/archive/`. Archived plans are historical design records: they explain the completed work
but are no longer maintained and are not a source of truth for the current system.

Plans that predate this convention may be migrated directly into `docs/plan/` without inventing a
module-local TODO or pointer retroactively. The pointer rule applies when a plan is promoted from an
existing module TODO.

## Plan format

Every active plan uses the following five top-level sections. Keep a section short when there is
little to say; do not add filler merely to satisfy the structure.

### Intent

State the capability being built and why it matters. Name motivating blueprint nodes or downstream
consumers when useful. This section defines the purpose and scope, not the detailed solution.

### Facts / Observations

Record only evidence that materially shapes the design: current code and API facts, repeated proof
patterns, relevant Mathlib facilities, experiments, or research conclusions. Keep observations
separate from the design chosen in response to them.

### Design

Describe the current chosen design, its public seams, and the important rationale or tradeoffs.
Update this section when implementation changes a material design decision.

### Specs / Constraints

State the properties the result must preserve or satisfy independently of implementation order:
public-interface expectations, dependency boundaries, compatibility requirements, invariants,
non-goals, and other hard constraints.

### Implementation / Verification

Record the concrete implementation path and completion checks: affected files or modules,
implementation order, migration or refactoring steps, builds, tests, and any explicitly authorized
blueprint validation.

## Conventions

- Plans are plain Markdown with no front matter or status metadata. File location expresses lifecycle.
- Module TODOs are plain natural-language bullets. Do not add IDs, owners, priorities, dates,
  checkboxes, or status fields.
- Active plans live directly under `docs/plan/` as single Markdown files by default. Use a directory
  for one plan only when essential supporting artifacts make a single file impractical.
- Archived plans live under `docs/plan/archive/` and are not kept current after archival.
- Do not maintain an active-plan index in this README; the directory contents are the index.
