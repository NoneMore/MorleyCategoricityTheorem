# Blueprint Instructions

## Scope

These instructions apply to files under `blueprint/src/` and supplement the
repository-level `AGENTS.md`.

## Mathematical Narrative

The blueprint should read as ordinary mathematical notes, not as a Lean proof
script. Organize it in mathematical order:

1. foundational definitions and conventions;
2. basic constructions;
3. intermediate lemmas and propositions;
4. main theorems.

State the mathematics independently of implementation details. Mention Lean
names only when linking a blueprint item to an existing formal declaration or
when a short formalization note resolves a genuine mismatch in representation.

## Source Layout

- Write the main mathematical narrative in `content.tex`, or in files imported
  from `content.tex` if the blueprint is split later.
- Keep `web.tex` and `print.tex` as output-specific preambles. Do not put the
  mathematical narrative there.
- Put macros shared by both output formats in `macros/common.tex`.
- Put format-specific macros in `macros/web.tex` or `macros/print.tex`.
- When editing a draft under `drafts/`, edit only that draft unless the user
  explicitly asks to promote or synchronize it with the formal blueprint.
- Do not hand-edit generated files such as `*.aux`, `*.log`, `*.toc`, `*.fls`,
  `*.fdb_latexmk`, `*.paux`, `*.synctex.gz`, generated PDFs, or files under
  `../web/` and `../print/`.

## Dependency Graph Nodes

- Use theorem-like environments collected by the dependency graph:
  `definition`, `lemma`, `proposition`, `theorem`, and `corollary`, unless the
  preamble is deliberately changed.
- Give every central graph node a stable, descriptive LaTeX label.
- Use predictable prefixes: `def:`, `lem:`, `prop:`, `thm:`, and `cor:`.
- Place Leanblueprint macros near the start of the environment, after
  `\label{...}` and before the mathematical prose.

## Leanblueprint Status Macros

- `\lean{...}` lists fully qualified Lean declaration names corresponding to
  the surrounding definition or statement. Separate multiple names with
  commas. Add only names that exist and type-check.
- `\leanok` on a definition or statement means that an existing Lean
  declaration matches it. `\leanok` in a proof means that the corresponding
  Lean proof contains no local `sorry`.
- A theorem proved using project lemmas that still contain `sorry` may have a
  locally complete proof, but must be reported as "proved modulo lemmas" rather
  than as an unconditional completion of the dependency chain.
- `\uses{label-a,label-b}` records graph dependencies. On a statement, list
  only dependencies needed to state it. In its proof, list proof-only
  dependencies.
- Prefer an explicit proof environment for proof-only dependencies instead of
  mixing statement and proof dependencies on the theorem node.
- `\notready` marks an item whose mathematical statement or prerequisites are
  not yet ready for formalization. Do not combine it with `\leanok`.
- `\discussion{123}` records a GitHub issue using the bare issue number.
- `\proves{label}` belongs in a non-adjacent proof environment. Omit it when a
  proof immediately follows the statement it proves.
- `\mathlibok` is reserved for declarations supplied by the current Mathlib
  dependency. Do not use it for declarations local to this repository.

For a formalized item with an immediate proof, prefer this shape:

```tex
\begin{theorem}[Descriptive title]
\label{thm:stable-label}
\lean{Namespace.declarationName}
\leanok
\uses{def:needed-to-state}
Mathematical statement.
\end{theorem}

\begin{proof}
\leanok
\uses{lem:proof-dependency}
Mathematical proof explanation.
\end{proof}
```

For a planned item, omit `\lean` and `\leanok`. Use `\notready` only while the
statement or its prerequisites are genuinely unstable.

## Validation

From the repository root, run:

```bash
leanblueprint all
```

This compiles the PDF and HTML blueprints and checks every declaration named by
`\lean{...}`. Inspect the rendered output when changing notation, diagrams,
macros, or layout; successful compilation alone does not establish that the
result is readable.
