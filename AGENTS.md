# AGENTS.md

## Blueprint Mathematical Narrative

The blueprint should remain mathematical. It should read like ordinary
mathematical notes, not like a Lean proof script.

The document should stay in ordinary mathematical order:

1. foundational definitions and conventions;
2. basic constructions;
3. intermediate lemmas and propositions;
4. main theorems.

Mention Lean names only when linking a blueprint item to an existing formal
declaration.

## Leanblueprint Source Layout

These conventions follow the `leanblueprint` project description:
https://github.com/PatrickMassot/leanblueprint.

The blueprint source lives under `blueprint/src`.

- Write the mathematical blueprint in `blueprint/src/content.tex`, or in files
  imported from `content.tex` if the blueprint is later split.
- Keep `blueprint/src/web.tex` and `blueprint/src/print.tex` as output-specific
  preambles. Do not put mathematical blueprint content there.
- Put macros shared by both output formats in `blueprint/src/macros/common.tex`.
  Put macros that must differ between HTML and PDF output in
  `blueprint/src/macros/web.tex` or `blueprint/src/macros/print.tex`.
- Use theorem-like environments that are collected by the dependency graph:
  `definition`, `lemma`, `proposition`, `theorem`, and `corollary`, unless the
  blueprint preamble is deliberately changed.
- Every central graph node should have a stable LaTeX label, with predictable
  prefixes such as `def:`, `lem:`, `prop:`, `thm:`, and `cor:`.

## Draft Blueprint Editing

When a user asks to revise a draft blueprint, edit only the corresponding file
under `blueprint/src/drafts/`. Do not also update `blueprint/src/content.tex`
or other formal blueprint entrypoints unless the user explicitly asks to
promote or synchronize the draft into the formal blueprint.

## Leanblueprint Special Macros

Use the leanblueprint macros to record formalization status and graph
dependencies. They should appear near the start of the surrounding environment,
after `\label{...}` and before the mathematical prose.

- `\lean{...}` lists the Lean declaration names corresponding to the surrounding
  definition or statement. Include namespaces. Use comma-separated names when
  one blueprint item is formalized by more than one Lean declaration. Do not use
  `\lean` for merely aspirational names that do not yet exist and type-check;
  `leanblueprint checkdecls` is expected to find every listed declaration.
- `\leanok` claims the surrounding environment is fully formalized. On a
  definition or statement, use it only when the Lean declaration exists and
  matches the blueprint item. Inside a `proof` environment, use it only when the
  Lean proof of that item contains no local `sorry`. A theorem whose proof uses
  other project lemmas that still contain `sorry` is still only "proved modulo
  lemmas" in status reports.
- `\uses{label-a,label-b}` lists LaTeX labels used by the surrounding
  environment. In a definition/theorem/lemma environment, list only the labels
  needed to state that item. In a `proof` environment, list proof-only
  dependencies. When revising old blueprint text, prefer moving proof-only
  dependencies into an explicit `proof` environment instead of adding mixed
  statement/proof dependencies to the theorem statement.
- `\notready` marks a surrounding environment as not ready to be formalized,
  typically because more blueprint work is still needed. Do not combine it with
  `\leanok`; remove it once the item has a stable formalization target.
- `\discussion{123}` records the GitHub issue number where the surrounding
  definition or statement is discussed. Use the bare issue number.
- `\proves{label}` is used inside a `proof` environment when the proof does not
  immediately follow the statement it proves. Omit it for the usual case where
  the proof directly follows its statement.
- `\mathlibok` marks a node whose corresponding result has already been merged
  into Mathlib. Use it only for results supplied by the current Mathlib
  dependency, not for declarations local to this repository.

For a formalized item with an immediate proof, the preferred shape is:

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

For a planned item, omit `\lean` and `\leanok`, and use `\notready` until the
statement is stable enough to formalize.
