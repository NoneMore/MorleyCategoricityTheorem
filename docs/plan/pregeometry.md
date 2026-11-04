# Strongly Minimal Pregeometry

## Scope and status

Blueprint [`def:strongly-minimal-pregeometry`](../../blueprint/src/content.tex) defines the closure
operator `cl_A(X) = D ∩ acl (A ∪ X)` on a strongly minimal set `D` definable over `A`, and
[`lem:strongly-minimal-closure-laws`](../../blueprint/src/content.tex) records that `cl_A` is
reflexive, monotone, idempotent and has finite character.  Both are implemented in
[`Pregeometry.lean`](../../MorleyCategoricityTheorem/ModelTheory/Pregeometry.lean), which imports
only [`AlgebraicClosure.lean`](../../MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean).

Exchange, the pregeometry structure, independence and dimension are deferred; see **Deferred
follow-ups**.  Both nodes carry `\lean{}`/`\leanok` in the blueprint, and their declarations are
listed in `blueprint/lean_decls`.

## Intent

The operator is the closure of the pregeometry attached to a strongly minimal set: it feeds
`lem:strongly-minimal-exchange`, then `prop:strongly-minimal-pregeometry`, then the independence,
basis and dimension API of `def:strongly-minimal-independence`.  Those later nodes decide the
interface, so the definition has to be usable both as a set-valued operator (`b ∈ cl_A X`,
`cl_A X ⊆ D`) and in finite-witness arguments (`X` replaced by a finite `F ⊆ X`).

The closure laws themselves use neither strong minimality nor the definability of `D` over `A`;
they are laws of algebraic closure restricted to an arbitrary set.  The definition and the four
laws are therefore stated for arbitrary `A` and `D`, which is the weakest faithful form of the
blueprint nodes.  Strong minimality enters only with exchange.

## Existing API

Mathlib `v4.34.1` has no pregeometry and no model-theoretic algebraic closure.  It has closed
operators (`ClosureOperator` in `Mathlib/Order/Closure.lean`) and infinite matroids under
`Mathlib/Combinatorics/Matroid/`, both relevant only once exchange exists.

The project's [`AlgebraicClosure.lean`](../../MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean)
already proves the `acl`-level laws that `cl_A` inherits.  The blueprint's four laws are
restatements of them, not new mathematics:

| law | `acl`-level declaration | use in `cl_A` |
|---|---|---|
| reflexive | `subset_algebraicClosure` | `X ⊆ D → X ⊆ cl_A X` |
| monotone | `algebraicClosure_mono` | `X ⊆ Y → cl_A X ⊆ cl_A Y` |
| idempotent | `algebraicClosure_idem` | `cl_A (cl_A X) = cl_A X` |
| finite character | `mem_algebraicClosure_iff_exists_finset` | `b ∈ cl_A X` iff a finite `F ⊆ X` witnesses it |
| absorption | `algebraicClosure_union_eq` | not needed yet |

## Chosen interface

The definition is unbundled, lives in `FirstOrder.Language` and takes the language explicitly
(the argument order is base, ambient set, closed set):

```lean
def relAlgebraicClosure (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (A D X : Set M) : Set M :=
  D ∩ L.algebraicClosure (A ∪ X)
```

Lemmas take `{L}` implicitly, since every statement mentions `L.relAlgebraicClosure`; this is the
convention already used by the `acl` API.

```lean
@[simp] theorem mem_relAlgebraicClosure_iff :
  b ∈ L.relAlgebraicClosure A D X ↔ b ∈ D ∧ L.IsAlgebraicOver (A ∪ X) b
theorem relAlgebraicClosure_subset : L.relAlgebraicClosure A D X ⊆ D
theorem subset_relAlgebraicClosure (hXD : X ⊆ D) : X ⊆ L.relAlgebraicClosure A D X
theorem relAlgebraicClosure_mono (hXY : X ⊆ Y) :
  L.relAlgebraicClosure A D X ⊆ L.relAlgebraicClosure A D Y
theorem relAlgebraicClosure_idem :
  L.relAlgebraicClosure A D (L.relAlgebraicClosure A D X) = L.relAlgebraicClosure A D X
theorem mem_relAlgebraicClosure_iff_exists_finset :
  b ∈ L.relAlgebraicClosure A D X ↔
    ∃ F : Finset M, (F : Set M) ⊆ X ∧ b ∈ L.relAlgebraicClosure A D (F : Set M)
```

Design points:

- **No notation, no `ClosureOperator` bundle.**  The blueprint orders the closure laws before
  exchange and before the pregeometry node, and no current caller consumes a bundled operator.
  A closure operator built here could not yet satisfy its interesting laws (exchange), and a
  notation for `cl_A` has no consumer until the independence API.
- **`D` is an ordinary parameter.**  Restricting the codomain to `D` by a subtype or a bundled
  `DefinableSet` would re-type every parameter set used by the later nodes, which all speak of
  `X ⊆ D` and `X ∪ {c}` for `c ∈ D`.
- **Reflexivity is the only law with a hypothesis.**  `X ⊆ cl_A X` asserts membership in `D`, so it
  is false for any element of `X \ D`; hence `X ⊆ D`.  Monotonicity, idempotence and finite
  character hold for arbitrary `X`.
- **Idempotence is unconditional.**  `cl_A (cl_A X) ⊆ cl_A X` because
  `A ∪ (D ∩ acl (A ∪ X)) ⊆ acl (A ∪ X)` and `acl` is idempotent; the reverse inclusion holds
  because every element of `cl_A X` is one of the adjoined parameters, hence algebraic over them.
  The archived [algebraic-closure plan](archive/algebraic-closure.md) records the opposite for the
  first inclusion; that remark conflates idempotence with reflexivity, which is the law that needs
  `X ⊆ D`.
- **Finite character uses the `Finset` form** to match `mem_algebraicClosure_iff_exists_finset`, so
  exchange can induct on the witness.  The forward direction first obtains a finite witness
  `F ⊆ A ∪ X` from the `acl`-level finite character and then filters out the parameters already in
  `A`, leaving a finite `F' ⊆ X` with `b ∈ acl (A ∪ F')`.

## Constraints

- [`Pregeometry.lean`](../../MorleyCategoricityTheorem/ModelTheory/Pregeometry.lean) imports only
  `AlgebraicClosure`; it must not pull in `Minimality`, the type-space layer, or compactness.
- No acl-level law is reproved; the `cl_A` proofs are one-line consequences of the table above.
- No `ClosureOperator`, matroid, dimension, notation or `DefinableSet`-valued API before exchange
  has a caller.  The archived plan's exchange counterexamples and `cRk`-versus-`eRk` requirement
  still constrain that follow-up.
- Variables are explicit (`autoImplicit = false`), and the module is registered in
  `MorleyCategoricityTheorem.lean` for `lake exe mk_all --check`.

## Deferred follow-ups

| item | state |
|---|---|
| exchange (`lem:strongly-minimal-exchange`) | Needs strong minimality, so a separate module importing `Pregeometry` and `Minimality`.  The blueprint's free `c` is refuted by the archived plan's counterexample, and the standard form carries `X ⊆ D` and `c ∈ D`. |
| pregeometry (`prop:strongly-minimal-pregeometry`) | Define the pregeometry structure (closure laws plus exchange) or build the matroid; Mathlib has neither.  Augmentation is not available before exchange. |
| independence, bases, dimension (`def:strongly-minimal-independence`) | Built on the pregeometry; a matroid-based `dim_A` must be the cardinal-valued `cRk`, and `M.closure X = D ∩ acl (A ∪ X)` is a proof obligation, not a definitional equality. |
| cardinality bound (`lem:algebraic-closure-cardinality`) | Independent of `cl_A`; needs a canonical enumeration of formulas with finite parameter tuples, so it belongs to the `acl` capability. |

## Validation

- `lake build MorleyCategoricityTheorem` succeeds with the new module registered.
- `lake exe mk_all --check` reports `No update necessary`.
- `FirstOrder.Language.relAlgebraicClosure_idem` and
  `FirstOrder.Language.mem_relAlgebraicClosure_iff_exists_finset` use only `propext`,
  `Classical.choice` and `Quot.sound`; there is no `sorry` in the module.
- `lake exe checkdecls blueprint/lean_decls` succeeds with both nodes' declarations listed.
