# Minimal and Strongly Minimal Unary Definable Sets

## Intent and scope

Formalize blueprint [`def:minimality`](../../blueprint/src/content.tex): an infinite unary
definable set `D` is minimal in `M` when every definable subset of `D` is finite or cofinite
in `D`; a defining formula is strongly minimal when its interpretation remains minimal in
every elementary extension.

Provide a local set predicate, formula-and-parameter wrappers, and the elementary-embedding
API needed to use strong minimality in arbitrary target universes. The universe bridge is
part of this capability: a definition restricted to one target universe does not by itself
finish the blueprint node.

The direct consumers explain the interface:

- `def:strongly-minimal-pregeometry` forms `D ∩ acl (A ∪ X)`, so local minimality should
  compose with the existing set-based algebraicity API.
- `lem:strongly-minimal-exchange` introduces new points in an elementary extension and
  applies minimality to fibers with those new parameters.
- `lem:independent-tuples-same-type` and `thm:strongly-minimal-dimension-classification`
  interpret one formula in two elementary extensions of a common base model.
- `thm:omega-stable-has-minimal-formula` needs local minimality, while
  `thm:minimal-formula-strongly-minimal` is a separate upgrade using no Vaughtian pairs.

These consumers guide the definitions; their proofs, exchange, pregeometry, dimension, and
the no-Vaughtian-pair finite-bound lemma are outside this capability. This plan does not
authorize changes to `blueprint/`.

## Existing API and investigation evidence

The repository pins Mathlib `v4.34.1`. Source searches found no model-theoretic minimality
or strong-minimality definition in that version or in the project. Relevant interfaces:

| Interface | Use |
|---|---|
| Mathlib `Set.Definable₁`, `Set.Definable.inter`, `.sdiff`, `.mono` | Unary definability and Boolean operations |
| Mathlib `Set.definable_iff_finitely_definable` | Finite support for arbitrary ambient parameters |
| [`Set.definable₁_iff_exists_realizationSet₁`](../../MorleyCategoricityTheorem/ModelTheory/Definability.lean) | Convert a unary definable set to a formula with assigned parameters |
| [`Formula.realizationSet₁`, `realizationSet_fin_one_equiv`, `infinite_realizationSet_fin_one_iff`](../../MorleyCategoricityTheorem/ModelTheory/Semantics.lean) | Keep the public carrier `Set M` and bridge to `Fin 1 → M` |
| `Formula.exists_fin_params` in the same semantic module | Extract a finite tuple of parameter values |
| [`ElementaryEmbedding.encard_realizations_eq_coe_iff`, `infinite_realizations_iff`](../../MorleyCategoricityTheorem/ModelTheory/ElementaryMaps.lean) | Preserve and reflect finite counts and infinitude across universes |
| [`Language.IsAlgebraicOver`, `algebraicClosure`](../../MorleyCategoricityTheorem/ModelTheory/AlgebraicClosure.lean) | Existing set-based algebraicity consumers |
| [`Theory.IsVaughtianPair`](../../MorleyCategoricityTheorem/ModelTheory/VaughtianPair.lean) | Existing formula, finite parameter tuple, and elementary embedding convention |

`Formula.exists_fin_params` returns `L.Formula (α ⊕ Fin n)`, with the realized variables
first. The public realization-set convention is parameters first, so conversion to
`L.Formula (Fin n ⊕ Fin 1)` requires relabeling. No new variable-order convention is needed.

The initial investigation used ephemeral Lean snippets, with no production declarations.
The following checks succeeded:

- The local definition below elaborates, and its subset and intersection/split versions
  are equivalent.
- Finite sets cannot satisfy the definition, although they satisfy the split dichotomy.
- Unary realization-set infinitude transfers across arbitrary elementary embeddings.
- Formulas with the same parameter layout and assignment that define the same source set
  also define the same set in an elementary target. Different layouts remain an API obligation.
- Uniform finite-count disjunctions for a formula family transfer to all target parameter
  tuples, using `iAlls`, `iExsAtMost`, and `ElementaryEmbedding.map_formula`.
- A small elementary hull in a language expanded by constants retains every named element.

The checked auxiliary proofs whose axioms were inspected used only `propext`,
`Classical.choice`, and `Quot.sound`, without `sorryAx`. The full universe bridge and the
compactness characterization by uniform bounds were not proved. The unchanged library
passed `lake build MorleyCategoricityTheorem`; this is baseline evidence, not completion
of the declarations proposed here.

## Chosen interface

### Local minimality

Proposed declarations live in `FirstOrder.Language` and its `Formula` namespace. Names are
provisional until checked against the implementation context. The intended local body is:

```lean
universe u v w p

namespace FirstOrder.Language

def IsMinimal (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (D : Set M) : Prop :=
  D.Infinite ∧
    (Set.univ : Set M).Definable₁ L D ∧
    ∀ S : Set M, (Set.univ : Set M).Definable₁ L S → S ⊆ D →
      S.Finite ∨ (D \ S).Finite

namespace Formula

def IsMinimal {L : Language.{u, v}} {M : Type w} [L.Structure M]
    {β : Type p} (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  L.IsMinimal (φ.realizationSet₁ a)

end Formula
end FirstOrder.Language
```

`univ.Definable₁` permits all parameters of the ambient model. The defining base `A` is
recorded separately by `A.Definable₁ L D` or by the range of `a`; it does not restrict the
parameters allowed in the subsets being tested. `A` may later enlarge, need not be finite,
and need not lie inside `D`.

Package infinitude and definability in the set predicate so that its meaning does not rely
on external side conditions. Keep `L` explicit on the set predicate and implicit where a
formula determines it. Use an ordinary `Prop`, without a typeclass or new notation.

The basic API should expose infinitude, definability, the finite/cofinite dichotomy, and
the equivalent split form

```lean
∀ S : Set M, (Set.univ : Set M).Definable₁ L S →
  (D ∩ S).Finite ∨ (D \ S).Finite
```

An infinite definable subset of a minimal set is cofinite in that set; a finite set is
not minimal. Include these elementary consequences rather than forcing consumers to
repeatedly unpack conjunctions.

### Strong minimality and interpretation in targets

Retain the formula and assigned parameters. For `e : M ↪ₑ[L] N`, the target set is
`φ.realizationSet₁ (e ∘ a)`. Elementarity gives only
`e '' φ.realizationSet₁ a ⊆ φ.realizationSet₁ (e ∘ a)`; equality is the additional
no-new-realizations condition appearing in Vaughtian pairs.

Use the following semantic definition, with an explicit canonical target universe:

```lean
def FirstOrder.Language.Formula.IsStronglyMinimal
    {L : FirstOrder.Language.{u, v}} {M : Type w} [L.Structure M]
    {β : Type p} (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  ∀ (N : Type (max u v w)) [L.Structure N] (e : M ↪ₑ[L] N),
    φ.IsMinimal (e ∘ a)
```

This skeleton elaborates. Its public meaning must be justified by the arbitrary-target
elimination theorem: for any `N : Type w'` and elementary `e : M ↪ₑ[L] N`, a strongly
minimal `φ` has minimal interpretation at `e ∘ a`. The reverse implication to the canonical
quantifier is immediate. Derive source minimality by applying this interface to the identity
embedding; derive preservation of strong minimality along elementary embeddings by composition.

A free `w'` in the defining body would specify a family of universe-relative predicates,
not quantify internally over all universes. An independently smaller target universe can
make the extension condition vacuous. The chosen bound contains the source and language
universes; its adequacy is a proof obligation, not a consequence of elaboration.

Permit arbitrary parameter index types `β`; each formula has finite support. Use `Fin n`
when extracting existential witnesses or normalizing a splitter, as in `IsVaughtianPair`.
Require no completeness, countability, saturation, or theory-model hypotheses in these
definitions. Document them as model-and-parameter predicates, not properties of an
uninterpreted formula or an arbitrary theory.

## Universe bridge

Work under the canonical-target hypothesis. First obtain source infinitude by applying
it to an elementary embedding into a suitably lifted copy of `M` in the canonical
universe, then reflecting infinitude. Transfer that infinitude to the arbitrary target.
This bootstrap must precede the arbitrary-target theorem; its source-minimality corollary
cannot serve as a premise of its own proof.

Prove that a nonminimal interpretation in the arbitrary target gives a nonminimal
interpretation in a target of type `Type (max u v w)`:

1. Obtain a definable split with both sides infinite. Target infinitude and definability
   of `D` must be established separately, so failure of minimality really yields such a split.
2. Extract a finite parameter tuple `b : Fin n → N` for the splitting formula.
3. Expand `N` by constants indexed by `M ⊕ Fin n`, interpreted by `Sum.elim e b`.
4. Apply Mathlib `exists_small_elementarySubstructure` to this expanded language. Its
   universe is bounded by `max u v w`, and `Substructure.constants_mem` retains the entire
   source image and the splitting parameters.
5. Pass to the elementary reduct in `L`, factor `e` through this hull, and transport the
   small hull to the canonical universe.
6. Reflect infinitude of both split pieces through the hull inclusion, using the existing
   realization-set transfer API. This contradicts canonical-target minimality.

Mathlib provides `constantsOn.structure`, `withConstantsStructure`,
`ElementarySubstructure.subtype`, and induced-structure/shrink transports. The core
constant-retention construction passed a scratch check. The elementary reduct, factorization,
and the complete shrinking argument remain unverified. `exists_small_elementarySubstructure`
without the constant expansion does not promise to retain the source or splitter parameters.

There is a second route via `exists_elementarySubstructure_card_eq` with a prescribed set
containing the source image and `b`. It introduces explicit cardinal inequalities; prefer
the constants route unless the full composition exposes a concrete disadvantage.

Public API must also establish independence of the defining presentation, including
different parameter layouts. Combine the parameters, universally close the equivalence
of the defining formulas, and transfer it by elementarity. Use reindexing and finite
parameter normalization only as needed by actual callers.

## Alternatives and boundaries

- **Only a bundled `L.DefinableSet`.** It stores a set in one model, does not directly supply
  its interpretation in another, and exposes tuple carriers. The unbundled unary predicate
  plus formula interface fits current consumers better.
- **Only a formula predicate.** This carries target interpretations well but adds syntax
  bookkeeping to local algebraicity arguments. Keep the set-level owner and a thin wrapper.
- **A uniform finite-bound definition of strong minimality.** For each `ψ(x, y)`, ask for
  `k : ℕ` such that every `b` makes either `D ∩ ψ(M, b)` or `D \ ψ(M, b)` have `encard ≤ k`.
  The bound depends on `ψ`, not on `b`. This avoids a target-universe parameter and its
  transfer mechanism has been checked, but equivalence with extension semantics requires
  compactness and finite parameter normalization. Retain it as a possible later
  characterization; do not silently replace the blueprint meaning with an unproved equivalence.
- **Restricting tests to the defining base or to transported source parameters.** This
  cannot support the exchange argument with new target parameters.

The infinity requirement and relative complement are essential. An ambient cofinite
condition would wrongly exclude strongly minimal sets whose complement in the model is
infinite. No set-only strong predicate, matroid packaging, rank API, or new notation is
needed for this capability.

## Module ownership and implementation steps

1. Add `MorleyCategoricityTheorem/ModelTheory/Minimality.lean`, documenting
   `def:minimality`, and implement the local definition, split equivalence, basic
   consequences, and formula wrapper.
2. Add the canonical-target strong predicate and prove its arbitrary-target interface,
   using the small-hull construction. Do not mark strong minimality complete with only
   the restricted-universe definition.
3. Prove source minimality, elementary-embedding transport, and presentation independence.
   Check a representative application with parameters new to the target and a different
   target universe.
4. Synchronize the root import file when the module is added. Keep public documentation
   about mathematical meaning and stable interfaces; keep design discussion in this plan.

Start with the local `Definability` and `ElementaryMaps` imports, and Mathlib
`ModelTheory.Skolem` for the universe bridge; add transport imports only as required. Do
not import the project's `AlgebraicClosure`, `OmegaStable`, `VaughtianPair`, `Types`, or
`DefinablyFull` merely because they are consumers. Do not add a reverse import from the
low-level semantic or definability modules, or from algebraic closure.

Generic elementary-reduct or transport lemmas belong at their appropriate elementary-map
layer when they have a useful general statement. Keep minimality-specific hull bookkeeping
private. Do not build a separate general-purpose hull framework for this one use.

Variables and universes must be explicit (`autoImplicit = false`). Keep imports minimal
and acyclic. Definitions and proofs must contain no `sorry` or extra axioms. Keep this
capability's changes outside `blueprint/`.

## Verification and completion

During implementation, use Lean LSP/scratch checks for declaration shapes and proof
exploration. Required build gates follow [CONTRIBUTING.md](../../CONTRIBUTING.md):

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
lake exe checkdecls blueprint/lean_decls
```

The module addition requires the root-import check. New definitions not yet referenced
from the blueprint do not require editing its declaration list; run `checkdecls` as a
compatibility check, as in project CI. Check completed declarations' axioms for `sorryAx`
and inspect their dependencies before reporting them proved.

Acceptance includes:

- Infinite, ambient-parameter, relative-cofinite semantics, with the subset/split equivalence.
- Formula interpretation through `e ∘ a` and tests using arbitrary target parameters.
- A proved arbitrary-target theorem, source minimality, transport, and independence of
  presentation; no countability or completeness assumptions added to hide a universe gap.
- Boundary checks for finite `D`, parameter-free formulas, infinite parameter bases with
  finite formula support, and source/target models in different universes.
- Successful applicable build/import/declaration checks and no changes to `blueprint/`.

For this plan-only change, review Markdown, relative links, and the diff; no Lean module
is added or changed. The implementation checks above are future completion requirements,
not claims that the proposed declarations already exist.

## Deferred consumers

The local existence theorem should reuse `IsOmegaStable.false_of_formula_splitting` from
[OmegaStable](../../MorleyCategoricityTheorem/ModelTheory/OmegaStable.lean), with an infinite
root realization set. It needs model infinitude explicitly: the current Lean definition of
omega-stability permits finite models, while the blueprint assumes infinite models globally.
The minimal-to-strong upgrade and uniform finite bounds without Vaughtian pairs remain
separate results.

Follow the existing [algebraic-closure plan](algebraic-closure.md) for downstream geometry:
exchange is on carrier `D`, with `X ⊆ D` and `c ∈ D`; the present capability neither proves
exchange nor changes its blueprint statement. Any later blueprint declaration mapping
requires an explicitly authorized blueprint change.
