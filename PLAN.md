# Plan: Type Spaces and Partial Elementary Embeddings

## Target

Implement blueprint node `lem:type-space-homeomorphism` from
`blueprint/src/content.tex`:

> If `A ⊆ M` and a partial elementary map sends `A` onto `B ⊆ N`, then the spaces of
> complete `α`-types over `A` and `B` are homeomorphic.

The intended public declaration is a bundled homeomorphism in the
`FirstOrder.Language.PartialElementaryEmbedding` namespace:

```lean
noncomputable def completeTypeOverHomeomorph
    (f : A ↪ₚₑ[L] B) (α : Type x) :
    L.CompleteTypeOver A α ≃ₜ L.CompleteTypeOver B α
```

The existing definition requires `f` to be surjective onto its declared codomain `B`, so `B`
represents the image `f(A)` appearing in the blueprint.

## Existing interface

- `PartialElementaryEmbedding.map_formula'` preserves formulas indexed by `Fin n`.
- `PartialElementaryEmbedding.toEquiv` gives the underlying equivalence `A ≃ B`.
- `LEmbedding.lhomWithConstantsMap` embeds `L[[A]]` into `L[[B]]` along an embedding of
  parameter types.
- `CompleteTypeOver L A α` abbreviates the complete types over
  `L[[A]].completeTheory M`.
- `CompleteType.isTopologicalBasis_range_typesWith` supplies the basic clopen basis of the Stone
  topology.

No current project or Mathlib declaration directly transports complete types, maximal theories,
or their topology along a parameter-language equivalence.

## Phase 1: Formula preservation for arbitrary variable types

Extend `PartialElementaryEmbedding` with formula-preservation lemmas matching the public Mathlib
interface for total elementary embeddings:

```lean
theorem PartialElementaryEmbedding.map_boundedFormula ...

@[simp]
theorem PartialElementaryEmbedding.map_formula ...
```

Derive these from `map_formula'` by restricting to the finite set of free variables and identifying
that finite subtype with `Fin n`. Keep the source and target assignments visibly factored through
the subset inclusions `A → M` and `B → N`.

This phase belongs in `ModelTheory/PartialEmbedding.lean` and must not change the structure fields
or the meaning of partial elementarity.

## Phase 2: Equivalences of languages with renamed constants

Add a language equivalence induced by an equivalence of parameter types:

```lean
def LEquiv.lhomWithConstantsCongr
    (L : Language) (e : α ≃ β) : L[[α]] ≃ᴸ L[[β]]
```

Its forward map should be `L.lhomWithConstantsMap e`, and its inverse should use `e.symm`. Also
provide the minimal helper that extends a language equivalence by an unchanged type of new
constants:

```lean
def LEquiv.addConstants (e : L ≃ᴸ L') (α : Type*) :
    L[[α]] ≃ᴸ L'[[α]]
```

Place reusable syntax-only constructions in `ModelTheory/LanguageEmbedding.lean`. Prove the
composition identities needed later rather than relying on large unfolded `simp` calls.

## Phase 3: Correspondence of parameter-expanded complete theories

For `f : A ↪ₚₑ[L] B`, instantiate the parameter-language equivalence with `f.toEquiv` and prove
that it carries the complete theory of `M` with constants from `A` to the complete theory of `N`
with constants from `B`:

```lean
theorem PartialElementaryEmbedding.map_completeTheory
    (f : A ↪ₚₑ[L] B) :
    f.parameterLEquiv.toLHom.onTheory (L[[A]].completeTheory M) =
      L[[B]].completeTheory N
```

Prove this by sentence extensionality:

1. Rewrite membership in `completeTheory` as realization.
2. Convert a sentence with named parameters using `BoundedFormula.constantsVarsEquiv`.
3. Apply the arbitrary-variable preservation theorem from Phase 1.
4. Rewrite the result as realization of the renamed sentence in `N`.
5. Use bijectivity of the sentence map to discharge image membership.

This is the main semantic bottleneck. Isolate coercion and function-composition identities in
small lemmas so the final theorem does not expose temporary constant structures.

## Phase 4: Generic transport of complete types

In a new module `ModelTheory/TypeSpaceHomeomorphism.lean`, define transport of complete types along
a language equivalence that identifies the base theories. The forward map sends the underlying
maximal theory through the induced equivalence after adding the free-variable constants.

Establish:

- containment of the transported base theory;
- preservation of satisfiability under the language equivalence;
- preservation of maximality, using surjectivity on sentences and compatibility with negation;
- inverse laws using the inverse language equivalence;
- a formula- or sentence-membership theorem for the transported complete type.

Keep low-level image and maximal-theory constructions private unless another caller needs them.
Expose the complete-type equivalence and its membership rule.

## Phase 5: Stone-space topology

Before constructing the homeomorphism, prove that the complete-type equivalence transports basic
open sets exactly. A suitable normal form is:

```lean
theorem preimage_typesWith ... :
    completeTypeEquiv e h ⁻¹' T'.typesWith σ =
      T.typesWith ((e.addConstants α).onSentence.symm σ)
```

Use `CompleteType.isTopologicalBasis_range_typesWith` and
`IsTopologicalBasis.continuous_iff` to prove continuity of the forward and inverse maps. Package
them as a `Homeomorph`, then specialize with `f.toEquiv` and `f.map_completeTheory` to obtain
`PartialElementaryEmbedding.completeTypeOverHomeomorph`.

Retain an explicit basic-open transport theorem as public API. It is the useful downstream form
for moving isolating formulas in the proof of the prime-extension theorem.

## File plan

1. `MorleyCategoricityTheorem/ModelTheory/PartialEmbedding.lean`
   - arbitrary-variable preservation for partial elementary embeddings;
   - parameter-expanded semantic transport helpers if they require structure semantics.
2. `MorleyCategoricityTheorem/ModelTheory/LanguageEmbedding.lean`
   - equivalences for renamed constants and unchanged added constants.
3. `MorleyCategoricityTheorem/ModelTheory/TypeSpaceHomeomorphism.lean`
   - generic complete-type equivalence and topology;
   - specialization to partial elementary embeddings.
4. `MorleyCategoricityTheorem.lean`
   - import the new module.
5. `blueprint/src/content.tex`
   - after the Lean declaration is complete, add its fully qualified `\lean{...}` name and
     `\leanok` to `lem:type-space-homeomorphism`.

Prefer the new module over importing the topology of complete types into the foundational partial
embedding module. Imports must remain acyclic.

## Risks and proof checkpoints

- The finite-support lift from `Fin n` is likely to be the first elaboration-heavy proof; mirror
  Mathlib's `ElementaryEmbedding.map_boundedFormula` closely.
- The two levels of added constants must remain distinct: parameters (`A` or `B`) belong to the
  base language of the type space, while `α` indexes the free variables of each complete type.
- Orient theory equalities and sentence maps consistently. Prove the inverse theory equality
  immediately after the forward one to avoid repeated rewriting later.
- Do not replace the target with mere cardinal equality or an unbundled bijection. The blueprint
  requires a homeomorphism and the downstream proof needs control of basic opens.
- Do not add `\leanok` while any target declaration or local dependency contains `sorry`.

## Completion criteria

- `PartialElementaryEmbedding.completeTypeOverHomeomorph` exists with the intended source and
  target `CompleteTypeOver` spaces.
- Forward and inverse membership rules are available without unfolding maximal theories.
- Basic clopen sets are transported explicitly.
- The new declarations contain no `sorry`.
- Root imports include the new module and remain acyclic.
- Blueprint node `lem:type-space-homeomorphism` names the compiled declaration and has accurate
  status markers.

## Validation for the implementation phase

Because the implementation will add a Lean module and update the blueprint, run from the project
root:

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
leanblueprint all
```

These commands belong to the later implementation phase; producing this plan does not execute
them.
