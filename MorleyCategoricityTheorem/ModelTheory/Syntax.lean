/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Syntax

/-!
# Additional First-Order Syntax

This file extends `Mathlib.ModelTheory.Syntax` with formula constructors needed for Morley's
categoricity theorem. Its declarations are intended to migrate directly to
`Mathlib/ModelTheory/Syntax.lean`, near `Formula.iExs` and `Formula.iExsUnique`.

This is the syntax-only layer. It must not depend on structures, formula realization, set
cardinality, or elementary embeddings.

## Main definitions

- `FirstOrder.Language.Formula.iExsAtLeast`: assert the existence of `n` pairwise distinct
  realizing `β`-tuples.
- `FirstOrder.Language.Formula.iExsAtMost`: defined as the negation of having at least `n + 1`
  realizations.
- `FirstOrder.Language.Formula.iExsExactly`: the conjunction of the corresponding lower and upper
  bounds.
- `FirstOrder.Language.Formula.existsExactlyLeft`: a convenience wrapper for formulas whose
  variables are ordered as `β ⊕ α`, implemented by relabeling with `Sum.swap`.

## Construction outline

For `φ : L.Formula (α ⊕ β)`, the lower-bound constructor quantifies a witness block indexed by
`Fin n × β`. The assignment at index `i : Fin n` represents one candidate tuple. The body asserts
that every candidate realizes `φ` and that candidates at distinct indices differ in at least one
coordinate.

The coordinatewise equality conjunction must handle an empty `β` correctly: there is exactly one
empty tuple. Helpers for relabeling a candidate, comparing two tuples, and indexing unequal pairs
are local `let` bindings inside `iExsAtLeast`. The semantic layer can then unfold the public
constructor without turning implementation details into declarations that also need to be migrated.

## Design constraints

- Require `[Finite β]`, because a single first-order formula can quantify the complete assignment
  only for a finite tuple of variables.
- Do not require `[Finite α]`, because the parameter variables remain free.
- Order variables as `α ⊕ β`, consistently with Mathlib's `Formula.iExs` / `Formula.iExsUnique`.
- Keep the natural-number API primary; defer an arbitrary finite index type until it is needed.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α β : Type*}

namespace Formula

variable (β) in
/-- Asserts that `φ` has at least `n` pairwise distinct realizing `β`-tuples, with free variables
of type `α`.

The formula existentially quantifies a witness block of type `Fin n × β`, asserts that each
candidate realizes `φ`, and that candidates at distinct indices differ in at least one coordinate.
When `β` is empty there is exactly one empty tuple, so the coordinatewise equality conjunction is
vacuously true and its negation is false. -/
noncomputable def iExsAtLeast [Finite β] (n : ℕ) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let realizeAt (i : Fin n) : L.Formula (α ⊕ (Fin n × β)) :=
    φ.relabel (Sum.map id fun b ↦ (i, b))
  let tupleNe (i j : Fin n) : L.Formula (α ⊕ (Fin n × β)) :=
    (iInf fun b : β ↦
      (Term.var (Sum.inr (i, b))).equal (Term.var (Sum.inr (j, b)))).not
  let NePair := {ij : Fin n × Fin n // ij.1 ≠ ij.2}
  let witnessesRealize : L.Formula (α ⊕ (Fin n × β)) :=
    iInf fun i : Fin n ↦ realizeAt i
  let witnessesDistinct : L.Formula (α ⊕ (Fin n × β)) :=
    iInf fun ij : NePair ↦ tupleNe ij.1.1 ij.1.2
  let body := witnessesRealize ⊓ witnessesDistinct
  body.iExs (Fin n × β)

variable (β) in
/-- Asserts that `φ` has at most `n` realizing `β`-tuples, with free variables of type `α`.

Defined as the negation of having at least `n + 1` realizations. -/
noncomputable def iExsAtMost [Finite β] (n : ℕ) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (φ.iExsAtLeast β (n + 1)).not

variable (β) in
/-- Asserts that `φ` has exactly `n` realizing `β`-tuples, with free variables of type `α`.

Defined as the conjunction of the corresponding lower and upper bounds. -/
noncomputable def iExsExactly [Finite β] (n : ℕ) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  φ.iExsAtLeast β n ⊓ φ.iExsAtMost β n

/-- Convenience wrapper for formulas whose variables are ordered as `β ⊕ α` rather than `α ⊕ β`.

Implemented by relabeling with `Sum.swap` and then applying `iExsExactly`. -/
noncomputable def existsExactlyLeft [Finite β] (φ : L.Formula (β ⊕ α)) (n : ℕ) : L.Formula α :=
  (φ.relabel Sum.swap).iExsExactly β n

end Formula

end Language

end FirstOrder
