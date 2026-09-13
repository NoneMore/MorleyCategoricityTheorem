/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Bundled
import MorleyCategoricityTheorem.ModelTheory.ElementaryMaps

/-!
# Vaughtian pairs

A Vaughtian pair for a theory `T` is a proper elementary pair `M ≺ N` of models of `T` together
with a one-variable formula, with parameters from `M`, whose realization set is infinite and does
not grow when passing from `M` to `N`.  Vaughtian pairs control the two-cardinal behaviour of `T`:
their absence forces every infinite parameter-definable subset of a model to have full cardinality,
while their presence produces an `(ℵ₁, ℵ₀)`-model.

## Main definitions

- `FirstOrder.Language.Theory.IsVaughtianPair`: a Vaughtian pair for a theory `T`, presented as a
  non-surjective elementary embedding `M ↪ₑ[L] N` together with the witnessing formula and
  parameter tuple.
- `FirstOrder.Language.Theory.HasVaughtianPair`: the theory `T` admits a Vaughtian pair.

## Main results

- `FirstOrder.Language.ElementaryEmbedding.image_realizations_subset`: the image of the
  `M`-realization set of a unary formula is always contained in the corresponding `N`-realization
  set.
- `FirstOrder.Language.Theory.isVaughtianPair_iff`: the "unchanged in `N`" condition can be
  equivalently stated as the absence of new realizations, because elementarity supplies the
  reverse inclusion.

## Implementation notes

The pair `M ≼ N` is encoded as an elementary embedding `e : M ↪ₑ[L] N`, and `M ≠ N` as
`¬ Function.Surjective e`.  Parameters are a finite tuple indexed by `Fin n`, matching
`Formula.exists_fin_params`, while the single distinguished variable is indexed by `Fin 1`; this
avoids the universe bookkeeping that an existential parameter *type* would introduce.  The
realization set is written with `Set.Infinite`, and "unchanged in `N`" as the equality of the
`N`-realization set with the image of the `M`-realization set.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

namespace ElementaryEmbedding

/-- The image of the `M`-realization set of a unary formula with parameters from `M`, under an
elementary embedding, is contained in the corresponding `N`-realization set.

This is the unary, parameter-tuple form of `ElementaryEmbedding.realizations_embedding`.  The
reverse inclusion need not hold, and it fails exactly when the pair is Vaughtian. -/
theorem image_realizations_subset (e : M ↪ₑ[L] N) (n : ℕ)
    (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M) :
    (e : M → N) '' {x : M | φ.Realize (Sum.elim a (fun _ : Fin 1 => x))} ⊆
      {y : N | φ.Realize (Sum.elim ((e : M → N) ∘ a) (fun _ : Fin 1 => y))} := by
  rintro y ⟨x, hx, rfl⟩
  show φ.Realize (Sum.elim ((e : M → N) ∘ a) (fun _ : Fin 1 => e x))
  have hfun : (Sum.elim ((e : M → N) ∘ a) (fun _ : Fin 1 => e x)) =
      (e : M → N) ∘ (Sum.elim a (fun _ : Fin 1 => x)) := by
    ext i
    cases i <;> rfl
  rw [hfun]
  exact (e.map_formula φ (Sum.elim a (fun _ => x))).mpr hx

end ElementaryEmbedding

namespace Theory

/-- A Vaughtian pair for a theory `T`.

It consists of a non-surjective elementary embedding `e : M ↪ₑ[L] N` between two models of `T`,
together with a one-variable formula `φ` with parameters `a` from `M` whose `M`-realizations form
an infinite set and whose `N`-realizations are exactly the image of that set.  Since `e` is
elementary, the latter condition is equivalent to saying that passing to `N` creates no new
realizations; see `Theory.isVaughtianPair_iff`. -/
def IsVaughtianPair (T : L.Theory) (e : M ↪ₑ[L] N) : Prop :=
  M ⊨ T ∧ N ⊨ T ∧ ¬ Function.Surjective e ∧
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M),
      Set.Infinite {x : M | φ.Realize (Sum.elim a (fun _ : Fin 1 => x))} ∧
      {y : N | φ.Realize (Sum.elim ((e : M → N) ∘ a) (fun _ : Fin 1 => y))} =
        (e : M → N) '' {x : M | φ.Realize (Sum.elim a (fun _ : Fin 1 => x))}

/-- Characteristic form of a Vaughtian pair in which "unchanged in `N`" is expressed as the
absence of new realizations: it suffices to show that every `N`-realization is the image of an
`M`-realization.  The reverse inclusion is automatic by
`ElementaryEmbedding.image_realizations_subset`. -/
theorem isVaughtianPair_iff (T : L.Theory) (e : M ↪ₑ[L] N) :
    IsVaughtianPair T e ↔
      M ⊨ T ∧ N ⊨ T ∧ ¬ Function.Surjective e ∧
        ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M),
          Set.Infinite {x : M | φ.Realize (Sum.elim a (fun _ : Fin 1 => x))} ∧
          {y : N | φ.Realize (Sum.elim ((e : M → N) ∘ a) (fun _ : Fin 1 => y))} ⊆
            (e : M → N) '' {x : M | φ.Realize (Sum.elim a (fun _ : Fin 1 => x))} := by
  simp only [IsVaughtianPair]
  refine and_congr_right fun _ => and_congr_right fun _ => and_congr_right fun _ => ?_
  constructor
  · rintro ⟨n, φ, a, hinf, heq⟩
    exact ⟨n, φ, a, hinf, heq.subset⟩
  · rintro ⟨n, φ, a, hinf, hsub⟩
    exact ⟨n, φ, a, hinf,
      Set.Subset.antisymm hsub (ElementaryEmbedding.image_realizations_subset e n φ a)⟩

/-- A theory has a Vaughtian pair if it has two models related by a Vaughtian pair. -/
def HasVaughtianPair (T : L.Theory) : Prop :=
  ∃ (M N : ModelType.{u, v, w} T) (e : M ↪ₑ[L] N), IsVaughtianPair T e

end Theory

end Language

end FirstOrder
