import Mathlib.ModelTheory.Equivalence

/-!
# Equivalence of formulas over the constant expansion

This module mirrors `Mathlib.ModelTheory.Equivalence` under the same module name, recording how
semantic consequence `⟹[T]` and semantic equivalence `⇔[T]` between formulas commute with the
syntactic translation `Formula.equivSentence` into the constant expansion `L[[α]]`: a formula-level
implication (resp. equivalence) over `T` holds exactly when the corresponding sentences over the
expanded theory `(L.lhomWithConstants α).onTheory T` hold.

These statements are intended to be upstreamed to `Mathlib.ModelTheory.Equivalence`, after which
this module can be removed and its imports redirected.

## TODO

- Generalize the underlying validity transport from formulas to bounded formulas.  For
  `φ : L.BoundedFormula α n`, first pass to `φ.toFormula`, whose free-variable context is
  `α ⊕ Fin n`, and then apply `Formula.equivSentence`.  The resulting theorem should identify
  `T ⊨ᵇ φ` with validity of the translated sentence over the constant expansion by
  `α ⊕ Fin n`; bounded-formula versions of the implication and equivalence theorems should be
  derived from this single result.
- Extend binary semantic consequence to consequence from a set `Γ : Set (L.Formula α)`.  Under
  `Formula.equivSentence`, consequence from `Γ` over `T` should correspond to sentence consequence
  from `Formula.equivSentence '' Γ` together with `(L.lhomWithConstants α).onTheory T`.  The
  implication theorem above is the singleton-antecedent case.
- Package `Formula.equivSentence` as an equivalence of the semantic preorders determined by
  `Theory.Imp`.  It should descend through `Theory.iffSetoid` to an equivalence of formulas modulo
  semantic equivalence and, once the relevant quotient API exists, to an isomorphism of the
  corresponding Lindenbaum--Tarski Boolean algebras.
- Investigate the analogous transport along a general language homomorphism.  Reducts give the
  forward preservation direction, whereas reflection requires an expansion-lifting hypothesis
  (available, for example, for suitable injective language maps); this extra hypothesis should be
  explicit rather than built into a theorem about arbitrary language homomorphisms.
-/

universe u v w

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

/-- Semantic consequence over `T` commutes with the translation of formulas to sentences with
constants: `φ ⟹[T] ψ` holds exactly when `Formula.equivSentence φ` implies `Formula.equivSentence ψ`
over the constant-expanded theory. -/
theorem imp_iff_imp_of_equivSentence {φ ψ : L.Formula α} :
    (φ ⟹[T] ψ) ↔ (Formula.equivSentence φ) ⟹[(L.lhomWithConstants α).onTheory T]
      (Formula.equivSentence ψ) := by
  rw [Theory.Imp, models_formula_iff_onTheory_models_equivSentence]
  rfl

/-- Semantic equivalence over `T` commutes with the translation of formulas to sentences with
constants: `φ ⇔[T] ψ` holds exactly when `Formula.equivSentence φ` is equivalent to
`Formula.equivSentence ψ` over the constant-expanded theory. -/
theorem iff_iff_iff_of_equivSentence {φ ψ : L.Formula α} :
    (φ ⇔[T] ψ) ↔ (Formula.equivSentence φ) ⇔[(L.lhomWithConstants α).onTheory T]
      (Formula.equivSentence ψ) := by
  rw [Theory.Iff, models_formula_iff_onTheory_models_equivSentence]
  rfl

end Theory

end Language

end FirstOrder
