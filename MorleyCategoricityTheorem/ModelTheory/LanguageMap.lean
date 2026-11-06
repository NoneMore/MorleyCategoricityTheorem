import Mathlib.ModelTheory.LanguageMap
import Mathlib.ModelTheory.Syntax

/-!
# Language maps

This file contains auxiliary results about language maps and expansions by constants. In
particular, it records the functoriality of the sum map `LHom.sumMap` (`LHom.sumMap_id`,
`LHom.sumMap_comp`) and the transport of sets of formulas along a language map
(`LHom.onFormulaSet`).

The formula-set transport API follows the design of the reference project
[`NoneMore/StabilityTheory`](https://github.com/NoneMore/StabilityTheory); its statements are
reproved here against this repository's `LHom.onFormula` API.
-/

universe u v w w' u' v' u'' v'' w''

namespace FirstOrder

namespace Language

namespace LHom

section FormulaSet

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}
variable {α : Type w''}

/-- Transports a set of formulas along a language homomorphism. -/
def onFormulaSet (φ : L →ᴸ L') (S : Set (L.Formula α)) : Set (L'.Formula α) :=
  φ.onFormula '' S

@[simp]
theorem mem_onFormulaSet {φ : L →ᴸ L'} {S : Set (L.Formula α)} {ψ : L'.Formula α} :
    ψ ∈ φ.onFormulaSet S ↔ ∃ θ ∈ S, φ.onFormula θ = ψ :=
  Iff.rfl

@[simp]
theorem onFormulaSet_id (L : Language.{u, v}) (S : Set (L.Formula α)) :
    (LHom.id L).onFormulaSet S = S := by
  simp [onFormulaSet, LHom.onFormula]

@[simp]
theorem onFormulaSet_comp (g : L' →ᴸ L'') (f : L →ᴸ L') (S : Set (L.Formula α)) :
    g.onFormulaSet (f.onFormulaSet S) = (g.comp f).onFormulaSet S := by
  simp only [onFormulaSet, LHom.onFormula, LHom.comp_onBoundedFormula]
  exact Set.image_image ..

theorem onFormulaSet_mono (f : L →ᴸ L') {S T : Set (L.Formula α)} (hST : S ⊆ T) :
    f.onFormulaSet S ⊆ f.onFormulaSet T :=
  Set.image_mono hST

end FormulaSet

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure N] [L[[M]].Structure N]
variable [(L.lhomWithConstants M).IsExpansionOn N]

/-- The sum map of two identity language maps is the identity map. -/
@[simp]
theorem sumMap_id (L L' : Language) :
    (LHom.id L).sumMap (LHom.id L') = LHom.id (L.sum L') := by
  ext n c <;> cases c <;> rfl

/-- The sum map is compatible with composition of language maps. -/
theorem sumMap_comp {L₁ L₂ L₃ L₁' L₂' L₃' : Language}
    (φ : L₁ →ᴸ L₂) (ψ : L₁' →ᴸ L₂') (φ' : L₂ →ᴸ L₃) (ψ' : L₂' →ᴸ L₃') :
    (φ'.sumMap ψ').comp (φ.sumMap ψ) = (φ'.comp φ).sumMap (ψ'.comp ψ) := by
  ext n c <;> cases c <;> rfl

theorem lhomWithConstantsMap_isExpansionOn_of_eq
    (f : M → N)
    (h : ∀ a : M, f a = ((L.con a : L[[M]].Constants) : N)) :
    (L.lhomWithConstantsMap f).IsExpansionOn N := by
  simp only [lhomWithConstantsMap]
  constructor
  · intro n g x
    cases g with
    | inl g => exact ((L.lhomWithConstants M).map_onFunction g x).symm
    | inr g =>
      cases n with
      | zero =>
        rw [Unique.eq_default x]
        exact h g
      | succ n => exact isEmptyElim g
  · intro n R x
    cases R with
    | inl R => exact ((L.lhomWithConstants M).map_onRelation R x).symm
    | inr R => exact isEmptyElim R

end LHom

end Language

end FirstOrder
