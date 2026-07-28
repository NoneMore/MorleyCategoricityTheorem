import Mathlib.ModelTheory.LanguageMap

/-!
# Language maps

This file contains auxiliary results about language maps and expansions by constants.
-/

universe u v w w'

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure N] [L[[M]].Structure N]
variable [(L.lhomWithConstants M).IsExpansionOn N]

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
