import Mathlib.ModelTheory.LanguageMap
import Mathlib.ModelTheory.Syntax

/-!
# Language maps

This file contains auxiliary results about language maps and expansions by constants.

## TODO

The following language-map API can be moved directly from
`../StabilityTheory/StabilityTheory/ModelTheory/LanguageMap.lean`:

* `LHom.addConstants_comp_lhomWithConstants`;
* `LHom.onTheory_comp`;
* `LHom.id_onTheory`;
* `LHom.onTheory_lhomWithConstants`.

The following compatibility results still need to be implemented for
`withConstantsSumEquiv`:

* its forward map commutes with the canonical maps adjoining constants;
* its action on `Formula.equivSentence` agrees with `BoundedFormula.constantsVarsEquiv`;
* its forward map is an expansion on the canonical one-step and iterated constant structures;
* realization and modelhood are preserved for these canonical structures.
-/

universe u v u' v' w w' w''

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}}

/-- The identity map on a sum language is the sum of the identity maps on the two factors. -/
theorem id_sumMap_id (L : Language.{u, v}) (L' : Language.{u', v'}) :
    LHom.id (L.sum L') = (LHom.id L).sumMap (LHom.id L') := by
  apply LHom.funext
  · ext _ f
    cases f <;> simp
  · ext _ R
    cases R <;> simp

variable {L' L'' L₁ L₂ L₃ L₄ : Language}

/-- Composition of sum-language maps is computed componentwise. -/
theorem sumMap_comp_sumMap (φ₂ : L' →ᴸ L'') (ψ₂ : L₃ →ᴸ L₄) (φ₁ : L →ᴸ L')
    (ψ₁ : L₁ →ᴸ L₃) :
    (φ₂.sumMap ψ₂).comp (φ₁.sumMap ψ₁) = (φ₂.comp φ₁).sumMap (ψ₂.comp ψ₁) := by
  apply LHom.funext
  · ext _ f
    cases f <;> simp
  · ext _ R
    cases R <;> simp

variable {M : Type w} {N : Type w'}
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

namespace LEquiv

variable {L : Language.{u, v}}

/-- A language equivalence built from equivalences of the symbol types of each arity. -/
def ofEquiv {L' : Language.{u', v'}} (f : ∀ n, L.Functions n ≃ L'.Functions n)
    (r : ∀ n, L.Relations n ≃ L'.Relations n) : L ≃ᴸ L' where
  toLHom := ⟨fun {n} => f n, fun {n} => r n⟩
  invLHom := ⟨fun {n} => (f n).symm, fun {n} => (r n).symm⟩
  left_inv := by
    apply LHom.funext <;> ext _ s <;> simp
  right_inv := by
    apply LHom.funext <;> ext _ s <;> simp

/-- The equivalence on `n`-ary function symbols induced by a language equivalence. -/
def functionsEquiv {L' : Language.{u', v'}} (e : L ≃ᴸ L') (n : ℕ) :
    L.Functions n ≃ L'.Functions n where
  toFun := e.toLHom.onFunction (n := n)
  invFun := e.invLHom.onFunction (n := n)
  left_inv := by
    intro f
    simpa using congr_fun (congr_fun (congr_arg (fun φ : L →ᴸ L => φ.onFunction) e.left_inv) n) f
  right_inv := by
    intro g
    simpa using congr_fun (congr_fun (congr_arg (fun φ : L' →ᴸ L' => φ.onFunction) e.right_inv) n) g

/-- The equivalence on `n`-ary relation symbols induced by a language equivalence. -/
def relationsEquiv {L' : Language.{u', v'}} (e : L ≃ᴸ L') (n : ℕ) :
    L.Relations n ≃ L'.Relations n where
  toFun := e.toLHom.onRelation (n := n)
  invFun := e.invLHom.onRelation (n := n)
  left_inv := by
    intro r
    simpa using congr_fun (congr_fun (congr_arg (fun φ : L →ᴸ L => φ.onRelation) e.left_inv) n) r
  right_inv := by
    intro s
    simpa using congr_fun (congr_fun (congr_arg (fun φ : L' →ᴸ L' => φ.onRelation) e.right_inv) n) s

/-- The language equivalence between two sum-languages induced by equivalences on the two
factors. -/
@[simps!]
def sumCongr {L₁ L₂ L₁' L₂' : Language} (e₁ : L₁ ≃ᴸ L₁') (e₂ : L₂ ≃ᴸ L₂') :
    L₁.sum L₂ ≃ᴸ L₁'.sum L₂' :=
  ofEquiv
    (fun n => Equiv.sumCongr (functionsEquiv e₁ n) (functionsEquiv e₂ n))
    (fun n => Equiv.sumCongr (relationsEquiv e₁ n) (relationsEquiv e₂ n))

/-- Associativity of the sum of languages, witnessed at the level of symbol types by
`Equiv.sumAssoc`. -/
@[simps!]
def sumAssoc (L₁ L₂ L₃ : Language) : (L₁.sum L₂).sum L₃ ≃ᴸ L₁.sum (L₂.sum L₃) :=
  ofEquiv
    (fun n => Equiv.sumAssoc (L₁.Functions n) (L₂.Functions n) (L₃.Functions n))
    (fun n => Equiv.sumAssoc (L₁.Relations n) (L₂.Relations n) (L₃.Relations n))

/-- Constants indexed by a sum are the disjoint union of the two constant languages. -/
def constantsOnSumEquiv (α : Type w') (β : Type w'') :
    constantsOn (α ⊕ β) ≃ᴸ (constantsOn α).sum (constantsOn β) :=
  ofEquiv
    (fun n => by
      cases n with
      | zero =>
        simp only [constantsOn_Functions, constantsOnFunc]
        rfl
      | succ n =>
        simp only [constantsOn_Functions, constantsOnFunc]
        exact Equiv.equivOfIsEmpty PEmpty (PEmpty ⊕ PEmpty))
    (fun n => by
      simp only [constantsOn_Relations]
      exact Equiv.equivOfIsEmpty Empty (Empty ⊕ Empty))

/-- Adding constants for `α ⊕ β` in one step is equivalent to adding constants for `α` and then
for `β`. -/
@[simps!]
def withConstantsSumEquiv (α : Type w') (β : Type w'') :
    L[[α ⊕ β]] ≃ᴸ (L[[α]])[[β]] :=
  ((LEquiv.refl L).sumCongr (constantsOnSumEquiv α β)).trans
    (sumAssoc L (constantsOn α) (constantsOn β)).symm

/-- Transport a theory along a language equivalence. -/
def onTheory {L' : Language} (e : L ≃ᴸ L') (T : L.Theory) : L'.Theory :=
  e.toLHom.onTheory T

end LEquiv

end Language

end FirstOrder
