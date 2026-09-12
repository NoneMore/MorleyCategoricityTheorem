import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Complexity
import MorleyCategoricityTheorem.ModelTheory.LanguageEmbedding
import MorleyCategoricityTheorem.ModelTheory.Semantics

/-!
# Partial Embeddings

This file defines partial embeddings and partial elementary embeddings between first-order
structures, and transports the complete theory of a parameter-expanded structure along a partial
elementary embedding.

## Main results

- `PartialElementaryEmbedding.map_boundedFormula` and `PartialElementaryEmbedding.map_formula`:
  preservation of bounded and ordinary formulas with an arbitrary type of free variables.
- `PartialEmbedding.parameterLEquiv`: a partial embedding `f` induces an equivalence between the
  constant expansions `L[[A]]` and `L[[B]]` that renames each constant `a` to the constant `f a`.
  `PartialElementaryEmbedding.parameterLEquiv` is the specialisation to partial elementary
  embeddings.
- `PartialElementaryEmbedding.map_sentence`: this equivalence preserves satisfaction of sentences.
- `PartialElementaryEmbedding.map_completeTheory`: it carries the complete theory of `M` over `A`
  onto the complete theory of `N` over `B`.
-/

universe u v w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- A partial embedding between first-order structures.

This is a map between arbitrary subsets, not necessarily substructures. It is required to be
surjective onto its declared codomain and to preserve all quantifier-free formulas. Injectivity is
derived from preservation of equality. -/
structure PartialEmbedding (A : Set M) (B : Set N) : Type (max u v w w') where
  /-- The underlying map from the source subset to the target subset. -/
  toFun : A → B
  /-- The underlying map is onto the declared target subset. -/
  surjective' : Function.Surjective toFun
  /-- Quantifier-free formulas hold of a tuple exactly when they hold of its image. -/
  map_qf_formula' : ∀ ⦃n⦄ (φ : L.Formula (Fin n)), φ.IsQF → (∀ (x : Fin n → A),
    φ.Realize (Subtype.val ∘ x) ↔ φ.Realize (Subtype.val ∘ toFun ∘ x))

scoped[FirstOrder] notation:25 A " ↪ₚ[" L "] " B =>
  FirstOrder.Language.PartialEmbedding L A B

/-- A partial elementary embedding between first-order structures.

This is a map between arbitrary subsets, not necessarily substructures. It is required to be
surjective onto its declared codomain and to preserve all first-order formulas. -/
structure PartialElementaryEmbedding (A : Set M) (B : Set N) : Type (max u v w w') where
  /-- The underlying map from the source subset to the target subset. -/
  toFun : A → B
  /-- The underlying map is onto the declared target subset. -/
  surjective' : Function.Surjective toFun
  /-- First-order formulas hold of a tuple exactly when they hold of its image. -/
  map_formula' : ∀ ⦃n⦄ (φ : L.Formula (Fin n)), ∀ (x : Fin n → A),
    φ.Realize (Subtype.val ∘ x) ↔ φ.Realize (Subtype.val ∘ toFun ∘ x)

scoped[FirstOrder] notation:25 A " ↪ₚₑ[" L "] " B =>
  FirstOrder.Language.PartialElementaryEmbedding L A B

namespace PartialEmbedding

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]
variable {A : Set M} {B : Set N}

instance : CoeFun (A ↪ₚ[L] B) fun _ => A → B :=
  ⟨PartialEmbedding.toFun⟩

/-- A partial embedding is injective, because it preserves the quantifier-free formula `x = y`. -/
theorem injective (f : A ↪ₚ[L] B) : Function.Injective f := by
  intro a b hab
  let φ : L.Formula (Fin 2) :=
    (Term.var (0 : Fin 2)).equal (Term.var (1 : Fin 2))
  have hφ : φ.IsQF := by
    unfold φ
    exact (BoundedFormula.IsAtomic.equal _ _).isQF
  let x : Fin 2 → A := fun i => if i = 0 then a else b
  have htarget : φ.Realize (Subtype.val ∘ f ∘ x) := by
    simp [φ, x, hab]
  have hsource : φ.Realize (Subtype.val ∘ x) :=
    (f.map_qf_formula' φ hφ x).mpr htarget
  have hval : (a : M) = b := by
    simpa [φ, x] using hsource
  exact Subtype.ext hval

/-- The equivalence between the source and target subsets induced by a partial embedding. -/
noncomputable def toEquiv (f : A ↪ₚ[L] B) : A ≃ B :=
  Equiv.ofBijective f ⟨f.injective, f.surjective'⟩

@[simp]
theorem toEquiv_apply (f : A ↪ₚ[L] B) (a : A) : f.toEquiv a = f a :=
  rfl

/-- The equivalence between the constant expansions `L[[A]]` and `L[[B]]` induced by a partial
embedding `f : A ↪ₚ[L] B`: it renames the constant `a` to the constant `f a` and leaves the symbols
of `L` unchanged.

Only the underlying equivalence `f.toEquiv` is used, so this applies to partial embeddings and
specialises to partial elementary embeddings. -/
noncomputable def parameterLEquiv (f : A ↪ₚ[L] B) : L[[A]] ≃ᴸ L[[B]] :=
  LEquiv.lhomWithConstantsCongr L f.toEquiv

@[simp]
theorem parameterLEquiv_toLHom (f : A ↪ₚ[L] B) :
    f.parameterLEquiv.toLHom = L.lhomWithConstantsMap (f.toEquiv : A → B) :=
  rfl

end PartialEmbedding

namespace PartialElementaryEmbedding

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]
variable {A : Set M} {B : Set N}

instance : CoeFun (A ↪ₚₑ[L] B) fun _ => A → B :=
  ⟨PartialElementaryEmbedding.toFun⟩

/-- A partial elementary embedding is, in particular, a partial embedding. -/
def toPartialEmbedding (f : A ↪ₚₑ[L] B) : A ↪ₚ[L] B where
  toFun := f
  surjective' := f.surjective'
  map_qf_formula' := fun {n} φ _ x => f.map_formula' (n := n) φ x

@[simp]
theorem toPartialEmbedding_apply (f : A ↪ₚₑ[L] B) (a : A) :
    f.toPartialEmbedding a = f a :=
  rfl

/-- A partial elementary embedding is injective, because it is a partial embedding. -/
theorem injective (f : A ↪ₚₑ[L] B) : Function.Injective f := by
  intro a b hab
  exact f.toPartialEmbedding.injective (by simpa only [toPartialEmbedding_apply] using hab)

/-- The equivalence between the source and target subsets induced by a partial elementary
embedding. -/
noncomputable def toEquiv (f : A ↪ₚₑ[L] B) : A ≃ B :=
  Equiv.ofBijective f ⟨f.injective, f.surjective'⟩

@[simp]
theorem toEquiv_apply (f : A ↪ₚₑ[L] B) (a : A) : f.toEquiv a = f a :=
  rfl

/-- A partial elementary embedding preserves the realization of bounded formulas, for an arbitrary
type `α` of free variables and an arbitrary number `n` of bound variables.

The source assignment is factored through the inclusion `A → M` and the target assignment through
the inclusion `B → N`, so that both sides are realized in the ambient structures. This is the
partial analogue of `FirstOrder.Language.ElementaryEmbedding.map_boundedFormula`. -/
@[simp]
theorem map_boundedFormula (f : A ↪ₚₑ[L] B) {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n)
    (v : α → A) (xs : Fin n → A) :
    φ.Realize (Subtype.val ∘ f ∘ v) (Subtype.val ∘ f ∘ xs) ↔
      φ.Realize (Subtype.val ∘ v) (Subtype.val ∘ xs) :=
  BoundedFormula.realize_iff_of_realize_fin (g := Subtype.val ∘ f) (s := (Subtype.val : A → M))
    (fun _ ψ x => (f.map_formula' ψ x).symm) φ v xs

/-- A partial elementary embedding preserves the realization of formulas, for an arbitrary type of
free variables.

This is the partial analogue of `FirstOrder.Language.ElementaryEmbedding.map_formula`. -/
@[simp]
theorem map_formula (f : A ↪ₚₑ[L] B) {α : Type*} (φ : L.Formula α) (x : α → A) :
    φ.Realize (Subtype.val ∘ f ∘ x) ↔ φ.Realize (Subtype.val ∘ x) := by
  rw [Formula.Realize, Formula.Realize,
    ← Unique.eq_default (Subtype.val ∘ f ∘ (default : Fin 0 → A)),
    ← Unique.eq_default (Subtype.val ∘ (default : Fin 0 → A))]
  exact f.map_boundedFormula (n := 0) φ x default

/-- The equivalence between the constant expansions `L[[A]]` and `L[[B]]` induced by a partial
elementary embedding `f : A ↪ₚₑ[L] B`: it renames the constant `a` to the constant `f a` and leaves
the symbols of `L` unchanged. -/
noncomputable def parameterLEquiv (f : A ↪ₚₑ[L] B) : L[[A]] ≃ᴸ L[[B]] :=
  f.toPartialEmbedding.parameterLEquiv

@[simp]
theorem parameterLEquiv_toLHom (f : A ↪ₚₑ[L] B) :
    f.parameterLEquiv.toLHom = L.lhomWithConstantsMap (f.toEquiv : A → B) :=
  rfl

/-- Renaming parameters along a partial elementary embedding preserves satisfaction of sentences in
the parameter-expanded language. -/
theorem map_sentence (f : A ↪ₚₑ[L] B) (φ : L[[A]].Sentence) :
    M ⊨ φ ↔ N ⊨ (f.parameterLEquiv.toLHom).onSentence φ := by
  obtain ⟨θ, rfl⟩ := Formula.equivSentence.surjective φ
  rw [parameterLEquiv_toLHom, LHom.realize_onSentence_equivSentence, Formula.realize_equivSentence]
  exact (f.map_formula θ id).symm

/-- The parameter-language equivalence induced by a partial elementary embedding carries the
complete theory of `M` over `A` onto the complete theory of `N` over `B`. -/
theorem map_completeTheory (f : A ↪ₚₑ[L] B) :
    f.parameterLEquiv.toLHom.onTheory (L[[A]].completeTheory M) =
      L[[B]].completeTheory N :=
  (LEquiv.onTheory_completeTheory_eq_iff f.parameterLEquiv).mpr (map_sentence f)

end PartialElementaryEmbedding

end Language

end FirstOrder
