import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Complexity

/-!
# Partial Embeddings

This file will contain partial embeddings between first-order structures.
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

end PartialElementaryEmbedding

end Language

end FirstOrder
