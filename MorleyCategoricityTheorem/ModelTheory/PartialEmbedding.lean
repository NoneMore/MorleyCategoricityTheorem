import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Complexity
import Mathlib.ModelTheory.ElementaryMaps
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
- `PartialElementaryEmbedding.Extends`: extension of partial elementary embeddings, and its basic
  closure properties.
- `PartialElementaryEmbedding.reindex`: transport of a partial elementary embedding along
  equalities of its source and target.
- `PartialElementaryEmbedding.comapEquiv`: pullback of a partial elementary embedding along a
  first-order equivalence.
- `ElementaryEmbedding.toPartialElementaryEmbeddingOn`: the restriction of an elementary embedding
  `M ↪ₑ[L] N` to a partial elementary embedding from a parameter set onto its image.
  `Equiv.toPartialElementaryEmbeddingOn` is the specialisation to a first-order equivalence.

## TODO

- Extend the extension relation `PartialElementaryEmbedding.Extends` with restrictions and unions
  of compatible chains of partial elementary embeddings when back-and-forth constructions create
  concrete callers.  Keep this API proof-driven rather than fixing a general framework in advance.
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

variable {A' A'' : Set M} {B' B'' : Set N}

/-- A partial elementary embedding `g` extends `f` when its source and target contain those of `f`
and it agrees with `f` on the source of `f`.

This is the one-step extension relation used to state homogeneity: extending over an additional
element adds that element to the source and a chosen image to the target. -/
def Extends (g : A' ↪ₚₑ[L] B') (f : A ↪ₚₑ[L] B) (hA : A ⊆ A') (hB : B ⊆ B') : Prop :=
  ∀ a : A, g ⟨a, hA a.2⟩ = ⟨f a, hB (f a).2⟩

/-- Every partial elementary embedding extends itself. -/
theorem Extends.refl (f : A ↪ₚₑ[L] B) :
    f.Extends f (Set.Subset.refl A) (Set.Subset.refl B) :=
  fun _ => rfl

/-- The underlying value of an extension is the underlying value of the original map. -/
@[simp]
theorem Extends.val_apply {f : A ↪ₚₑ[L] B} {g : A' ↪ₚₑ[L] B'}
    {hA : A ⊆ A'} {hB : B ⊆ B'} (hgf : g.Extends f hA hB) (a : A) :
    (g ⟨a, hA a.2⟩ : N) = f a := by
  simpa using congrArg Subtype.val (hgf a)

/-- Extension of partial elementary embeddings is transitive. -/
theorem Extends.trans {f : A ↪ₚₑ[L] B} {g : A' ↪ₚₑ[L] B'} {h : A'' ↪ₚₑ[L] B''}
    {hA : A ⊆ A'} {hB : B ⊆ B'} {hA' : A' ⊆ A''} {hB' : B' ⊆ B''}
    (hgf : g.Extends f hA hB) (hhg : h.Extends g hA' hB') :
    h.Extends f (hA.trans hA') (hB.trans hB') := by
  intro a
  apply Subtype.ext
  simpa using (Extends.val_apply hhg ⟨a, hA a.2⟩).trans (Extends.val_apply hgf a)

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

/-- Transport a partial elementary embedding along equalities of its source and target. -/
def reindex (f : A ↪ₚₑ[L] B) {A' : Set M} {B' : Set N} (hA : A = A') (hB : B = B') :
    A' ↪ₚₑ[L] B' :=
  let toFun : A' → B' := fun a =>
    ⟨f ⟨a.1, hA.symm ▸ a.2⟩, hB ▸ (f ⟨a.1, hA.symm ▸ a.2⟩).2⟩
  { toFun := toFun
    surjective' := by
      intro b
      obtain ⟨a, ha⟩ := f.surjective' ⟨b.1, hB.symm ▸ b.2⟩
      refine ⟨⟨a.1, hA ▸ a.2⟩, ?_⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val ha
    map_formula' := by
      intro n φ x
      let y : Fin n → A := fun i => ⟨(x i).1, hA.symm ▸ (x i).2⟩
      have hx : (Subtype.val ∘ x : Fin n → M) = Subtype.val ∘ y := rfl
      have hfx : (Subtype.val ∘ toFun ∘ x : Fin n → N) = Subtype.val ∘ f ∘ y := rfl
      rw [hx, hfx]
      exact f.map_formula' φ y }

/-- Pull back a partial elementary embedding between subsets of `N` along a first-order equivalence
`e : M ≃[L] N`, obtaining a partial elementary embedding between their preimages in `M`.

The underlying map is `e.symm ∘ f ∘ e`. -/
noncomputable def comapEquiv (e : M ≃[L] N) {A B : Set N} (f : A ↪ₚₑ[L] B) :
    (e ⁻¹' A) ↪ₚₑ[L] (e ⁻¹' B) :=
  let toFun : (e ⁻¹' A) → (e ⁻¹' B) := fun a =>
    ⟨e.symm (f ⟨e a.1, a.2⟩), by
      change e (e.symm (f ⟨e a.1, a.2⟩).1) ∈ B
      rw [FirstOrder.Language.Equiv.apply_symm_apply]
      exact (f ⟨e a.1, a.2⟩).2⟩
  { toFun := toFun
    surjective' := by
      intro b
      obtain ⟨a0, ha0⟩ := f.surjective' ⟨e b.1, b.2⟩
      let a1 : A := ⟨e (e.symm a0.1), by
        rw [FirstOrder.Language.Equiv.apply_symm_apply]
        exact a0.2⟩
      refine ⟨⟨e.symm a0.1, by simp [a0.2]⟩, ?_⟩
      apply Subtype.ext
      change e.symm (f a1).1 = b.1
      have harg : a1 = a0 := Subtype.ext (FirstOrder.Language.Equiv.apply_symm_apply e a0.1)
      rw [harg]
      have hf : (f a0).1 = e b.1 := congrArg Subtype.val ha0
      rw [hf, FirstOrder.Language.Equiv.symm_apply_apply]
    map_formula' := by
      intro n φ x
      let y : Fin n → A := fun i => ⟨e (x i).1, (x i).2⟩
      have hx : (e ∘ (Subtype.val ∘ x) : Fin n → N) = Subtype.val ∘ y := rfl
      have hfx : (e ∘ (Subtype.val ∘ toFun ∘ x) : Fin n → N) = Subtype.val ∘ f ∘ y := by
        funext i
        change e (e.symm (f ⟨e (x i).1, (x i).2⟩).1) = (f ⟨e (x i).1, (x i).2⟩).1
        exact FirstOrder.Language.Equiv.apply_symm_apply e _
      calc
        φ.Realize (Subtype.val ∘ x)
            ↔ φ.Realize (e ∘ (Subtype.val ∘ x)) :=
              (StrongHomClass.realize_formula (g := e) φ).symm
        _ ↔ φ.Realize (Subtype.val ∘ y) := by rw [hx]
        _ ↔ φ.Realize (Subtype.val ∘ f ∘ y) := f.map_formula' φ y
        _ ↔ φ.Realize (e ∘ (Subtype.val ∘ toFun ∘ x)) := by rw [hfx]
        _ ↔ φ.Realize (Subtype.val ∘ toFun ∘ x) :=
              StrongHomClass.realize_formula (g := e) φ }

end PartialElementaryEmbedding

namespace ElementaryEmbedding

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- The restriction of an elementary embedding `e : M ↪ₑ[L] N` to a partial elementary embedding
from a parameter set `A` onto its image `e '' A`.

The underlying map sends `a : A` to `e a`, and elementarity is inherited from `e`. -/
def toPartialElementaryEmbeddingOn (e : M ↪ₑ[L] N) (A : Set M) : A ↪ₚₑ[L] (e '' A) where
  toFun a := ⟨e a, Set.mem_image_of_mem e a.2⟩
  surjective' b := by
    obtain ⟨a, ha, hfa⟩ := b.2
    exact ⟨⟨a, ha⟩, Subtype.ext hfa⟩
  map_formula' := fun {n} φ x => by
    have h : Subtype.val ∘ (fun a : A => (⟨e a, Set.mem_image_of_mem e a.2⟩ : e '' A)) ∘ x =
        ⇑e ∘ (Subtype.val ∘ x) := rfl
    rw [h]
    exact (e.map_formula φ (Subtype.val ∘ x)).symm

end ElementaryEmbedding

namespace Equiv

variable {L : Language.{u, v}} {M : Type w} {N : Type w'}
variable [L.Structure M] [L.Structure N]

/-- The restriction of a first-order equivalence `f : M ≃[L] N` to a partial elementary embedding
from a parameter set `A` onto its image `f '' A`.

This is the specialisation of `ElementaryEmbedding.toPartialElementaryEmbeddingOn` to the
elementary embedding underlying `f`. -/
def toPartialElementaryEmbeddingOn (f : M ≃[L] N) (A : Set M) : A ↪ₚₑ[L] (f '' A) :=
  f.toElementaryEmbedding.toPartialElementaryEmbeddingOn A

end Equiv

end Language

end FirstOrder
