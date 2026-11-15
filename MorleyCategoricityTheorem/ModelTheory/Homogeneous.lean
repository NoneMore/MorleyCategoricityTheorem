/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import MorleyCategoricityTheorem.ModelTheory.PartialEmbedding

/-!
# Homogeneous models

A structure `M` is `κ`-homogeneous when every partial elementary map between subsets of `M` whose
domain has cardinality below `κ` extends over any one additional element.  A structure is
homogeneous when it is `#M`-homogeneous.

This is blueprint `def:homogeneous-model`.  The definition is stated for an arbitrary cardinal `κ`;
the interesting range is `ℵ₀ ≤ κ ≤ #M`.  Infinitude is not built into the predicate, matching the
project's convention of leaving the range hypothesis to consumers (compare
`Theory.IsKappaLambdaModel`).

## Main definitions

- `FirstOrder.Language.IsHomogeneous`: `κ`-homogeneity of a structure.
- `FirstOrder.Language.IsHomogeneousModel`: homogeneity, i.e. `#M`-homogeneity.

## Main results

- `IsHomogeneous.extend`: the defining one-element extension property.
- `IsHomogeneous.mono`: `κ'`-homogeneity implies `κ`-homogeneity for `κ ≤ κ'`.
- `IsHomogeneousModel.isHomogeneous`: homogeneity implies `κ`-homogeneity for every `κ ≤ #M`.
- `IsHomogeneousModel.isHomogeneous_aleph0`: an infinite homogeneous structure is
  `ℵ₀`-homogeneous.
- `IsHomogeneous.of_equiv` and `IsHomogeneousModel.of_equiv`: homogeneity is invariant under
  first-order equivalence.
-/

universe u v w

namespace FirstOrder

namespace Language

open scoped Cardinal

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {N : Type w} [L.Structure N]
variable {κ κ' : Cardinal.{w}}

/-- A structure `M` is `κ`-homogeneous when every partial elementary map between subsets of `M`
whose domain has cardinality below `κ` extends over any one additional element.

The extension over `x` may use any image `y` of `x`; the target of the extended map is
`insert y B`, where `B` is the target of the original map.  The definition is meaningful for every
cardinal `κ`; the interesting range is `ℵ₀ ≤ κ ≤ #M`. -/
def IsHomogeneous (L : Language.{u, v}) (M : Type w) [L.Structure M] (κ : Cardinal.{w}) : Prop :=
  ∀ ⦃A B : Set M⦄ (f : A ↪ₚₑ[L] B), #A < κ →
    ∀ x : M, ∃ y : M, ∃ g : (insert x A : Set M) ↪ₚₑ[L] (insert y B : Set M),
      g.Extends f (Set.subset_insert x A) (Set.subset_insert y B)

/-- A structure is homogeneous when it is `#M`-homogeneous. -/
def IsHomogeneousModel (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  L.IsHomogeneous M #M

/-- The defining form of homogeneity. -/
theorem isHomogeneousModel_iff : L.IsHomogeneousModel M ↔ L.IsHomogeneous M #M :=
  Iff.rfl

namespace IsHomogeneous

/-- The defining one-element extension property of `κ`-homogeneity. -/
theorem extend (h : L.IsHomogeneous M κ) {A B : Set M} (f : A ↪ₚₑ[L] B)
    (hA : #A < κ) (x : M) :
    ∃ y : M, ∃ g : (insert x A : Set M) ↪ₚₑ[L] (insert y B : Set M),
      g.Extends f (Set.subset_insert x A) (Set.subset_insert y B) :=
  h f hA x

/-- Monotonicity in the cardinal: `κ'`-homogeneity implies `κ`-homogeneity for `κ ≤ κ'`. -/
theorem mono (h : L.IsHomogeneous M κ') (hκ : κ ≤ κ') : L.IsHomogeneous M κ :=
  fun _ _ f hA => h f (lt_of_lt_of_le hA hκ)

/-- `κ`-homogeneity is invariant under first-order equivalence. -/
theorem of_equiv (e : M ≃[L] N) (h : L.IsHomogeneous M κ) :
    L.IsHomogeneous N κ := by
  intro A B f hA x
  have hcard : #(e ⁻¹' A) = #A := Cardinal.mk_subtype_of_equiv A e.toEquiv
  obtain ⟨y', g', hg'⟩ :=
    h (PartialElementaryEmbedding.comapEquiv e f) (hcard ▸ hA) (e.symm x)
  have hsetA : e.symm ⁻¹' (insert (e.symm x) (e ⁻¹' A)) = insert x A := by
    show e.toEquiv.symm ⁻¹' insert (e.toEquiv.symm x) (e.toEquiv ⁻¹' A) = insert x A
    rw [← _root_.Equiv.image_eq_preimage_symm (e := e.toEquiv), Set.image_insert_eq,
      _root_.Equiv.image_preimage, _root_.Equiv.apply_symm_apply]
  have hsetB : e.symm ⁻¹' (insert y' (e ⁻¹' B)) = insert (e y') B := by
    show e.toEquiv.symm ⁻¹' insert y' (e.toEquiv ⁻¹' B) = insert (e.toEquiv y') B
    rw [← _root_.Equiv.image_eq_preimage_symm (e := e.toEquiv), Set.image_insert_eq,
      _root_.Equiv.image_preimage]
  refine ⟨e y', (PartialElementaryEmbedding.comapEquiv e.symm g').reindex hsetA hsetB, ?_⟩
  intro a
  apply Subtype.ext
  rw [PartialElementaryEmbedding.reindex_apply]
  calc ((PartialElementaryEmbedding.comapEquiv e.symm g')
        ⟨a.1, hsetA.symm ▸ Set.subset_insert x A a.2⟩ : N)
      = e (g' ⟨e.symm a.1, by simp⟩ : M) := by
        rw [PartialElementaryEmbedding.comapEquiv_apply]
        rfl
    _ = e (PartialElementaryEmbedding.comapEquiv e f ⟨e.symm a.1, by simp⟩ : M) := by
        rw [PartialElementaryEmbedding.Extends.val_apply hg' ⟨e.symm a.1, by simp⟩]
    _ = (f a : N) := by
        rw [PartialElementaryEmbedding.comapEquiv_apply]
        simp

/-- `κ`-homogeneity is invariant under first-order equivalence. -/
theorem iff_of_equiv (e : M ≃[L] N) :
    L.IsHomogeneous M κ ↔ L.IsHomogeneous N κ :=
  ⟨of_equiv e, of_equiv e.symm⟩

end IsHomogeneous

namespace IsHomogeneousModel

/-- The defining one-element extension property of homogeneity. -/
theorem extend (h : L.IsHomogeneousModel M) {A B : Set M} (f : A ↪ₚₑ[L] B)
    (hA : #A < #M) (x : M) :
    ∃ y : M, ∃ g : (insert x A : Set M) ↪ₚₑ[L] (insert y B : Set M),
      g.Extends f (Set.subset_insert x A) (Set.subset_insert y B) :=
  h f hA x

/-- A homogeneous structure is `κ`-homogeneous for every cardinal `κ ≤ #M`. -/
theorem isHomogeneous (h : L.IsHomogeneousModel M) (hκ : κ ≤ #M) :
    L.IsHomogeneous M κ :=
  h.mono hκ

/-- An infinite homogeneous structure is `ℵ₀`-homogeneous. -/
theorem isHomogeneous_aleph0 [Infinite M] (h : L.IsHomogeneousModel M) :
    L.IsHomogeneous M ℵ₀ :=
  h.isHomogeneous (Cardinal.aleph0_le_mk M)

/-- Homogeneity is invariant under first-order equivalence. -/
theorem of_equiv (e : M ≃[L] N) (h : L.IsHomogeneousModel M) :
    L.IsHomogeneousModel N := by
  have hmk : #M = #N := Cardinal.mk_congr e.toEquiv
  rw [isHomogeneousModel_iff] at h ⊢
  simpa [hmk] using IsHomogeneous.of_equiv e h

end IsHomogeneousModel

end Language

end FirstOrder
