/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import MorleyCategoricityTheorem.ModelTheory.AlgebraicClosure

/-!
# Relative algebraic closure

For a base `A` and a set `D` in an `L`-structure `M`, the relative algebraic closure of `X` is
`cl_A(X) = D ∩ acl(A ∪ X)`: the elements of `D` that are algebraic over `A ∪ X`.  This is the
closure operator used for a strongly minimal set (blueprint `def:strongly-minimal-pregeometry`);
the laws proved here are blueprint `lem:strongly-minimal-closure-laws`.

The closure laws do not use strong minimality or the definability of `D` over `A`, so both the
definition and the laws are stated for an arbitrary set `D`.  Exchange, which does need strong
minimality, belongs to a later module.

## Main definitions

- `FirstOrder.Language.relAlgebraicClosure`: the operator `cl_A(X) = D ∩ acl (A ∪ X)`.

## Main results

- `relAlgebraicClosure_subset`: `cl_A(X) ⊆ D`.
- `subset_relAlgebraicClosure`: `X ⊆ D → X ⊆ cl_A(X)` (reflexivity).
- `relAlgebraicClosure_mono`: `X ⊆ Y → cl_A(X) ⊆ cl_A(Y)` (monotonicity).
- `relAlgebraicClosure_idem`: `cl_A(cl_A(X)) = cl_A(X)` (idempotence).
- `mem_relAlgebraicClosure_iff_exists_finset`: membership in `cl_A(X)` depends on finitely many
  parameters from `X` (finite character).
-/

universe u v w

namespace FirstOrder

namespace Language

/-- The relative algebraic closure `cl_A(X) = D ∩ acl (A ∪ X)`: the elements of `D` that are
algebraic over `A ∪ X`. -/
def relAlgebraicClosure (L : Language.{u, v}) {M : Type w} [L.Structure M]
    (A D X : Set M) : Set M :=
  D ∩ L.algebraicClosure (A ∪ X)

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {A D X Y : Set M} {b : M}

/-- Membership in the relative algebraic closure: `b ∈ cl_A(X)` exactly when `b ∈ D` is algebraic
over `A ∪ X`. -/
@[simp]
theorem mem_relAlgebraicClosure_iff :
    b ∈ L.relAlgebraicClosure A D X ↔ b ∈ D ∧ L.IsAlgebraicOver (A ∪ X) b :=
  Iff.rfl

/-- The relative algebraic closure consists of elements of `D`. -/
theorem relAlgebraicClosure_subset : L.relAlgebraicClosure A D X ⊆ D :=
  Set.inter_subset_left

/-- Reflexivity: every subset of `D` is contained in its relative algebraic closure. -/
theorem subset_relAlgebraicClosure (hXD : X ⊆ D) : X ⊆ L.relAlgebraicClosure A D X := by
  intro x hx
  exact ⟨hXD hx, subset_algebraicClosure (Set.mem_union_right A hx)⟩

/-- Monotonicity of the relative algebraic closure in its argument. -/
theorem relAlgebraicClosure_mono (hXY : X ⊆ Y) :
    L.relAlgebraicClosure A D X ⊆ L.relAlgebraicClosure A D Y := by
  rintro b ⟨hbD, hb⟩
  exact ⟨hbD, algebraicClosure_mono (Set.union_subset_union_right A hXY) hb⟩

/-- Idempotence: closing a set twice does not add elements.

For `cl_A (cl_A X) ⊆ cl_A X`, the parameter set `A ∪ (D ∩ acl (A ∪ X))` is contained in
`acl (A ∪ X)`, and algebraic closure is idempotent.  The reverse inclusion holds because every
element of `D ∩ acl (A ∪ X)` is one of the adjoined parameters. -/
theorem relAlgebraicClosure_idem :
    L.relAlgebraicClosure A D (L.relAlgebraicClosure A D X) = L.relAlgebraicClosure A D X := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro b ⟨hbD, hb⟩
    refine ⟨hbD, ?_⟩
    have hsub : A ∪ (D ∩ L.algebraicClosure (A ∪ X)) ⊆ L.algebraicClosure (A ∪ X) :=
      Set.union_subset (fun a ha => subset_algebraicClosure (Set.mem_union_left X ha))
        Set.inter_subset_right
    have hmem : b ∈ L.algebraicClosure (L.algebraicClosure (A ∪ X)) :=
      algebraicClosure_mono hsub hb
    simpa only [algebraicClosure_idem] using hmem
  · rintro b ⟨hbD, hb⟩
    exact ⟨hbD, subset_algebraicClosure (Set.mem_union_right A ⟨hbD, hb⟩)⟩

/-- Finite character: `b ∈ cl_A(X)` depends on finitely many parameters from `X`.

The forward direction discards from a finite witness set the parameters that already lie in the
base `A`. -/
theorem mem_relAlgebraicClosure_iff_exists_finset :
    b ∈ L.relAlgebraicClosure A D X ↔
      ∃ F : Finset M, (F : Set M) ⊆ X ∧ b ∈ L.relAlgebraicClosure A D (F : Set M) := by
  classical
  constructor
  · rintro ⟨hbD, hb⟩
    obtain ⟨F, hF, hbF⟩ := mem_algebraicClosure_iff_exists_finset.mp hb
    refine ⟨F.filter fun x => x ∉ A, ?_, hbD, ?_⟩
    · -- the retained parameters lie in `X`, because the discarded ones lie in `A`
      intro x hx
      have hxF : x ∈ F := Finset.mem_of_mem_filter x hx
      rcases hF (Finset.mem_coe.mp hxF) with hxA | hxX
      · exact absurd hxA (Finset.mem_filter.mp hx).2
      · exact hxX
    · -- every parameter of `F` is either in `A` or retained by the filter
      have hF' : (F : Set M) ⊆ A ∪ ↑(F.filter fun x => x ∉ A) := by
        intro x hx
        by_cases hxA : x ∈ A
        · exact Set.mem_union_left _ hxA
        · exact Set.mem_union_right _ (Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hx, hxA⟩))
      exact algebraicClosure_mono hF' hbF
  · rintro ⟨F, hF, hb⟩
    exact ⟨hb.1, algebraicClosure_mono (Set.union_subset_union_right A hF) hb.2⟩

end Language

end FirstOrder
