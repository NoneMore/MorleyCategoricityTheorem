/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import MorleyCategoricityTheorem.ModelTheory.PartialTypes

/-!
# Finitely many distinct realizations of a partial type

This file shows that a unary partial type over a parameter set `B ⊆ M`, every finite fragment of
which has infinitely many realizations in `M`, has `n + 1` pairwise distinct realizations in some
model of the elementary diagram of `M`, for every `n`.

The proof adjoins to the partial type, for each coordinate, the formulas relabelled to that
coordinate, together with the inequalities between distinct coordinates, and applies the
compactness interface of `ModelTheory.PartialTypes`. A finite fragment mentions only finitely many
formulas of the partial type, so each coordinate's finite conjunction still has infinitely many
candidates in `M`, among which pairwise distinct witnesses can be chosen.

## Main results

- `Theory.PartialType.exists_distinct_realizations`: the finite-witness theorem, with parameter
  transport stated explicitly along the canonical elementary embedding of `M` into a model of its
  elementary diagram.

The result follows the design of the reference project
[`NoneMore/StabilityTheory`](https://github.com/NoneMore/StabilityTheory); it is reproved here
against this repository's APIs and its Mathlib revision.
-/

universe u v w w'

namespace FirstOrder

namespace Language

namespace Theory

namespace PartialType

variable {L : Language.{u, v}}

/-- The formula `φ`, whose free variable is relabelled to the coordinate `i`. -/
private def relabelToCoord {n : ℕ} (i : Fin (n + 1)) (φ : L.Formula (Fin 1)) :
    L.Formula (Fin (n + 1)) :=
  φ.relabel fun _ => i

/-- Realizing the relabelled formula at `i` is realizing `φ` at the `i`-th component. -/
private theorem relabelToCoord_realize {M : Type w'} [L.Structure M] {n : ℕ}
    (i : Fin (n + 1)) (φ : L.Formula (Fin 1)) (v : Fin (n + 1) → M) :
    (relabelToCoord i φ).Realize v ↔ φ.Realize (fun _ : Fin 1 => v i) := by
  rw [relabelToCoord, Formula.realize_relabel]
  exact Iff.rfl

/-- The formula `x_i ≠ x_j` in the variables `Fin (n + 1)`. -/
private def neqFormula {n : ℕ} (i j : Fin (n + 1)) : L.Formula (Fin (n + 1)) :=
  (Term.equal (Term.var i) (Term.var j)).not

/-- The joint formula set in the variables `Fin (n + 1)`: the coordinate relabellings of the
formulas of `p` together with the inequalities between distinct coordinates. -/
private def jointSet {M : Type w'} [L.Structure M] (B : Set M)
    (p : Set (L[[B]].Formula (Fin 1))) (n : ℕ) : Set (L[[B]].Formula (Fin (n + 1))) :=
  (⋃ i : Fin (n + 1), relabelToCoord i '' p) ∪
    {ψ | ∃ i j : Fin (n + 1), i ≠ j ∧ ψ = neqFormula i j}

variable {M : Type w'} [L.Structure M] [Nonempty M]

/-- A finite family of infinite subsets of `M` admits an injective choice. -/
private theorem exists_injective_of_forall_infinite {ι : Type*} [Fintype ι] {W : ι → Set M}
    (hW : ∀ i, (W i).Infinite) :
    ∃ x : ι → M, Function.Injective x ∧ ∀ i, x i ∈ W i := by
  classical
  have key : ∀ t : Finset ι, ∃ x : ι → M, Set.InjOn x ↑t ∧ ∀ i ∈ t, x i ∈ W i := by
    intro t
    induction t using Finset.induction with
    | empty => exact ⟨fun _ => Classical.arbitrary M, by simp, by simp⟩
    | insert a s ha ih =>
      obtain ⟨x, hx, hxW⟩ := ih
      obtain ⟨y, hyW, hy⟩ := (hW a).exists_notMem_finite (s.finite_toSet.image x)
      refine ⟨Function.update x a y, ?_, ?_⟩
      · intro i hi j hj hij
        simp only [Finset.coe_insert, Set.mem_insert_iff] at hi hj
        rcases hi with hia | hi <;> rcases hj with hja | hj
        · rw [hia, hja]
        · rw [hia] at hij ⊢
          have hja' : j ≠ a := fun h => ha (by simpa [h] using hj)
          rw [Function.update_self, Function.update_of_ne hja'] at hij
          exact (hy ⟨j, hj, hij.symm⟩).elim
        · rw [hja] at hij ⊢
          have hia' : i ≠ a := fun h => ha (by simpa [h] using hi)
          rw [Function.update_self, Function.update_of_ne hia'] at hij
          exact (hy ⟨i, hi, hij⟩).elim
        · have hia' : i ≠ a := fun h => ha (by simpa [h] using hi)
          have hja' : j ≠ a := fun h => ha (by simpa [h] using hj)
          rw [Function.update_of_ne hia', Function.update_of_ne hja'] at hij
          exact hx hi hj hij
      · intro i hi
        rw [Finset.mem_insert] at hi
        rcases hi with hia | hi
        · rw [hia]
          simpa only [Function.update_self] using hyW
        · have hia' : i ≠ a := fun h => ha (h ▸ hi)
          simpa only [Function.update_of_ne hia'] using hxW i hi
  obtain ⟨x, hx⟩ := key Finset.univ
  exact ⟨x, fun i j h => hx.1 (Finset.mem_univ i) (Finset.mem_univ j) h,
    fun i => hx.2 i (Finset.mem_univ i)⟩

/-- If every finite fragment of a unary partial type `p` over `B ⊆ M` has infinitely many
realizations in `M`, then `p` has `n + 1` pairwise distinct realizations in a model of the
elementary diagram of `M`.

The parameters of `B` are interpreted along the canonical elementary embedding of `M` into that
model, as recorded by the last two components of the conclusion. -/
theorem exists_distinct_realizations {B : Set M} {p : Set (L[[B]].Formula (Fin 1))}
    (hp : ∀ s : Finset (L[[B]].Formula (Fin 1)),
      (↑s : Set (L[[B]].Formula (Fin 1))) ⊆ p →
        {x : M | ∀ φ ∈ s, φ.Realize (fun _ : Fin 1 => x)}.Infinite)
    (n : ℕ) :
    ∃ N : ModelType.{max u w', v, max (max u w') v} (L.elementaryDiagram M), ∃ e : M ↪ₑ[L] N,
      ∃ x : Fin (n + 1) → N,
        Function.Injective x ∧
          (∀ a : B, e (a : M) = (L.con (a : M) : N)) ∧
            ∀ (i : Fin (n + 1)) (φ : L[[B]].Formula (Fin 1)), φ ∈ p →
              ((L.lhomWithConstantsMap ((↑) : B → M)).onFormula φ).Realize
                (fun _ : Fin 1 => x i) := by
  classical
  let P : Set (L[[B]].Formula (Fin (n + 1))) := jointSet B p n
  have hfin : ∀ s : Finset (L[[B]].Formula (Fin (n + 1))),
      (↑s : Set (L[[B]].Formula (Fin (n + 1)))) ⊆ P →
        ∃ v : Fin (n + 1) → M, ∀ ψ ∈ s, ψ.Realize v := by
    intro s hs
    -- For each coordinate, the finite set of formulas of `p` whose relabelling occurs in `s`.
    -- `src i ψ` is such a formula for the fragment element `ψ`; the fallback is filtered out below.
    let src : Fin (n + 1) → {ψ // ψ ∈ s} → L[[B]].Formula (Fin 1) := fun i ψ =>
      if h : ∃ φ ∈ p, relabelToCoord i φ = ψ.1 then Classical.choose h else ⊥
    let T : Fin (n + 1) → Finset (L[[B]].Formula (Fin 1)) := fun i =>
      (s.attach.filter fun ψ => ∃ φ ∈ p, relabelToCoord i φ = ψ.1).image (src i)
    have hT : ∀ i, (↑(T i) : Set (L[[B]].Formula (Fin 1))) ⊆ p := by
      intro i φ hφ
      obtain ⟨ψ, hψ, hψφ⟩ := Finset.mem_image.mp hφ
      rw [← hψφ]
      obtain ⟨-, hcond⟩ := Finset.mem_filter.mp hψ
      simp only [src, dite_eq_left hcond]
      exact (Classical.choose_spec hcond).1
    let W : Fin (n + 1) → Set M := fun i =>
      {x : M | ∀ φ ∈ T i, φ.Realize (fun _ : Fin 1 => x)}
    have hW : ∀ i, (W i).Infinite := fun i => hp (T i) (hT i)
    obtain ⟨x, hxinj, hxW⟩ := exists_injective_of_forall_infinite hW
    refine ⟨x, fun ψ hψ => ?_⟩
    have hψP : (ψ : L[[B]].Formula (Fin (n + 1))) ∈ jointSet B p n := hs hψ
    simp only [jointSet, Set.mem_union] at hψP
    rcases hψP with hA | hB
    · obtain ⟨i, hmem⟩ := Set.mem_iUnion.mp hA
      simp only [Set.mem_image] at hmem
      obtain ⟨φ, hφp, hφeq⟩ := hmem
      have hcond : ∃ φ' ∈ p, relabelToCoord i φ' = (ψ : L[[B]].Formula (Fin (n + 1))) :=
        ⟨φ, hφp, hφeq⟩
      have hmemT : src i ⟨ψ, hψ⟩ ∈ T i := by
        refine Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, ?_, rfl⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hcond⟩
      have hxWi : ∀ φ' ∈ T i, φ'.Realize (fun _ : Fin 1 => x i) := hxW i
      have hsrc : (src i ⟨ψ, hψ⟩).Realize (fun _ : Fin 1 => x i) := hxWi _ hmemT
      simp only [src, dite_eq_left hcond] at hsrc
      have hrel : (relabelToCoord i (Classical.choose hcond)).Realize x :=
        (relabelToCoord_realize i _ x).mpr hsrc
      rw [← (Classical.choose_spec hcond).2]
      exact hrel
    · obtain ⟨i, j, hij, rfl⟩ := hB
      simp only [neqFormula, Formula.realize_not, Formula.realize_equal, Term.realize_var]
      exact fun h => hij (hxinj h)
  have hsat : ((L[[B]].completeTheory M).withSet P).IsSatisfiable :=
    (partialTypeOver_iff_finitelyRealizable (L := L) (M := M) (A := B) (α := Fin (n + 1))
      P).2 hfin
  obtain ⟨N, e, he, v, hv⟩ :=
    (partialTypeOver_iff_realizedIn_elementaryExtension_with_embedding (L := L) (M := M) (A := B)
      (α := Fin (n + 1)) P).1 hsat
  -- Work in the `L[[B]]`-reduct of `N` to compare with formulas over `B`.
  let f := L.lhomWithConstantsMap ((↑) : B → M)
  let : L[[B]].Structure N := f.reduct N
  have : f.IsExpansionOn N := LHom.isExpansionOn_reduct f N
  refine ⟨N, e, v, ?_, ?_, ?_⟩
  · intro i j hij
    by_contra hne
    have hmem : neqFormula i j ∈ jointSet B p n := by
      simp only [jointSet, Set.mem_union]
      exact Or.inr ⟨i, j, hne, rfl⟩
    have hreal : (neqFormula i j).Realize v := (LHom.realize_onFormula f _).mp (hv _ hmem)
    simp only [neqFormula, Formula.realize_not, Formula.realize_equal, Term.realize_var] at hreal
    exact hreal hij
  · intro a
    exact he (a : M)
  · intro i φ hφ
    have hmem : relabelToCoord i φ ∈ jointSet B p n := by
      simp only [jointSet, Set.mem_union]
      exact Or.inl (Set.mem_iUnion.mpr ⟨i, Set.mem_image_of_mem _ hφ⟩)
    have hreal : (relabelToCoord i φ).Realize v := (LHom.realize_onFormula f _).mp (hv _ hmem)
    exact (LHom.realize_onFormula f φ).mpr ((relabelToCoord_realize i φ v).mp hreal)

end PartialType

end Theory

end Language

end FirstOrder
