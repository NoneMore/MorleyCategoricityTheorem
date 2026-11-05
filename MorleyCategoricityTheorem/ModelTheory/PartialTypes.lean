/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.ModelTheory.Satisfiability
import MorleyCategoricityTheorem.ModelTheory.LanguageMap
import MorleyCategoricityTheorem.ModelTheory.Satisfiability

/-!
# Partial types and compactness

This file develops the minimal partial-type layer needed to realize types in elementary
extensions. A partial type over a theory `T` is a set of formulas whose finite fragments are
simultaneously realized; `Theory.withSet` turns such a set into a theory in the language expanded
by constants for the variables, so that compactness applies.

The central results are:

- `Theory.PartialType.partialTypeOver_iff_finitelyRealizable`: a set of `L[[A]]`-formulas is
  consistent with the complete theory of `M` exactly when every finite fragment is realized in
  `M` itself.
- `Theory.PartialType.partialTypeOver_iff_realizedIn_elementaryExtension`: the same consistency is
  equivalent to simultaneous realization in a model of the elementary diagram of `M`, after
  transporting parameters along `A → M`.

The results follow the design of the reference project
[`NoneMore/StabilityTheory`](https://github.com/NoneMore/StabilityTheory); they are reproved here
against this repository's APIs and its Mathlib revision.

## Main definitions

- `FirstOrder.Language.Theory.withSet`: a theory with a set of formulas adjoined as sentences over
  constants for the variables.
- `FirstOrder.Language.Theory.PartialType`: a set of formulas consistent with a theory.
- `FirstOrder.Language.Theory.PartialTypeOver`: a partial type over the complete theory of a
  structure in a parameter-expanded language.
- `FirstOrder.Language.Theory.PartialType.ofFinitelyRealizable`: package a set of formulas whose
  finite fragments are realized in a fixed structure as a bundled partial type; its specialization
  `FirstOrder.Language.Theory.PartialTypeOver.ofFinitelyRealizable` does the same for a parameter
  set.

## Main results

- `Theory.PartialType.partialType_completeTheory_iff_finitelyRealizable`: finite realization in a
  fixed model detects consistency with its complete theory.
- `Theory.PartialType.partialType_completeTheory_mapExpansion`: consistency transports along a
  language expansion.
- `Theory.PartialType.partialTypeOver_iff_finitelyRealizable`: the parameter-expanded form over a
  set `A ⊆ M`.
- `Theory.PartialType.partialTypeOver_iff_realizedIn_elementaryExtension`: realization in a model
  of the elementary diagram.
- `Theory.PartialType.partialTypeOver_iff_realizedIn_elementaryExtension_with_embedding`: the same
  statement together with an elementary embedding `M ↪ₑ[L] N` that interprets each parameter as the
  corresponding constant; its forward direction produces the canonical embedding
  `ElementaryEmbedding.ofModelsElementaryDiagram`.
- `ElementaryEmbedding.ofModelsElementaryDiagram_apply`: the canonical embedding interprets each
  parameter as the corresponding constant.
-/

universe u v w w' x

namespace FirstOrder

namespace Language

namespace ElementaryEmbedding

/-- The canonical elementary embedding of a structure into a model of its elementary diagram
interprets each parameter as the corresponding constant. -/
theorem ofModelsElementaryDiagram_apply {L : Language.{u, v}} {M : Type w'} [L.Structure M]
    {N : Type x} [L.Structure N] [L[[M]].Structure N] [(L.lhomWithConstants M).IsExpansionOn N]
    [N ⊨ L.elementaryDiagram M] (a : M) :
    ofModelsElementaryDiagram L M N a = (L.con a : N) :=
  rfl

end ElementaryEmbedding

namespace Theory

variable {L : Language.{u, v}}

/-- The theory obtained from `T` by adjoining a set of formulas in variables `α`, viewed as
sentences in the language with constants for `α`. -/
def withSet (T : L.Theory) {α : Type w} (S : Set (L.Formula α)) : L[[α]].Theory :=
  (L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' S

/-- A partial type over `T` in variables `α` is a set of formulas consistent with `T`. -/
structure PartialType (T : L.Theory) (α : Type w) where
  /-- The underlying set of formulas. -/
  toSet : Set (L.Formula α)
  /-- Consistency with `T`, packaged as satisfiability in the language with constants for `α`. -/
  isSatisfiable' : (T.withSet toSet).IsSatisfiable

/-- Partial types over a parameter set `A` in a structure `M`, implemented as partial types over
the complete `L[[A]]`-theory of `M`. -/
abbrev PartialTypeOver (L : Language.{u, v}) {M : Type w'} [L.Structure M] (A : Set M)
    (α : Type w) :=
  (L[[A]].completeTheory M).PartialType α

/-- A model of the elementary diagram of `M` carries the canonical `L`-structure obtained by
restricting along the constants map. -/
instance instStructureModelTypeElementaryDiagram {L : Language.{u, v}} {M : Type w'}
    [L.Structure M] (N : Theory.ModelType (L.elementaryDiagram M)) : L.Structure N :=
  (L.lhomWithConstants M).reduct N

namespace PartialType

variable {T : L.Theory} {α : Type w}

/-- A model of a consistent set of formulas realizes it simultaneously. -/
private theorem exists_modelType_realizing {S : Set (L.Formula α)}
    (hS : (T.withSet S).IsSatisfiable) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T,
      ∃ v : α → M, ∀ φ ∈ S, φ.Realize v := by
  let N : (T.withSet S).ModelType := hS.some
  let : L.Structure N := (L.lhomWithConstants α).reduct N
  have : (L.lhomWithConstants α).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
  have hN : N ⊨ T :=
    (LHom.onTheory_model (L.lhomWithConstants α) T).1 (N.is_model.mono Set.subset_union_left)
  refine ⟨Theory.ModelType.of T N, fun a => (L.con a : N), ?_⟩
  intro φ hφ
  have hmem : Formula.equivSentence φ ∈ T.withSet S := Or.inr ⟨φ, hφ, rfl⟩
  exact (Formula.realize_equivSentence N φ).1 (N.is_model.realize_of_mem _ hmem)

/-- A set of formulas simultaneously realized in a model of `T` is consistent with `T`. -/
private theorem isSatisfiable_withSet_of_realize {M : Type w'} [L.Structure M] [Nonempty M]
    [M ⊨ T] {S : Set (L.Formula α)} {v : α → M} (h : ∀ φ ∈ S, φ.Realize v) :
    (T.withSet S).IsSatisfiable := by
  let : (constantsOn α).Structure M := constantsOn.structure v
  have : (L.lhomWithConstants α).IsExpansionOn M := L.withConstants_expansion α
  have hM : M ⊨ T.withSet S := by
    refine ⟨fun φ hφ => ?_⟩
    rcases hφ with hφ | ⟨ψ, hψS, rfl⟩
    · exact ((LHom.onTheory_model _ _).2 inferInstance).realize_of_mem φ hφ
    · exact (Formula.realize_equivSentence_symm M (Formula.equivSentence ψ) v).1
        (by simpa using h ψ hψS)
  exact Theory.Model.isSatisfiable M

/-- Over the complete theory of a structure, a set of formulas is consistent exactly when every
finite fragment is realized in the structure itself. -/
theorem partialType_completeTheory_iff_finitelyRealizable {M : Type w'} [L.Structure M]
    [Nonempty M] (S : Set (L.Formula α)) :
    ((L.completeTheory M).withSet S).IsSatisfiable ↔
      ∀ s : Finset (L.Formula α), (↑s : Set (L.Formula α)) ⊆ S →
        ∃ v : α → M, ∀ φ ∈ s, φ.Realize v := by
  classical
  constructor
  · intro hS s hs
    obtain ⟨N, v, hv⟩ := exists_modelType_realizing (T := L.completeTheory M) hS
    let ψ : L.Formula α := Formula.iInf fun φ : s => (φ : L.Formula α)
    have hψ : ψ.Realize v := by
      simp only [ψ, Formula.realize_iInf]
      exact fun φ => hv φ (hs φ.2)
    obtain ⟨w, hw⟩ := (completeTheory.isComplete L M).exists_realize_of_isComplete v ψ hψ M
    exact ⟨w, fun φ hφ => Formula.realize_iInf.mp hw ⟨φ, hφ⟩⟩
  · intro h
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro T0 hT0
    let s : Finset (L.Formula α) :=
      (T0.map (Formula.equivSentence).symm.toEmbedding).filter fun φ => φ ∈ S
    have hs : (↑s : Set (L.Formula α)) ⊆ S := fun φ hφ => (Finset.mem_filter.mp hφ).2
    obtain ⟨v, hv⟩ := h s hs
    have hsub : (T0 : L[[α]].Theory) ⊆ (L.completeTheory M).withSet ↑s := by
      intro φ hφ
      rcases hT0 hφ with hφT | ⟨ψ, hψS, rfl⟩
      · exact Or.inl hφT
      · have hψ : ψ ∈ s := by simpa [s, hψS] using hφ
        exact Or.inr ⟨ψ, hψ, rfl⟩
    exact (isSatisfiable_withSet_of_realize (T := L.completeTheory M) hv).mono hsub

/-- Package a set of formulas whose finite fragments are realized in `M` as a partial type over the
complete theory of `M`. -/
def ofFinitelyRealizable {M : Type w'} [L.Structure M] [Nonempty M] (S : Set (L.Formula α))
    (h : ∀ s : Finset (L.Formula α), (↑s : Set (L.Formula α)) ⊆ S →
      ∃ v : α → M, ∀ φ ∈ s, φ.Realize v) :
    (L.completeTheory M).PartialType α :=
  ⟨S, (partialType_completeTheory_iff_finitelyRealizable S).2 h⟩

/-- Transport a consistent set of formulas along a language expansion. -/
theorem partialType_completeTheory_mapExpansion {L₁ L₂ : Language.{u, v}} {M : Type w'}
    [L₁.Structure M] [L₂.Structure M] [Nonempty M] {φ : L₁ →ᴸ L₂} [φ.IsExpansionOn M]
    {S : Set (L₁.Formula α)}
    (hS : ((L₁.completeTheory M).withSet S).IsSatisfiable) :
    ((L₂.completeTheory M).withSet (φ.onFormulaSet S)).IsSatisfiable := by
  classical
  rw [partialType_completeTheory_iff_finitelyRealizable] at hS ⊢
  intro s hs
  choose g hgS hgeq using fun ψ : s => LHom.mem_onFormulaSet.mp (hs ψ.2)
  have ht : (↑(s.attach.image g) : Set (L₁.Formula α)) ⊆ S := by
    rw [Finset.coe_image]
    rintro _ ⟨ψ, -, rfl⟩
    exact hgS ψ
  obtain ⟨v, hv⟩ := hS _ ht
  refine ⟨v, fun ψ hψ => ?_⟩
  have hψt : g ⟨ψ, hψ⟩ ∈ s.attach.image g :=
    Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
  have hψeq : φ.onFormula (g ⟨ψ, hψ⟩) = ψ := hgeq ⟨ψ, hψ⟩
  rw [← hψeq]
  exact (LHom.realize_onFormula φ (g ⟨ψ, hψ⟩)).mpr (hv _ hψt)

variable {M : Type w'} [L.Structure M] [Nonempty M]

variable {A : Set M}

/-- Over the complete theory of a structure, a set of formulas with parameters from `A` is
consistent exactly when every finite fragment is realized in the structure itself. -/
theorem partialTypeOver_iff_finitelyRealizable (S : Set (L[[A]].Formula α)) :
    ((L[[A]].completeTheory M).withSet S).IsSatisfiable ↔
      ∀ s : Finset (L[[A]].Formula α), (↑s : Set (L[[A]].Formula α)) ⊆ S →
        ∃ v : α → M, ∀ φ ∈ s, φ.Realize v := by
  exact partialType_completeTheory_iff_finitelyRealizable S

/-- A set of formulas with parameters from `A` is consistent with the complete theory of `M`
exactly when it is realized in a model of the elementary diagram of `M`, after transporting
parameters along `A → M`. -/
theorem partialTypeOver_iff_realizedIn_elementaryExtension (S : Set (L[[A]].Formula α)) :
    ((L[[A]].completeTheory M).withSet S).IsSatisfiable ↔
      ∃ N : Theory.ModelType.{max u w', v, max (max (max u w') v) w} (L.elementaryDiagram M),
        ∃ v : α → N,
          ∀ φ ∈ S,
            ((L.lhomWithConstantsMap ((↑) : A → M)).onFormula φ).Realize v := by
  classical
  let f : L[[A]] →ᴸ L[[M]] := L.lhomWithConstantsMap ((↑) : A → M)
  let S' : Set (L[[M]].Formula α) := f.onFormulaSet S
  have : (LHom.constantsOnMap ((↑) : A → M)).IsExpansionOn M :=
    constantsOnMap_isExpansionOn rfl
  have hf : f.IsExpansionOn M := LHom.sumMap_isExpansionOn (LHom.id L) _ M
  constructor
  · intro hS
    obtain ⟨N, v, hv⟩ := exists_modelType_realizing (T := L[[M]].completeTheory M)
      (partialType_completeTheory_mapExpansion (φ := f) (S := S) hS)
    exact ⟨N, v, fun φ hφ => hv _ ⟨φ, hφ, rfl⟩⟩
  · rintro ⟨N, v, hv⟩
    -- `S'` is consistent, so completeness realizes its finite fragments in `M` itself
    have hsat : ((L[[M]].completeTheory M).withSet S').IsSatisfiable :=
      isSatisfiable_withSet_of_realize (M := N) fun ψ hψ => by
        obtain ⟨φ, hφ, rfl⟩ := hψ
        exact hv φ hφ
    rw [partialTypeOver_iff_finitelyRealizable]
    intro s hs
    obtain ⟨w, hw⟩ := (partialType_completeTheory_iff_finitelyRealizable (M := M) S').1 hsat
      (s.image fun φ => f.onFormula φ)
      (by simpa [S', LHom.onFormulaSet] using LHom.onFormulaSet_mono f hs)
    exact ⟨w, fun φ hφ =>
      (LHom.realize_onFormula f (φ : L[[A]].Formula α)).mp
        (hw _ (Finset.mem_image.mpr ⟨φ, hφ, rfl⟩))⟩

/-- A set of formulas with parameters from `A` is consistent with the complete theory of `M`
exactly when it is realized in a model of the elementary diagram of `M` through an elementary
embedding that interprets each parameter as the corresponding constant. -/
theorem partialTypeOver_iff_realizedIn_elementaryExtension_with_embedding
    (S : Set (L[[A]].Formula α)) :
    ((L[[A]].completeTheory M).withSet S).IsSatisfiable ↔
      ∃ N : Theory.ModelType.{max u w', v, max (max (max u w') v) w} (L.elementaryDiagram M),
        ∃ e : M ↪ₑ[L] N,
          (∀ a : M, e a = (L.con a : N)) ∧
            ∃ v : α → N,
              ∀ φ ∈ S,
                ((L.lhomWithConstantsMap ((↑) : A → M)).onFormula φ).Realize v := by
  constructor
  · intro hS
    obtain ⟨N, v, hv⟩ := (partialTypeOver_iff_realizedIn_elementaryExtension S).1 hS
    have : (L.lhomWithConstants M).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
    exact ⟨N, ElementaryEmbedding.ofModelsElementaryDiagram L M N,
      ElementaryEmbedding.ofModelsElementaryDiagram_apply, v, hv⟩
  · rintro ⟨N, _, _, v, hv⟩
    exact (partialTypeOver_iff_realizedIn_elementaryExtension S).2 ⟨N, v, hv⟩

end PartialType

/-- Package a set of formulas over `A` whose finite fragments are realized in `M` as a partial type
over `A`. -/
def PartialTypeOver.ofFinitelyRealizable {L : Language.{u, v}} {M : Type w'} [L.Structure M]
    [Nonempty M] {A : Set M} {α : Type w} (S : Set (L[[A]].Formula α))
    (h : ∀ s : Finset (L[[A]].Formula α), (↑s : Set (L[[A]].Formula α)) ⊆ S →
      ∃ v : α → M, ∀ φ ∈ s, φ.Realize v) :
    PartialTypeOver L A α :=
  PartialType.ofFinitelyRealizable (L := L[[A]]) (M := M) (α := α) S h

end Theory

end Language

end FirstOrder
