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
    let N : ((L.completeTheory M).withSet S).ModelType := hS.some
    let : L.Structure N := (L.lhomWithConstants α).reduct N
    have : (L.lhomWithConstants α).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
    have hN : N ⊨ L.completeTheory M :=
      (LHom.onTheory_model (L.lhomWithConstants α) (L.completeTheory M)).1
        (N.is_model.mono Set.subset_union_left)
    have hv : ∀ φ ∈ s, φ.Realize (fun a => (L.con a : N)) := by
      intro φ hφ
      have hmem : Formula.equivSentence φ ∈ (L.completeTheory M).withSet S :=
        Or.inr ⟨φ, hs hφ, rfl⟩
      have hreal : N ⊨ Formula.equivSentence φ := N.is_model.realize_of_mem _ hmem
      exact (Formula.realize_equivSentence N φ).1 hreal
    let ψ : L.Formula α := Formula.iInf fun φ : s => (φ : L.Formula α)
    have hψ : ψ.Realize (fun a => (L.con a : N)) := by
      simp only [ψ, Formula.realize_iInf, Subtype.forall]
      exact fun φ hφ => hv φ hφ
    obtain ⟨w, hw⟩ :=
      (completeTheory.isComplete L M).exists_realize_of_isComplete
        (M := N) (fun a => (L.con a : N)) ψ hψ M
    exact ⟨w, fun φ hφ => (Formula.realize_iInf.mp hw) ⟨φ, hφ⟩⟩
  · intro h
    rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro T0 hT0
    let s : Finset (L.Formula α) :=
      (T0.map (Formula.equivSentence).symm.toEmbedding).filter fun φ => φ ∈ S
    have hs : (↑s : Set (L.Formula α)) ⊆ S := fun φ hφ => (Finset.mem_filter.mp hφ).2
    obtain ⟨v, hv⟩ := h s hs
    let : (constantsOn α).Structure M := constantsOn.structure v
    have : (L.lhomWithConstants α).IsExpansionOn M := L.withConstants_expansion α
    have hM : M ⊨ (T0 : L[[α]].Theory) := by
      rw [Theory.model_iff]
      intro φ hφ
      rcases hT0 hφ with hφT | hφS
      · exact ((LHom.onTheory_model (L.lhomWithConstants α) (L.completeTheory M)).2
          (by infer_instance)).realize_of_mem _ hφT
      · obtain ⟨ψ, hψS, rfl⟩ := hφS
        have hψ : ψ ∈ s := by
          simpa [s, hψS] using hφ
        exact (Formula.realize_equivSentence_symm M (Formula.equivSentence ψ) v).1
          (by simpa using hv ψ hψ)
    exact Theory.Model.isSatisfiable M

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
  let g : s → L₁.Formula α := fun ψ => Classical.choose (LHom.mem_onFormulaSet.mp (hs ψ.2))
  have hg_mem : ∀ ψ : s, g ψ ∈ S := fun ψ =>
    (Classical.choose_spec (LHom.mem_onFormulaSet.mp (hs ψ.2))).1
  have hg_eq : ∀ ψ : s, φ.onFormula (g ψ) = (ψ : L₂.Formula α) := fun ψ =>
    (Classical.choose_spec (LHom.mem_onFormulaSet.mp (hs ψ.2))).2
  let t : Finset (L₁.Formula α) := s.attach.image g
  have ht : (↑t : Set (L₁.Formula α)) ⊆ S := by
    intro ψ hψ
    obtain ⟨ψ', _, rfl⟩ := Finset.mem_image.mp hψ
    exact hg_mem ψ'
  obtain ⟨v, hv⟩ := hS t ht
  refine ⟨v, fun ψ hψ => ?_⟩
  have hψt : g ⟨ψ, hψ⟩ ∈ t :=
    Finset.mem_image.mpr ⟨⟨ψ, hψ⟩, Finset.mem_attach _ _, rfl⟩
  have hψeq : φ.onFormula (g ⟨ψ, hψ⟩) = ψ := by simpa using hg_eq ⟨ψ, hψ⟩
  rw [← hψeq]
  exact (LHom.realize_onFormula φ (g ⟨ψ, hψ⟩)).mpr (hv _ hψt)

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
  have hreal : N ⊨ Formula.equivSentence φ := N.is_model.realize_of_mem _ hmem
  exact (Formula.realize_equivSentence N φ).1 hreal

variable {M : Type w'} [L.Structure M] [Nonempty M]

variable {A : Set M}

/-- Over the complete theory of a structure, a set of formulas with parameters from `A` is
consistent exactly when every finite fragment is realized in the structure itself. -/
theorem partialTypeOver_iff_finitelyRealizable (S : Set (L[[A]].Formula α)) :
    ((L[[A]].completeTheory M).withSet S).IsSatisfiable ↔
      ∀ s : Finset (L[[A]].Formula α), (↑s : Set (L[[A]].Formula α)) ⊆ S →
        ∃ v : α → M, ∀ φ ∈ s, φ.Realize v := by
  simpa using
    (partialType_completeTheory_iff_finitelyRealizable (L := L[[A]]) (M := M) (α := α) S)

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
  constructor
  · intro hS
    let f : L[[A]] →ᴸ L[[M]] := L.lhomWithConstantsMap ((↑) : A → M)
    let S' : Set (L[[M]].Formula α) := f.onFormulaSet S
    have : (LHom.constantsOnMap ((↑) : A → M)).IsExpansionOn M :=
      constantsOnMap_isExpansionOn rfl
    have : f.IsExpansionOn M := LHom.sumMap_isExpansionOn (LHom.id L) _ M
    have hS' : ((L[[M]].completeTheory M).withSet S').IsSatisfiable := by
      have h := partialType_completeTheory_mapExpansion (L₁ := L[[A]]) (L₂ := L[[M]])
        (φ := f) (S := S) hS
      simpa [S', f] using h
    obtain ⟨N, v, hv⟩ := exists_modelType_realizing (T := L[[M]].completeTheory M) hS'
    exact ⟨N, v, fun φ hφ => hv _ ⟨φ, hφ, rfl⟩⟩
  · rintro ⟨N, v, h⟩
    rw [partialTypeOver_iff_finitelyRealizable]
    have : (LHom.constantsOnMap ((↑) : A → M)).IsExpansionOn M :=
      constantsOnMap_isExpansionOn rfl
    have : (L.lhomWithConstantsMap ((↑) : A → M)).IsExpansionOn M :=
      LHom.sumMap_isExpansionOn (LHom.id L) _ M
    intro s hs
    let ψ : L[[M]].Formula α := Formula.iInf fun φ : s =>
      (L.lhomWithConstantsMap ((↑) : A → M)).onFormula (φ : L[[A]].Formula α)
    have hψ : ψ.Realize v := by
      simp only [ψ, Formula.realize_iInf, Subtype.forall]
      exact fun φ hφ => h φ (hs hφ)
    obtain ⟨w, hw⟩ :=
      (completeTheory.isComplete (L[[M]]) M).exists_realize_of_isComplete
        (M := N) v ψ hψ M
    refine ⟨w, fun φ hφ => ?_⟩
    have h1 : ((L.lhomWithConstantsMap ((↑) : A → M)).onFormula
        (φ : L[[A]].Formula α)).Realize w :=
      (Formula.realize_iInf.mp hw) ⟨φ, hφ⟩
    exact (LHom.realize_onFormula (L.lhomWithConstantsMap ((↑) : A → M))
      (φ : L[[A]].Formula α)).mp h1

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
    obtain ⟨N, v, hv⟩ :=
      (partialTypeOver_iff_realizedIn_elementaryExtension (L := L) (M := M) (A := A) (α := α)
        S).1 hS
    have : (L.lhomWithConstants M).IsExpansionOn N := LHom.isExpansionOn_reduct _ _
    exact ⟨N, ElementaryEmbedding.ofModelsElementaryDiagram L M N,
      fun a => ElementaryEmbedding.ofModelsElementaryDiagram_apply (L := L) (M := M) (N := N) a,
      v, hv⟩
  · rintro ⟨N, _, _, v, hv⟩
    exact
      (partialTypeOver_iff_realizedIn_elementaryExtension (L := L) (M := M) (A := A) (α := α)
        S).2 ⟨N, v, hv⟩

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
