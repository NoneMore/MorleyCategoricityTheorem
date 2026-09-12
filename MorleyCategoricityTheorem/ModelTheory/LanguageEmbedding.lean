/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.LanguageMap

import MorleyCategoricityTheorem.ModelTheory.LanguageMap

/-!
# Language embeddings

This file develops a bundled notion of an *embedding between first-order languages*: an
injective language homomorphism.

## Main definitions

- `FirstOrder.Language.LEmbedding L L'`, denoted `L ↪ᴸ L'`, bundles an injective language
  homomorphism `L →ᴸ L'` together with a proof of injectivity on function and relation symbols.
  It is the embedding analogue of `FirstOrder.Language.LHom` and
  `FirstOrder.Language.LEquiv`.
- `LEquiv.lhomWithConstantsCongr`: an equivalence of parameter types `α ≃ β` induces a language
  equivalence `L[[α]] ≃ᴸ L[[β]]`, renaming the added constants.
- `LEquiv.addConstants`: a language equivalence `L ≃ᴸ L'` extends to an equivalence
  `L[[α]] ≃ᴸ L'[[α]]` that leaves a fixed type of new constants unchanged.

## Main results

- `LEmbedding.refl`, `LEmbedding.comp`, `LEmbedding.sumInl`, `LEmbedding.sumInr`, and
  `LEmbedding.lhomWithConstants` provide the basic language embeddings.
- `LEmbedding.ofLEquiv` turns a language equivalence into a language embedding.
- `LEmbedding.lhomWithConstantsMap`: the central construction. An embedding of parameter
  types `f : α ↪ β` induces a language embedding `L[[α]] ↪ᴸ L[[β]]` between the corresponding
  expansions of the base language `L` by constants.
- `LHom.constantsOnMap_comp`, `LHom.constantsOnMap_id`, `LHom.addConstants_comp`,
  `LHom.id_addConstants`, `lhomWithConstantsMap_comp`, and `lhomWithConstantsMap_id` record the
  composition and identity laws for the maps on constant-expanded languages used by the
  equivalences above.
-/

universe u v u' v' u'' v'' u₁ v₁ u₂ v₂ w w' w''

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-- The identity language homomorphism is injective. -/
theorem id_injective (L : Language.{u, v}) : (LHom.id L).Injective := by
  constructor
  · intro n
    change Function.Injective (id : L.Functions n → L.Functions n)
    exact Function.injective_id
  · intro n
    change Function.Injective (id : L.Relations n → L.Relations n)
    exact Function.injective_id

/-- The sum of two injective language homomorphisms is injective. -/
theorem sumMap_injective {L₁ : Language.{u₁, v₁}} {L₂ : Language.{u₂, v₂}}
    {ϕ : L →ᴸ L'} {ψ : L₁ →ᴸ L₂} (hϕ : ϕ.Injective) (hψ : ψ.Injective) :
    (ϕ.sumMap ψ).Injective := by
  constructor
  · intro n
    change Function.Injective (Sum.map (fun f : L.Functions n => ϕ.onFunction f)
        (fun f : L₁.Functions n => ψ.onFunction f))
    exact (Sum.map_injective (f := fun f : L.Functions n => ϕ.onFunction f)
      (g := fun f : L₁.Functions n => ψ.onFunction f)).2 ⟨hϕ.onFunction, hψ.onFunction⟩
  · intro n
    change Function.Injective (Sum.map (fun R : L.Relations n => ϕ.onRelation R)
        (fun R : L₁.Relations n => ψ.onRelation R))
    exact (Sum.map_injective (f := fun R : L.Relations n => ϕ.onRelation R)
      (g := fun R : L₁.Relations n => ψ.onRelation R)).2 ⟨hϕ.onRelation, hψ.onRelation⟩

/-- A map between constant languages is injective when the underlying map of index types is
  injective. -/
theorem constantsOnMap_injective {α : Type w} {β : Type w'} {f : α → β}
    (hf : Function.Injective f) : (LHom.constantsOnMap f).Injective := by
  constructor
  · intro n
    cases n with
    | zero => simpa [LHom.constantsOnMap, constantsOn, constantsOnFunc] using hf
    | succ n => intro c; exact isEmptyElim c
  · intro n R
    exact isEmptyElim R

/-- Composition of maps between constant languages is the map induced by the composite of the
underlying maps on index types. -/
theorem constantsOnMap_comp {α : Type w} {β : Type w'} {γ : Type w''} (f : α → β)
    (g : β → γ) :
    (LHom.constantsOnMap g).comp (LHom.constantsOnMap f) = LHom.constantsOnMap (g ∘ f) := by
  ext n c <;> cases n <;> first | rfl | exact isEmptyElim c

/-- The map between constant languages induced by the identity on the index type is the identity
map. -/
@[simp]
theorem constantsOnMap_id (α : Type w) :
    LHom.constantsOnMap (id : α → α) = LHom.id (constantsOn α) := by
  ext n c <;> cases n <;> first | rfl | exact isEmptyElim c

/-- Adding an unchanged type of constants to the identity language map gives the identity map on
the expanded language. -/
@[simp]
theorem id_addConstants (L : Language.{u, v}) (α : Type w) :
    (LHom.id L).addConstants α = LHom.id L[[α]] := by
  ext n c <;> cases c <;> rfl

/-- Adding an unchanged type of constants commutes with composition of language maps. -/
theorem addConstants_comp (ϕ : L →ᴸ L') (ψ : L' →ᴸ L'') (α : Type w) :
    (ψ.addConstants α).comp (ϕ.addConstants α) = (ψ.comp ϕ).addConstants α := by
  ext n c <;> cases c <;> rfl

end LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-- An embedding of index types induces an injective language map between the expansions of a
  language by constants. -/
theorem lhomWithConstantsMap_injective {α : Type w} {β : Type w'} (f : α ↪ β) :
    (L.lhomWithConstantsMap f).Injective := by
  unfold Language.lhomWithConstantsMap
  exact LHom.sumMap_injective (LHom.id_injective L) (LHom.constantsOnMap_injective f.injective)

/-- Composition of constant-expanding language maps is the constant-expanding map of the
composite. -/
theorem lhomWithConstantsMap_comp (L : Language.{u, v}) {α : Type w} {β : Type w'}
    {γ : Type w''} (f : α → β) (g : β → γ) :
    (L.lhomWithConstantsMap g).comp (L.lhomWithConstantsMap f) =
      L.lhomWithConstantsMap (g ∘ f) := by
  dsimp only [lhomWithConstantsMap, Language.withConstants]
  rw [LHom.sumMap_comp, LHom.id_comp, LHom.constantsOnMap_comp]

/-- The constant-expanding language map induced by the identity on the index type is the identity
map on the expanded language. -/
@[simp]
theorem lhomWithConstantsMap_id (L : Language.{u, v}) (α : Type w) :
    L.lhomWithConstantsMap (id : α → α) = LHom.id L[[α]] := by
  dsimp only [lhomWithConstantsMap, Language.withConstants]
  rw [LHom.constantsOnMap_id, LHom.sumMap_id]

namespace LEquiv

/-- An equivalence of parameter types induces an equivalence between the expansions of a language
by the corresponding constants.

The forward map renames constants along `e` and the inverse map renames them back along `e.symm`. -/
def lhomWithConstantsCongr (L : Language.{u, v}) {α : Type w} {β : Type w'} (e : α ≃ β) :
    L[[α]] ≃ᴸ L[[β]] where
  toLHom := L.lhomWithConstantsMap (e : α → β)
  invLHom := L.lhomWithConstantsMap (e.symm : β → α)
  left_inv := by simp [lhomWithConstantsMap_comp, lhomWithConstantsMap_id]
  right_inv := by simp [lhomWithConstantsMap_comp, lhomWithConstantsMap_id]

/-- Extends a language equivalence by a type of new constants that is left unchanged: the
forward and inverse maps act as the original equivalence on the old symbols and as the identity on
the constants. -/
def addConstants (e : L ≃ᴸ L') (α : Type w) : L[[α]] ≃ᴸ L'[[α]] where
  toLHom := e.toLHom.addConstants α
  invLHom := e.invLHom.addConstants α
  left_inv := by
    rw [LHom.addConstants_comp, e.left_inv, LHom.id_addConstants]
  right_inv := by
    rw [LHom.addConstants_comp, e.right_inv, LHom.id_addConstants]

end LEquiv

/-- An embedding of first-order languages is an injective language homomorphism: it maps
  function and relation symbols of the source language to symbols of the same kind and arity in
  the target language, injectively. -/
structure LEmbedding (L : Language.{u, v}) (L' : Language.{u', v'}) where
  /-- The underlying language homomorphism. -/
  toLHom : L →ᴸ L'
  /-- The underlying language homomorphism is injective on function and relation symbols. -/
  injective' : toLHom.Injective

@[inherit_doc FirstOrder.Language.LEmbedding]
infixl:10 " ↪ᴸ " => LEmbedding

namespace LEmbedding

variable (e : L ↪ᴸ L')

/-- A language embedding is injective on function symbols. -/
theorem injective_onFunction {n : ℕ} :
    Function.Injective fun f : L.Functions n => e.toLHom.onFunction f :=
  e.injective'.onFunction

/-- A language embedding is injective on relation symbols. -/
theorem injective_onRelation {n : ℕ} :
    Function.Injective fun R : L.Relations n => e.toLHom.onRelation R :=
  e.injective'.onRelation

/-- A language embedding is an injective language homomorphism. -/
theorem injective : e.toLHom.Injective :=
  e.injective'

@[ext]
theorem ext {e f : L ↪ᴸ L'} (h : e.toLHom = f.toLHom) : e = f := by
  cases e
  cases f
  congr

theorem toLHom_injective : Function.Injective (fun e : L ↪ᴸ L' => e.toLHom) := by
  intro e f h
  exact ext h

/-- Build a language embedding from a language homomorphism and a proof of injectivity. -/
def ofLHom (ϕ : L →ᴸ L') (h : ϕ.Injective) : L ↪ᴸ L' :=
  ⟨ϕ, h⟩

/-- The identity language embedding. -/
@[refl, simps toLHom]
def refl (L : Language.{u, v}) : L ↪ᴸ L :=
  ⟨LHom.id L, LHom.id_injective L⟩

/-- Composition of language embeddings. -/
@[trans, simps toLHom]
def comp (e' : L' ↪ᴸ L'') (e : L ↪ᴸ L') : L ↪ᴸ L'' :=
  ⟨e'.toLHom.comp e.toLHom, by
    constructor
    · intro n f g h
      exact e.injective.onFunction (e'.injective.onFunction h)
    · intro n R S h
      exact e.injective.onRelation (e'.injective.onRelation h)⟩

/-- The inclusion of the left factor into the sum of two languages is a language embedding. -/
def sumInl (L L' : Language.{u, v}) : L ↪ᴸ L.sum L' :=
  ⟨LHom.sumInl, LHom.sumInl_injective⟩

/-- The inclusion of the right factor into the sum of two languages is a language embedding. -/
def sumInr (L L' : Language.{u, v}) : L' ↪ᴸ L.sum L' :=
  ⟨LHom.sumInr, LHom.sumInr_injective⟩

/-- The canonical embedding of a language into its expansion by constants. -/
def lhomWithConstants (L : Language.{u, v}) (α : Type w) : L ↪ᴸ L[[α]] :=
  ⟨L.lhomWithConstants α, L.lhomWithConstants_injective α⟩

/-- A language equivalence induces a language embedding. -/
def ofLEquiv (e : L ≃ᴸ L') : L ↪ᴸ L' :=
  ⟨e.toLHom, by
    constructor
    · intro n f g h
      have hf : e.invLHom.onFunction (e.toLHom.onFunction f) = f := by
        simpa [LHom.comp, LHom.id] using
          congrArg (fun θ : L →ᴸ L => θ.onFunction f) e.left_inv
      have hg : e.invLHom.onFunction (e.toLHom.onFunction g) = g := by
        simpa [LHom.comp, LHom.id] using
          congrArg (fun θ : L →ᴸ L => θ.onFunction g) e.left_inv
      rw [← hf, ← hg]
      simpa using congrArg (fun f : L'.Functions n => e.invLHom.onFunction f) h
    · intro n R S h
      have hR : e.invLHom.onRelation (e.toLHom.onRelation R) = R := by
        simpa [LHom.comp, LHom.id] using
          congrArg (fun θ : L →ᴸ L => θ.onRelation R) e.left_inv
      have hS : e.invLHom.onRelation (e.toLHom.onRelation S) = S := by
        simpa [LHom.comp, LHom.id] using
          congrArg (fun θ : L →ᴸ L => θ.onRelation S) e.left_inv
      rw [← hR, ← hS]
      simpa using congrArg (fun R : L'.Relations n => e.invLHom.onRelation R) h⟩

/-- An embedding of parameter types induces an embedding of the corresponding constant
  expansions of a base language.

Given an embedding `f : α ↪ β` of parameter types, the induced language map
`L.lhomWithConstantsMap f : L[[α]] →ᴸ L[[β]]` is injective on symbols, so it is a language
embedding `L[[α]] ↪ᴸ L[[β]]`. -/
def lhomWithConstantsMap (L : Language.{u, v}) {α : Type w} {β : Type w'} (f : α ↪ β) :
    L[[α]] ↪ᴸ L[[β]] :=
  ⟨L.lhomWithConstantsMap f, L.lhomWithConstantsMap_injective f⟩

end LEmbedding

end Language

end FirstOrder
