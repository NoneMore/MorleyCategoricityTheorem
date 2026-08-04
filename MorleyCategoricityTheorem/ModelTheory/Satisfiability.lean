/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Satisfiability
import MorleyCategoricityTheorem.ModelTheory.Syntax

/-!
# Additional First-Order Satisfiability

This file extends `Mathlib.ModelTheory.Satisfiability` with two families of results:

- a completeness transfer lemma for formulas: over a complete theory, realization of a formula in a
  single nonempty model transfers to every nonempty model;
- lifting of language embeddings to theories: an injective language map, and in particular a
  language embedding, induces an embedding of theories.

## Main results

- `FirstOrder.Language.Theory.IsComplete.exists_realize_of_isComplete`: a formula realized in one
  model of a complete theory is realized in every nonempty model.
- `FirstOrder.Language.LHom.onTheory_injective`: an injective language map induces an injective map
  on theories.
- `FirstOrder.Language.LEmbedding.mapTheory`: a language embedding induces an embedding of theories.

## Proof outline

For the completeness transfer, given `φ.Realize v` in `M`, the existential closure `φ.exClosure` is
an `L`-sentence realized in `M`. By completeness (`IsComplete.realize_sentence_iff`), `T` models it,
and hence every nonempty model `N` of `T` realizes it. Unfolding the existential closure
(`Formula.realize_exClosure`) and extending the resulting assignment from the free variables of `φ`
to all of `α` using nonemptiness gives a tuple `w : α → N` with `φ.Realize w`.

For the theory embedding, since `LHom.onTheory` is `Set.image` of `LHom.onSentence`, injectivity
follows from `Set.image_injective` applied to `LHom.onSentence_injective`.
-/

universe u v u' v' w w' x y

namespace FirstOrder

namespace Language

namespace Theory

namespace IsComplete

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

/-- A formula realized in one nonempty model of a complete theory is realized in every nonempty
model. -/
theorem exists_realize_of_isComplete {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T]
    (hT : T.IsComplete) (v : α → M) (φ : L.Formula α) (hφ : φ.Realize v) :
    ∀ (N : Type x) [L.Structure N] [Nonempty N] [N ⊨ T], ∃ w : α → N, φ.Realize w := by
  classical
  intro N _ hNe _
  replace hφ : M ⊨ φ.exClosure := by
   refine (Formula.realize_exClosure φ).mpr ⟨fun i => v i,?_⟩
   simpa [Formula.Realize, BoundedFormula.realize_restrictFreeVar] using hφ
  simp [hT.realize_sentence_iff _ M, ←hT.realize_sentence_iff _ N] at hφ
  obtain ⟨w,hw⟩ := hφ
  let w' := Function.extend Subtype.val w (fun _ ↦ Classical.choice hNe)
  exists w'
  rwa [Formula.Realize, BoundedFormula.realize_restrictFreeVar w'] at hw
  intro i; simp [w']

end IsComplete

end Theory

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- The map on theories induced by a language map is injective when the language map is
  injective. -/
theorem onTheory_injective (φ : L →ᴸ L') (h : φ.Injective) :
    Function.Injective (φ.onTheory : L.Theory → L'.Theory) := by
  change Function.Injective (Set.image (φ.onSentence : L.Sentence → L'.Sentence))
  exact Set.image_injective.mpr (onSentence_injective φ h)

end LHom

namespace LEmbedding

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- A language embedding induces an embedding of theories. -/
def mapTheory (e : L ↪ᴸ L') : L.Theory ↪ L'.Theory :=
  (LEmbedding.mapSentence e).image

end LEmbedding

end Language

end FirstOrder
