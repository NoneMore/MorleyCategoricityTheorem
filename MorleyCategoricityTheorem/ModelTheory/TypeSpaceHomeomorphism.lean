/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Types
import MorleyCategoricityTheorem.ModelTheory.LanguageEmbedding

/-!
# Transporting complete types along language equivalences

A language equivalence `e : L ≃ᴸ L'` that carries a theory `T` onto a theory `T'` identifies the
spaces of complete types over `T` and over `T'`.  A complete type over `T` with variables `α` is,
by definition, a maximal `L[[α]]`-theory extending the constants expansion of `T`, so the transport
acts on sentences of `L[[α]]` through the language equivalence `e.addConstants α`, which extends `e`
to the constant expansions while leaving the free-variable constants unchanged.

## Main definitions

- `FirstOrder.Language.Theory.CompleteType.completeTypeEquiv`: the equivalence of complete types
  `T.CompleteType α ≃ T'.CompleteType α` induced by a language equivalence `e : L ≃ᴸ L'` and a proof
  that `e.toLHom.onTheory T = T'`.

## Main results

- `FirstOrder.Language.Theory.CompleteType.mem_completeTypeEquiv_iff`: membership in the
  transported complete type is membership of the renamed sentence in the original type.
- `FirstOrder.Language.Theory.CompleteType.mem_completeTypeEquiv_symm_iff`: the inverse membership
  rule, formulated for the inverse equivalence.
- `FirstOrder.Language.LHom.onTheory_comp`, `FirstOrder.Language.LHom.id_onTheory` and
  `FirstOrder.Language.LHom.onSentence_not`: `LHom.onSentence` and `LHom.onTheory` are compatible
  with composition, identity, and negation.
- `FirstOrder.Language.LEquiv.invLHom_onTheory_toLHom_onTheory` and
  `FirstOrder.Language.LEquiv.toLHom_onTheory_invLHom_onTheory`: the two maps of a language
  equivalence are mutually inverse on theories.
- `FirstOrder.Language.LEquiv.isMaximal_onTheory`: a language equivalence carries maximal theories
  to maximal theories.
- `FirstOrder.Language.LEquiv.onTheory_addConstants_lhomWithConstants`: adding constants to a
  language equivalence is natural with respect to the constants expansion of a theory.

## TODO

- Move the syntax-only functoriality laws (`LHom.comp_onFormula`, `LHom.comp_onSentence`,
  `LHom.id_onSentence`, `LHom.onSentence_not`, `LHom.onTheory_comp`, `LHom.id_onTheory`,
  `LEquiv.toLHom_addConstants_comp_lhomWithConstants`,
  `LEquiv.onTheory_addConstants_lhomWithConstants`, `LEquiv.invLHom_onTheory_toLHom_onTheory`, and
  `LEquiv.toLHom_onTheory_invLHom_onTheory`) to the syntax layer; see the `## TODO` of
  `ModelTheory/Syntax.lean`.
-/

universe u v u' v' u'' v'' w

namespace FirstOrder

namespace Language

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {L'' : Language.{u'', v''}}

/-- Renaming the symbols of a formula along a composite language map is the composite of the two
renamings. -/
theorem comp_onFormula {α : Type*} (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onFormula : L.Formula α → L''.Formula α) = φ.onFormula ∘ ψ.onFormula :=
  comp_onBoundedFormula φ ψ

/-- Renaming the symbols of a sentence along a composite language map is the composite of the two
renamings. -/
theorem comp_onSentence (φ : L' →ᴸ L'') (ψ : L →ᴸ L') :
    ((φ.comp ψ).onSentence : L.Sentence → L''.Sentence) = φ.onSentence ∘ ψ.onSentence :=
  comp_onFormula φ ψ

/-- Renaming the symbols of a sentence along the identity language map is the identity. -/
@[simp]
theorem id_onSentence (L : Language.{u, v}) :
    ((LHom.id L).onSentence : L.Sentence → L.Sentence) = id :=
  id_onBoundedFormula

/-- Renaming the symbols of a sentence along a language map commutes with negation. -/
@[simp]
theorem onSentence_not (g : L →ᴸ L') (φ : L.Sentence) :
    g.onSentence φ.not = (g.onSentence φ).not :=
  rfl

/-- Renaming the symbols of a theory along a composite language map is the composite of the two
renamings. -/
theorem onTheory_comp (φ : L' →ᴸ L'') (ψ : L →ᴸ L') (T : L.Theory) :
    (φ.comp ψ).onTheory T = φ.onTheory (ψ.onTheory T) := by
  rw [onTheory, onTheory, onTheory, comp_onSentence, Set.image_comp]

/-- Renaming the symbols of a theory along the identity language map is the identity. -/
@[simp]
theorem id_onTheory (T : L.Theory) : (LHom.id L).onTheory T = T := by
  rw [onTheory, id_onSentence, Set.image_id]

end LHom

namespace LEquiv

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- Adding an unchanged type of constants to a language equivalence commutes with the canonical
embedding of a language into its constants expansion. -/
theorem toLHom_addConstants_comp_lhomWithConstants (e : L ≃ᴸ L') (α : Type w) :
    (e.addConstants α).toLHom.comp (L.lhomWithConstants α) =
      (L'.lhomWithConstants α).comp e.toLHom :=
  LHom.sumMap_comp_inl (ϕ := e.toLHom) (ψ := LHom.id (constantsOn α))

/-- Extending a language equivalence by an unchanged type of constants is natural with respect to
the constants expansion of a theory. -/
theorem onTheory_addConstants_lhomWithConstants (e : L ≃ᴸ L') (α : Type w) (T : L.Theory) :
    (e.addConstants α).toLHom.onTheory ((L.lhomWithConstants α).onTheory T) =
      (L'.lhomWithConstants α).onTheory (e.toLHom.onTheory T) := by
  conv_lhs => rw [← LHom.onTheory_comp]
  rw [toLHom_addConstants_comp_lhomWithConstants, LHom.onTheory_comp]

/-- The inverse of a language equivalence undoes the renaming of a theory. -/
theorem invLHom_onTheory_toLHom_onTheory (e : L ≃ᴸ L') (T : L.Theory) :
    e.invLHom.onTheory (e.toLHom.onTheory T) = T := by
  conv_lhs => rw [← LHom.onTheory_comp]
  rw [e.left_inv, LHom.id_onTheory]

/-- The forward map of a language equivalence undoes the inverse renaming of a theory. -/
theorem toLHom_onTheory_invLHom_onTheory (e : L ≃ᴸ L') (T : L'.Theory) :
    e.toLHom.onTheory (e.invLHom.onTheory T) = T := by
  conv_lhs => rw [← LHom.onTheory_comp]
  rw [e.right_inv, LHom.id_onTheory]

/-- A language equivalence carries maximal theories to maximal theories.

Satisfiability transfers along the equivalence, and each sentence of the image is the image of a
sentence of the source theory or of its negation. -/
theorem isMaximal_onTheory (e : L ≃ᴸ L') (T : L.Theory) (hT : T.IsMaximal) :
    (e.toLHom.onTheory T).IsMaximal := by
  refine ⟨?_, ?_⟩
  · exact (Theory.isSatisfiable_onTheory_iff (LEmbedding.ofLEquiv e).injective).mpr hT.1
  · intro φ
    obtain ⟨ψ, rfl⟩ := e.onSentence.surjective φ
    rcases hT.mem_or_not_mem ψ with hψ | hψ
    · exact Or.inl (LHom.mem_onTheory.mpr ⟨ψ, hψ, rfl⟩)
    · have hnot : (e.onSentence ψ).not = e.toLHom.onSentence ψ.not :=
        (LHom.onSentence_not e.toLHom ψ).symm
      refine Or.inr ?_
      rw [hnot]
      exact LHom.mem_onTheory.mpr ⟨ψ.not, hψ, rfl⟩

end LEquiv

namespace Theory

namespace CompleteType

variable {L : Language.{u, v}} {L' : Language.{u', v'}}
variable {T : L.Theory} {T' : L'.Theory} {α : Type w}

/-- The inverse language equivalence carries the transported theory back: if `e` identifies `T` with
`T'`, then `e.symm` identifies `T'` with `T`. -/
private theorem onTheory_symm (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T') :
    e.symm.toLHom.onTheory T' = T := by
  change e.invLHom.onTheory T' = T
  rw [← h, ← LHom.onTheory_comp, e.left_inv, LHom.id_onTheory]

/-- The forward transport of a complete type along a language equivalence `e` identifying `T` with
`T'`: it renames the symbols of the underlying maximal theory along the constants-extended
equivalence `e.addConstants α`. -/
private noncomputable def map (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T')
    (p : T.CompleteType α) : T'.CompleteType α where
  toTheory := (e.addConstants α).toLHom.onTheory p.toTheory
  subset' := by
    rw [← h, ← LEquiv.onTheory_addConstants_lhomWithConstants]
    exact Set.image_mono p.subset
  isMaximal' := LEquiv.isMaximal_onTheory (e.addConstants α) p.toTheory p.isMaximal

/-- Applying the inverse transport after the forward transport returns the original theory. -/
private theorem map_map_toTheory (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T')
    (p : T.CompleteType α) :
    (map e.symm (onTheory_symm e h) (map e h p)).toTheory = p.toTheory := by
  change (e.addConstants α).invLHom.onTheory ((e.addConstants α).toLHom.onTheory p.toTheory)
      = p.toTheory
  rw [LEquiv.invLHom_onTheory_toLHom_onTheory]

/-- Applying the forward transport after the inverse transport returns the original theory. -/
private theorem map_map_toTheory' (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T')
    (p : T'.CompleteType α) :
    (map e h (map e.symm (onTheory_symm e h) p)).toTheory = p.toTheory := by
  change (e.addConstants α).toLHom.onTheory ((e.addConstants α).invLHom.onTheory p.toTheory)
      = p.toTheory
  rw [LEquiv.toLHom_onTheory_invLHom_onTheory]

/-- A language equivalence that carries a theory `T` onto a theory `T'` induces an equivalence
between the complete types over `T` and the complete types over `T'` with the same variables.

The forward direction renames the symbols of the underlying maximal theory along `e.addConstants α`,
and the inverse direction renames them back along `(e.symm).addConstants α`. -/
noncomputable def completeTypeEquiv (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T') :
    T.CompleteType α ≃ T'.CompleteType α where
  toFun := map e h
  invFun := map e.symm (onTheory_symm e h)
  left_inv := fun p => by
    apply SetLike.ext
    intro σ
    change σ ∈ (map e.symm (onTheory_symm e h) (map e h p)).toTheory ↔ σ ∈ p.toTheory
    rw [map_map_toTheory e h p]
  right_inv := fun p => by
    apply SetLike.ext
    intro σ
    change σ ∈ (map e h (map e.symm (onTheory_symm e h) p)).toTheory ↔ σ ∈ p.toTheory
    rw [map_map_toTheory' e h p]

/-- Membership in the transported complete type: a sentence belongs to the image of `p` exactly
when its preimage under the constants-extended language equivalence belongs to `p`. -/
@[simp]
theorem mem_completeTypeEquiv_iff (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T')
    (p : T.CompleteType α) (φ : L'[[α]].Sentence) :
    φ ∈ completeTypeEquiv e h p ↔ (e.addConstants α).onSentence.symm φ ∈ p := by
  change φ ∈ (e.addConstants α).onSentence '' p.toTheory ↔
    (e.addConstants α).onSentence.symm φ ∈ p.toTheory
  exact Set.mem_image_equiv

/-- Membership in the inverse of the transported complete type: a sentence belongs to the preimage
of `p` exactly when its image under the constants-extended language equivalence belongs to `p`. -/
@[simp]
theorem mem_completeTypeEquiv_symm_iff (e : L ≃ᴸ L') (h : e.toLHom.onTheory T = T')
    (p : T'.CompleteType α) (φ : L[[α]].Sentence) :
    φ ∈ (completeTypeEquiv e h).symm p ↔ (e.addConstants α).onSentence φ ∈ p := by
  change φ ∈ ((e.addConstants α).onSentence).symm '' p.toTheory ↔
    (e.addConstants α).onSentence φ ∈ p.toTheory
  rw [Equiv.image_symm_eq_preimage]
  rfl

end CompleteType

end Theory

end Language

end FirstOrder
