/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Syntax
import MorleyCategoricityTheorem.ModelTheory.LanguageEmbedding

/-!
# Additional First-Order Syntax

This file extends `Mathlib.ModelTheory.Syntax` with formula constructors needed for Morley's
categoricity theorem. Its declarations are intended to migrate directly to
`Mathlib/ModelTheory/Syntax.lean`, near `Formula.iExs` and `Formula.iExsUnique`.

This is the syntax-only layer. It must not depend on structures, formula realization, set
cardinality, or elementary embeddings.

This file also proves that an injective language homomorphism maps terms, formulas, and sentences
injectively, and that a language embedding `FirstOrder.Language.LEmbedding` therefore induces
embeddings of terms, formulas, and sentences (`LEmbedding.mapTerm`, `LEmbedding.mapFormula`,
`LEmbedding.mapSentence`).

## Main definitions

- `FirstOrder.Language.Formula.iExsAtLeast`: assert the existence of `n` pairwise distinct
  realizing `β`-tuples.
- `FirstOrder.Language.Formula.iExsAtMost`: defined as the negation of having at least `n + 1`
  realizations.
- `FirstOrder.Language.Formula.iExsExactly`: the conjunction of the corresponding lower and upper
  bounds.
- `FirstOrder.Language.Formula.existsExactlyLeft`: a convenience wrapper for formulas whose
  variables are ordered as `β ⊕ α`, implemented by relabeling with `Sum.swap`.

## Construction outline

For `φ : L.Formula (α ⊕ β)`, the lower-bound constructor quantifies a witness block indexed by
`Fin n × β`. The assignment at index `i : Fin n` represents one candidate tuple. The body asserts
that every candidate realizes `φ` and that candidates at distinct indices differ in at least one
coordinate.

The coordinatewise equality conjunction must handle an empty `β` correctly: there is exactly one
empty tuple. Helpers for relabeling a candidate, comparing two tuples, and indexing unequal pairs
are local `let` bindings inside `iExsAtLeast`. The semantic layer can then unfold the public
constructor without turning implementation details into declarations that also need to be migrated.

## Design constraints

- Require `[Finite β]`, because a single first-order formula can quantify the complete assignment
  only for a finite tuple of variables.
- Do not require `[Finite α]`, because the parameter variables remain free.
- Order variables as `α ⊕ β`, consistently with Mathlib's `Formula.iExs` / `Formula.iExsUnique`.
- Keep the natural-number API primary; defer an arbitrary finite index type until it is needed.
-/

universe u v

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {α β : Type*}

namespace Formula

variable (β) in
/-- Asserts that `φ` has at least `n` pairwise distinct realizing `β`-tuples, with free variables
of type `α`.

The formula existentially quantifies a witness block of type `Fin n × β`, asserts that each
candidate realizes `φ`, and that candidates at distinct indices differ in at least one coordinate.
When `β` is empty there is exactly one empty tuple, so the coordinatewise equality conjunction is
vacuously true and its negation is false. -/
noncomputable def iExsAtLeast [Finite β] (n : ℕ) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let realizeAt (i : Fin n) : L.Formula (α ⊕ (Fin n × β)) :=
    φ.relabel (Sum.map id fun b ↦ (i, b))
  let tupleNe (i j : Fin n) : L.Formula (α ⊕ (Fin n × β)) :=
    (iInf fun b : β ↦
      (Term.var (Sum.inr (i, b))).equal (Term.var (Sum.inr (j, b)))).not
  let NePair := {ij : Fin n × Fin n // ij.1 ≠ ij.2}
  let witnessesRealize : L.Formula (α ⊕ (Fin n × β)) :=
    iInf fun i : Fin n ↦ realizeAt i
  let witnessesDistinct : L.Formula (α ⊕ (Fin n × β)) :=
    iInf fun ij : NePair ↦ tupleNe ij.1.1 ij.1.2
  let body := witnessesRealize ⊓ witnessesDistinct
  body.iExs (Fin n × β)

variable (β) in
/-- Asserts that `φ` has at most `n` realizing `β`-tuples, with free variables of type `α`.

Defined as the negation of having at least `n + 1` realizations. -/
noncomputable def iExsAtMost [Finite β] (n : ℕ) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  (φ.iExsAtLeast β (n + 1)).not

variable (β) in
/-- Asserts that `φ` has exactly `n` realizing `β`-tuples, with free variables of type `α`.

Defined as the conjunction of the corresponding lower and upper bounds. -/
noncomputable def iExsExactly [Finite β] (n : ℕ) (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  φ.iExsAtLeast β n ⊓ φ.iExsAtMost β n

/-- Convenience wrapper for formulas whose variables are ordered as `β ⊕ α` rather than `α ⊕ β`.

Implemented by relabeling with `Sum.swap` and then applying `iExsExactly`. -/
noncomputable def existsExactlyLeft [Finite β] (φ : L.Formula (β ⊕ α)) (n : ℕ) : L.Formula α :=
  (φ.relabel Sum.swap).iExsExactly β n

variable [DecidableEq α] [DecidableEq β] in
/-- Existentially quantifies the free variables of `φ : L.Formula (α ⊕ β)` that live in the right
component `β`, leaving the free variables in `α` free.

Following `exClosure`, the formula is first restricted to its finite set of free variables; the
right part is then extracted with `Finset.toRight`, relabeled into the right component of
`α ⊕ φ.freeVarFinset.toRight`, and quantified away with `iExs`. -/
noncomputable def existsRight (φ : L.Formula (α ⊕ β)) : L.Formula α :=
  let g : φ.freeVarFinset → α ⊕ φ.freeVarFinset.toRight := fun x =>
    match x with
    | ⟨Sum.inl a, _⟩ => Sum.inl a
    | ⟨Sum.inr b, hb⟩ => Sum.inr ⟨b, Finset.mem_toRight.2 hb⟩
  iExs φ.freeVarFinset.toRight (Formula.relabel g (φ.restrictFreeVar id))

variable [DecidableEq α] [DecidableEq β] in
/-- Existentially quantifies the free variables of `φ : L.Formula (α ⊕ β)` that live in the left
component `α`, leaving the free variables in `β` free.

Implemented by swapping the two components and applying `existsRight`. -/
noncomputable def existsLeft (φ : L.Formula (α ⊕ β)) : L.Formula β :=
  (φ.relabel Sum.swap).existsRight

end Formula

universe u' v' w

namespace LHom

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {α : Type w}

/-- The map on terms induced by a language map is injective when the language map is injective. -/
theorem onTerm_injective (φ : L →ᴸ L') (h : φ.Injective) :
    Function.Injective (φ.onTerm : L.Term α → L'.Term α) := by
  intro t₁ t₂ h₂
  induction t₁ generalizing t₂ with
  | var i =>
    cases t₂ with
    | var j => simpa [onTerm] using h₂
    | func f ts => cases h₂
  | func f ts ih =>
    cases t₂ with
    | var j => cases h₂
    | func f' ts' =>
      simp only [onTerm] at h₂
      injection h₂ with h_ar hf hts
      subst h_ar
      have hf' : φ.onFunction f = φ.onFunction f' := eq_of_heq hf
      have hff : f = f' := h.onFunction hf'
      have hts' : ts = ts' := by
        funext i
        exact ih i (congr_fun (eq_of_heq hts) i)
      exact congr (congrArg Term.func hff) hts'

/-- The map on bounded formulas induced by a language map is injective when the language map is
  injective. -/
theorem onBoundedFormula_injective (φ : L →ᴸ L') (h : φ.Injective) :
    ∀ {n : ℕ}, Function.Injective
      (φ.onBoundedFormula : L.BoundedFormula α n → L'.BoundedFormula α n) := by
  intro n g₁ g₂ hg
  induction g₁ with
  | falsum =>
    cases g₂ with
    | falsum => rfl
    | equal _ _ => cases hg
    | rel _ _ => cases hg
    | imp _ _ => cases hg
    | all _ => cases hg
  | equal t₁ s₁ =>
    cases g₂ with
    | falsum => cases hg
    | equal t₂ s₂ =>
      simp only [onBoundedFormula, Term.bdEqual] at hg
      injection hg with _ ht hs
      have h_t : t₁ = t₂ := onTerm_injective φ h ht
      have h_s : s₁ = s₂ := onTerm_injective φ h hs
      exact congr (congrArg BoundedFormula.equal h_t) h_s
    | rel _ _ => cases hg
    | imp _ _ => cases hg
    | all _ => cases hg
  | rel R₁ ts₁ =>
    cases g₂ with
    | falsum => cases hg
    | equal _ _ => cases hg
    | rel R₂ ts₂ =>
      simp only [onBoundedFormula, Relations.boundedFormula] at hg
      injection hg with _ h_l hR hts
      subst h_l
      have h_R : R₁ = R₂ := h.onRelation (eq_of_heq hR)
      have h_ts : ts₁ = ts₂ := by
        funext i
        exact onTerm_injective φ h (congr_fun (eq_of_heq hts) i)
      exact congr (congrArg BoundedFormula.rel h_R) h_ts
    | imp _ _ => cases hg
    | all _ => cases hg
  | imp f₁ g₁ ih1 ih2 =>
    cases g₂ with
    | falsum => cases hg
    | equal _ _ => cases hg
    | rel _ _ => cases hg
    | imp f₂ g₂ =>
      simp only [onBoundedFormula] at hg
      injection hg with _ hf hg'
      have h_f : f₁ = f₂ := ih1 hf
      have h_g : g₁ = g₂ := ih2 hg'
      exact congr (congrArg BoundedFormula.imp h_f) h_g
    | all _ => cases hg
  | all f₁ ih =>
    cases g₂ with
    | falsum => cases hg
    | equal _ _ => cases hg
    | rel _ _ => cases hg
    | imp _ _ => cases hg
    | all f₂ =>
      simp only [onBoundedFormula] at hg
      injection hg with _ hf
      exact congrArg BoundedFormula.all (ih hf)

/-- The map on formulas induced by a language map is injective when the language map is
  injective. -/
theorem onFormula_injective (φ : L →ᴸ L') (h : φ.Injective) :
    Function.Injective (φ.onFormula : L.Formula α → L'.Formula α) := by
  simpa [onFormula] using (onBoundedFormula_injective φ h (n := 0))

/-- The map on sentences induced by a language map is injective when the language map is
  injective. -/
theorem onSentence_injective (φ : L →ᴸ L') (h : φ.Injective) :
    Function.Injective (φ.onSentence : L.Sentence → L'.Sentence) := by
  simpa [onSentence] using (onFormula_injective φ h (α := Empty))

end LHom

namespace LEmbedding

variable {L : Language.{u, v}} {L' : Language.{u', v'}}

/-- A language embedding induces an embedding of terms. -/
def mapTerm (e : L ↪ᴸ L') (α : Type w) : L.Term α ↪ L'.Term α :=
  ⟨e.toLHom.onTerm, LHom.onTerm_injective e.toLHom e.injective⟩

/-- A language embedding induces an embedding of formulas. -/
def mapFormula (e : L ↪ᴸ L') (α : Type w) : L.Formula α ↪ L'.Formula α :=
  ⟨e.toLHom.onFormula, LHom.onFormula_injective e.toLHom e.injective⟩

/-- A language embedding induces an embedding of sentences. -/
def mapSentence (e : L ↪ᴸ L') : L.Sentence ↪ L'.Sentence :=
  ⟨e.toLHom.onSentence, LHom.onSentence_injective e.toLHom e.injective⟩

end LEmbedding

end Language

end FirstOrder
