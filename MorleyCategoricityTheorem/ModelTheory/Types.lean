import Mathlib.ModelTheory.Topology.Types
import MorleyCategoricityTheorem.ModelTheory.Semantics
import MorleyCategoricityTheorem.ModelTheory.Satisfiability

/-!
# Complete types

This file defines realization and omission for complete types, together with complete types over a
parameter set in a structure.  Isolation of complete types is developed in
`ModelTheory.IsolatedTypes`.

## TODO

- Generalize `typeOf_eq_of_realize_imp` to formula-level extensionality lemmas for arbitrary
  complete types, including one-sided containment and biconditional forms, so callers need not
  pass through `Formula.equivSentence.symm`.
- Develop contravariant reindexing of complete types along variable maps for arbitrary theories,
  including formula membership, compatibility with `typeOf`, functoriality, variance under
  injective or surjective maps, and isolation or topological behavior; avoid assuming a canonical
  covariant extension along injections.
- Generalize `typeOf_eq_of_typeOf_eq_of_subset` from realized types to a contravariant parameter
  restriction map on arbitrary complete types; prove compatibility with formula membership,
  `typeOf`, and composition, relate it to continuous or open maps of Stone spaces, and reformulate
  isolation transport through it where useful.
-/

universe u v w w' x y

namespace FirstOrder

namespace Language

open Theory

namespace Theory

namespace CompleteType

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

/-- A semantic consequence of a sentence in a complete type also belongs to that type. -/
theorem mem_of_mem_of_models_imp (p : T.CompleteType α) {φ ψ : L[[α]].Sentence}
    (hφ : φ ∈ p) (hφψ : (L.lhomWithConstants α).onTheory T ⊨ᵇ φ.imp ψ) : ψ ∈ p := by
  apply p.isMaximal.mem_of_models
  rw [models_sentence_iff]
  intro M
  have hMp : M ⊨ (p : L[[α]].Theory) := inferInstance
  haveI : M ⊨ (L.lhomWithConstants α).onTheory T := hMp.mono p.subset
  exact (hφψ.realize_sentence M) (hMp.realize_of_mem φ hφ)

/-- A complete type contains a conjunction exactly when it contains both conjuncts. -/
@[simp]
theorem inf_mem_iff (p : T.CompleteType α) (φ ψ : L[[α]].Sentence) :
    φ ⊓ ψ ∈ p ↔ φ ∈ p ∧ ψ ∈ p := by
  simp_rw [← SetLike.mem_coe, p.isMaximal.mem_iff_models, models_sentence_iff,
    Sentence.Realize, Formula.realize_inf, forall_and]

/-- A complete type contains a disjunction exactly when it contains one of the disjuncts. -/
@[simp]
theorem sup_mem_iff (p : T.CompleteType α) (φ ψ : L[[α]].Sentence) :
    φ ⊔ ψ ∈ p ↔ φ ∈ p ∨ ψ ∈ p := by
  contrapose!
  simp_rw [← not_mem_iff, ← SetLike.mem_coe, p.isMaximal.mem_iff_models,
    models_sentence_iff, Sentence.Realize, Formula.realize_not, Formula.realize_sup,
    ← forall_and, not_or]

/-- A complete type contains an implication exactly when membership of the antecedent implies
membership of the consequent. -/
@[simp]
theorem imp_mem_iff (p : T.CompleteType α) (φ ψ : L[[α]].Sentence) :
    φ.imp ψ ∈ p ↔ (φ ∈ p → ψ ∈ p) := by
  contrapose!
  simp_rw [← not_mem_iff, ← SetLike.mem_coe, p.isMaximal.mem_iff_models,
    models_sentence_iff, Sentence.Realize, Formula.realize_not, Formula.realize_imp,
    Classical.not_imp, forall_and]

/-- A complete type contains a biconditional exactly when its two sides have equivalent
membership. -/
@[simp]
theorem iff_mem_iff (p : T.CompleteType α) (φ ψ : L[[α]].Sentence) :
    φ.iff ψ ∈ p ↔ (φ ∈ p ↔ ψ ∈ p) := by
  simp_rw [Formula.iff, BoundedFormula.iff]
  rw [← Formula.imp]
  simp only [inf_mem_iff, imp_mem_iff, iff_def]

/-- A complete type is determined by containment in another complete type: maximality makes the
inclusion order antisymmetric on complete types. -/
theorem eq_of_le {p q : T.CompleteType α} (h : (p : L[[α]].Theory) ⊆ q) : p = q := by
  exact le_antisymm h (by
    intro φs hφs
    by_contra hφp
    exact CompleteType.false_of_mem_of_not_mem q.isMaximal.1 hφs
      (h ((CompleteType.not_mem_iff p φs).mpr hφp)))

/-- A basic open set splits into its intersections with a sentence and its negation. -/
theorem typesWith_eq_union_inf_not (φ ψ : L[[α]].Sentence) :
    T.typesWith φ = T.typesWith (φ ⊓ ψ) ∪ T.typesWith (φ ⊓ ∼ψ) := by
  simp [typesWith_inf, typesWith_not]

/-- A complete type is realized by a tuple when it is the type of that tuple. -/
def RealizedBy {N : Type w'} [L.Structure N] [Nonempty N] [N ⊨ T]
    (p : T.CompleteType α) (v : α → N) : Prop :=
  T.typeOf v = p

/-- A complete type is realized in a model when some tuple in the model realizes it. -/
def IsRealizedIn (p : T.CompleteType α) (N : Type w') [L.Structure N] [Nonempty N] [N ⊨ T] :
    Prop :=
  ∃ v : α → N, p.RealizedBy v

/-- A complete type is omitted in a model when no tuple in the model realizes it. -/
def IsOmittedIn (p : T.CompleteType α) (N : Type w') [L.Structure N] [Nonempty N] [N ⊨ T] :
    Prop :=
  ¬p.IsRealizedIn N

/-- Realization is membership in the set of types realized in a model. -/
theorem isRealizedIn_iff_mem_realizedTypes {N : Type w'} [L.Structure N] [Nonempty N] [N ⊨ T]
    (p : T.CompleteType α) : p.IsRealizedIn N ↔ p ∈ T.realizedTypes N α := by
  simp [IsRealizedIn, RealizedBy]

/-- Omission is nonmembership in the set of types realized in a model. -/
theorem isOmittedIn_iff_not_mem_realizedTypes {N : Type w'} [L.Structure N] [Nonempty N]
    [N ⊨ T] (p : T.CompleteType α) : p.IsOmittedIn N ↔ p ∉ T.realizedTypes N α := by
  simp [IsOmittedIn, IsRealizedIn, RealizedBy]

/-- Tuples with the same type realize exactly the same formulas, possibly in different
models. -/
theorem realize_iff_of_typeOf_eq {M : Type w'} {N : Type x} [L.Structure M] [Nonempty M]
    [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T] (v : α → M) (w : α → N)
    (h : T.typeOf v = T.typeOf w) (φ : L.Formula α) :
    φ.Realize v ↔ φ.Realize w := by
  rw [← formula_mem_typeOf (T := T) (v := v) (φ := φ), h,
    formula_mem_typeOf (T := T) (v := w) (φ := φ)]

/-- If every formula realized by one tuple is realized by another, then the tuples have the same
complete type.  One-sided preservation suffices because complete types are maximal. -/
theorem typeOf_eq_of_realize_imp {M : Type w'} {N : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T]
    (v : α → M) (w : α → N) (h : ∀ φ : L.Formula α, φ.Realize v → φ.Realize w) :
    T.typeOf v = T.typeOf w := by
  apply eq_of_le
  intro σs hσs
  let σ : L.Formula α := Formula.equivSentence.symm σs
  have hσv : σ.Realize v := by
    rw [← formula_mem_typeOf (T := T)]
    simpa [σ] using hσs
  simpa [σ] using (formula_mem_typeOf (T := T)).2 (h σ hσv)

/-- Equality of tuple types over a larger parameter set descends along inclusions of parameter
sets. -/
theorem typeOf_eq_of_typeOf_eq_of_subset {M : Type w'} [L.Structure M] [Nonempty M]
    {A B : Set M} (hAB : A ⊆ B) (v w : α → M)
    (h : (L[[B]].completeTheory M).typeOf v = (L[[B]].completeTheory M).typeOf w) :
    (L[[A]].completeTheory M).typeOf v = (L[[A]].completeTheory M).typeOf w := by
  apply typeOf_eq_of_realize_imp
  intro φ hφv
  let φB : (L[[B]]).Formula α :=
    (L.lhomWithConstantsMap (Set.inclusion hAB)).onFormula φ
  have hφB_realize (a : α → M) : φB.Realize a ↔ φ.Realize a := by
    exact LHom.realize_onFormula
      (φ := L.lhomWithConstantsMap (Set.inclusion hAB)) (ψ := φ) (v := a)
  exact (hφB_realize w).1
    ((realize_iff_of_typeOf_eq v w h φB).1 ((hφB_realize v).2 hφv))

/-- Equality of tuple types is preserved by precomposition with a variable map: if two
`β`-tuples have the same type, then the corresponding `α`-tuples obtained by relabelling along
`f : α → β` have the same type as well. -/
theorem typeOf_comp_eq_of_typeOf_eq {M : Type w'} {N : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type y} (f : α → β) (v : β → M) (w : β → N)
    (h : T.typeOf v = T.typeOf w) : T.typeOf (v ∘ f) = T.typeOf (w ∘ f) := by
  classical
  have h' (ψ : L.Formula α) : ψ.Realize (v ∘ f) ↔ ψ.Realize (w ∘ f) := by
    rw [← Formula.realize_relabel (φ := ψ) (g := f) (v := v),
        ← Formula.realize_relabel (φ := ψ) (g := f) (v := w)]
    exact realize_iff_of_typeOf_eq v w h (ψ.relabel f)
  apply SetLike.ext
  intro σs
  rw [mem_typeOf, mem_typeOf]
  exact h' (Formula.equivSentence.symm σs)

/-- Equality of joint tuple types projects to equality of the left tuple types. -/
theorem typeOf_left_of_typeOf_sum_eq {M : Type w'} {N : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type y} (a : α → M) (b : β → M) (c : α → N) (d : β → N)
    (h : T.typeOf (Sum.elim a b) = T.typeOf (Sum.elim c d)) :
    T.typeOf a = T.typeOf c := by
  simpa [Sum.elim_comp_inl] using
    (typeOf_comp_eq_of_typeOf_eq (f := Sum.inl) (v := Sum.elim a b) (w := Sum.elim c d) h)

/-- Equality of joint tuple types projects to equality of the right tuple types. -/
theorem typeOf_right_of_typeOf_sum_eq {M : Type w'} {N : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type y} (a : α → M) (b : β → M) (c : α → N) (d : β → N)
    (h : T.typeOf (Sum.elim a b) = T.typeOf (Sum.elim c d)) :
    T.typeOf b = T.typeOf d := by
  simpa [Sum.elim_comp_inr] using
    (typeOf_comp_eq_of_typeOf_eq (f := Sum.inr) (v := Sum.elim a b) (w := Sum.elim c d) h)

/-- If two tuples have the same type, every finite extension of the first tuple can be transferred
to a finite extension of the second tuple, possibly in a different model. -/
theorem exists_realize_sum_of_typeOf_eq {M : Type w'} {N : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type y} (a : α → M) (b : β → M) (c : β → N)
    (hbc : T.typeOf b = T.typeOf c) {φ : L.Formula (α ⊕ β)}
    (hφ : φ.Realize (Sum.elim a b)) : ∃ a' : α → N, φ.Realize (Sum.elim a' c) := by
  classical
  apply (Formula.realize_existsLeft φ c).1
  apply (realize_iff_of_typeOf_eq b c hbc φ.existsLeft).1
  exact (Formula.realize_existsLeft φ b).2 ⟨a, hφ⟩

end CompleteType

end Theory

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]
variable (A : Set M) (α : Type w')

/-- Complete types over a parameter set `A` inside the structure `M`. -/
abbrev CompleteTypeOver :=
  (L[[A]].completeTheory M).CompleteType α

end Language

end FirstOrder
