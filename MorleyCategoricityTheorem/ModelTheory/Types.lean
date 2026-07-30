import Mathlib.ModelTheory.Topology.Types

/-!
# Complete types

This file defines realization, omission, and isolation for complete types, together with complete
types over a parameter set in a structure.
-/

universe u v w w' x

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

/-- A complete type is isolated when a formula in it belongs to no other complete type. -/
def IsIsolated (p : T.CompleteType α) : Prop :=
  ∃ φ : L.Formula α, Formula.equivSentence φ ∈ p ∧
    ∀ q : T.CompleteType α, Formula.equivSentence φ ∈ q → q = p

/-- Realization is membership in the set of types realized in a model. -/
theorem isRealizedIn_iff_mem_realizedTypes {N : Type w'} [L.Structure N] [Nonempty N] [N ⊨ T]
    (p : T.CompleteType α) : p.IsRealizedIn N ↔ p ∈ T.realizedTypes N α := by
  simp [IsRealizedIn, RealizedBy]

/-- Omission is nonmembership in the set of types realized in a model. -/
theorem isOmittedIn_iff_not_mem_realizedTypes {N : Type w'} [L.Structure N] [Nonempty N]
    [N ⊨ T] (p : T.CompleteType α) : p.IsOmittedIn N ↔ p ∉ T.realizedTypes N α := by
  simp [IsOmittedIn, IsRealizedIn, RealizedBy]

/-- A type is isolated exactly when one of its basic clopen neighborhoods is its singleton. -/
theorem isIsolated_iff_typesWith_eq_singleton (p : T.CompleteType α) :
    p.IsIsolated ↔ ∃ φ : L.Formula α, T.typesWith (Formula.equivSentence φ) = {p} := by
  simp [IsIsolated, typesWith, Set.eq_singleton_iff_unique_mem]
  rfl

/-- Formula isolation agrees with topological isolation in the Stone space of complete types. -/
theorem isIsolated_iff_isOpen_singleton (p : T.CompleteType α) :
    p.IsIsolated ↔ IsOpen ({p} : Set (T.CompleteType α)) := by
  rw [isIsolated_iff_typesWith_eq_singleton]
  constructor
  · rintro ⟨φ, hφ⟩
    simpa only [hφ] using CompleteType.isOpen_typesWith (T := T) (Formula.equivSentence φ)
  · intro h
    obtain ⟨_, ⟨φ, rfl⟩, hpφ, hφp⟩ :=
      (CompleteType.isTopologicalBasis_range_typesWith).exists_subset_of_mem_open
        (Set.mem_singleton p) h
    refine ⟨Formula.equivSentence.symm φ, ?_⟩
    simpa using Set.Subset.antisymm hφp (Set.singleton_subset_iff.mpr hpφ)

/-- A basic open set is a singleton exactly when its defining sentence semantically entails every
sentence in that type over the ambient theory. -/
theorem singleton_eq_typesWith_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) :
    T.typesWith φ = {p}  ↔
      φ ∈ p ∧ ∀ ψ ∈ p, (L.lhomWithConstants α).onTheory T ⊨ᵇ φ.imp ψ := by
  rw [Set.eq_singleton_iff_unique_mem, mem_typesWith_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro hp ψ hψ
    rw [← setOf_mem_eq_univ_iff, Set.eq_univ_iff_forall]
    intro q
    simpa only [Set.mem_setOf_eq, imp_mem_iff] using fun hφq ↦ hp q hφq ▸ hψ
  · intro hφp q hφq
    rw [mem_typesWith_iff] at hφq
    have hpq : p ≤ q := fun ψ hψ ↦ mem_of_mem_of_models_imp q hφq (hφp ψ hψ)
    apply le_antisymm ?_ hpq
    intro ψ hψq
    by_contra hψp
    exact false_of_mem_of_not_mem q.isMaximal.1 hψq (hpq ((not_mem_iff p ψ).2 hψp))

/-- A nonempty basic open set without isolated types splits into two such basic open sets. -/
theorem exists_isolated_splitting (φ : L[[α]].Sentence)
    (hne : (T.typesWith φ).Nonempty)
    (hni : ∀ p ∈ T.typesWith φ, ¬p.IsIsolated) :
    ∃ ψ : L[[α]].Sentence,
      (T.typesWith (φ ⊓ ψ)).Nonempty ∧
        (T.typesWith (φ ⊓ ∼ψ)).Nonempty ∧
          (∀ p ∈ T.typesWith (φ ⊓ ψ), ¬p.IsIsolated) ∧
            ∀ p ∈ T.typesWith (φ ⊓ ∼ψ), ¬p.IsIsolated := by
  suffices ∃ ψ, (T.typesWith (φ ⊓ ψ)).Nonempty ∧ (T.typesWith (φ ⊓ ∼ψ)).Nonempty by
    obtain ⟨ψ, hψ, hnψ⟩ := this
    refine ⟨ψ, hψ, hnψ, ?_⟩
    simp only [typesWith_inf, Set.mem_inter_iff]
    exact ⟨fun p hp ↦ hni p hp.1, fun p hp ↦ hni p hp.1⟩
  simp only [IsIsolated] at hni
  push Not at hni
  obtain ⟨p, hpφ⟩ := hne
  obtain ⟨q, hqφ, hpq⟩ := hni p hpφ (Formula.equivSentence.symm φ) (by simpa using hpφ)
  simp only [_root_.Equiv.apply_symm_apply] at hqφ
  simp only [ne_eq, SetLike.ext_iff, not_forall, not_iff] at hpq
  obtain ⟨ψ, hψ⟩ := hpq
  simp only [Set.nonempty_def, mem_typesWith_iff, inf_mem_iff, not_mem_iff]
  rcases p.mem_or_not_mem ψ with hψp | hψp
  · exact ⟨ψ, ⟨p, hpφ, hψp⟩, q, hqφ, hψ.mpr hψp⟩
  · have hψnp := (not_mem_iff p ψ).mp hψp
    exact ⟨ψ, ⟨q, hqφ, Classical.not_not.mp (mt hψ.mp hψnp)⟩, p, hpφ, hψnp⟩

/-- The type of the left tuple of a pair of tuples is isolated whenever their joint type is
isolated. -/
theorem isIsolated_typeOf_left {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] (a : α → M) (b : β → M)
    (h : (T.typeOf (Sum.elim a b)).IsIsolated) : (T.typeOf a).IsIsolated := by
  classical
  rw [isIsolated_iff_typesWith_eq_singleton] at h ⊢
  obtain ⟨φ,hφ⟩ := h
  simp_rw [singleton_eq_typesWith_iff] at hφ
  obtain ⟨hφ, hφ'⟩ := hφ
  let ψ : L.Formula α := Formula.equivSentence.symm <| Formula.exClosure (BoundedFormula.constantsVarsEquiv.symm φ)
  exists ψ
  simp_rw [singleton_eq_typesWith_iff]
  refine ⟨?_,?_⟩
  · refine formula_mem_typeOf.mpr ?_
    simp [ψ]
    rw [Formula.realize_equivSentence_symm, @Formula.realize_exClosure]
    letI : (constantsOn α).Structure M := constantsOn.structure a
    refine ⟨fun i ↦ b i, ?_⟩
    apply (BoundedFormula.realize_restrictFreeVar b (by intro i; rfl)).mpr
    rw [← BoundedFormula.realize_constantsVarsEquiv]
    rw [_root_.Equiv.apply_symm_apply]
    change φ.Realize (Sum.elim a b)
    exact formula_mem_typeOf.mp hφ
  · intro ϕ hϕ
    let χ : L.Formula (α ⊕ β) := (Formula.equivSentence.symm ϕ).relabel (Sum.inl)
    specialize hφ' (Formula.equivSentence χ) ?_
    · simp [χ]
      exact (Formula.realize_equivSentence_symm M ϕ a).mpr hϕ
    rw [models_sentence_iff]
    intro N
    haveI : (L.lhomWithConstants α).IsExpansionOn ↑N :=
      LHom.isExpansionOn_reduct (L.lhomWithConstants α) ↑N
    simp only [Sentence.realize_imp]
    intro hψN
    simp only [_root_.Equiv.apply_symm_apply, Formula.realize_exClosure, ψ] at hψN
    obtain ⟨v,hv⟩ := hψN
    let v' : β → N :=
      Function.extend Subtype.val v (fun _ ↦ Classical.choice N.nonempty')
    -- Expanding the existing `L[[α]]`-structure again by `β` gives `L[[α]][[β]]`, which is
    -- canonically equivalent to the one-step expansion `L[[α ⊕ β]]`. Since these languages are
    -- not definitionally equal, we explicitly build the latter: its `α`-constants retain their
    -- current interpretations in `N`, while its `β`-constants are interpreted by `v'`.
    letI : (constantsOn (α ⊕ β)).Structure N :=
      constantsOn.structure <| Sum.elim (fun i ↦ (L.con i : N)) v'
    haveI : N ⊨ (L.lhomWithConstants (α ⊕ β)).onTheory T := by
      simpa [LHom.onTheory_model] using N.is_model
    have hχN : N ⊨ Formula.equivSentence χ := by
      apply hφ'.realize_sentence
      change N ⊨ Formula.equivSentence φ
      simp
      change φ.Realize <| Sum.elim (fun i ↦ (L.con i : N)) v'
      rw [← _root_.Equiv.apply_symm_apply BoundedFormula.constantsVarsEquiv φ]
      refine BoundedFormula.realize_constantsVarsEquiv.mpr
          ((BoundedFormula.realize_restrictFreeVar v' ?_).mp hv)
      intro i; simp [v']
    simp only [Formula.realize_equivSentence, Formula.realize_relabel, χ] at hχN
    rwa [← Formula.realize_equivSentence_symm_con N ϕ]

end CompleteType

end Theory

variable (L : Language.{u, v}) {M : Type w} [L.Structure M]
variable (A : Set M) (α : Type w')

/-- Complete types over a parameter set `A` inside the structure `M`. -/
abbrev CompleteTypeOver :=
  (L[[A]].completeTheory M).CompleteType α

end Language

end FirstOrder
