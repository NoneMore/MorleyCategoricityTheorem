import MorleyCategoricityTheorem.ModelTheory.Equivalence
import MorleyCategoricityTheorem.ModelTheory.Types

/-!
# Isolated complete types

This file develops isolation for complete types, complementing `ModelTheory.Types`, which defines
realization and omission.  It gives the definition of an isolated type, its characterizations in
terms of basic open sets and the topology of the Stone space of complete types, and the projection
and transitivity results for isolated types of tuples.

## Main definitions

- `CompleteType.IsolatedBy`: a formula belongs to exactly one complete type.
- `CompleteType.IsIsolated`: a complete type admits an isolating formula.

## Main results

- `CompleteType.isolatedBy_iff_typesWith_eq_singleton` and
  `CompleteType.isIsolated_iff_isOpen_singleton` identify formula isolation with singleton basic
  opens and topological isolation in the Stone space.
- `CompleteType.isolatedBy_iff_models_imp` and
  `CompleteType.IsolatedBy.realize_iff_typeOf_eq` give semantic characterizations of isolation.
- `CompleteType.exists_isolated_splitting` splits a nonempty basic open set containing no isolated
  type.
- `CompleteType.isIsolated_typeOf_left` projects isolation from a joint tuple to its left
  coordinates.
- `CompleteType.typeOf_isolatedBy_iff_of_isComplete` characterizes isolation inside one model of a
  complete theory.
- `CompleteType.isIsolated_typeOf_trans` transports isolation down a parameter-set inclusion.
-/

universe u v w w' x

namespace FirstOrder

namespace Language

open Theory

namespace Theory

namespace CompleteType

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

/-! ## Definitions and basic API -/

/-- A complete type is isolated by a formula when that formula belongs to it and to no other
complete type. -/
def IsolatedBy (p : T.CompleteType α) (φ : L.Formula α) : Prop :=
  Formula.equivSentence φ ∈ p ∧ ∀ q : T.CompleteType α, Formula.equivSentence φ ∈ q → q = p

/-- A complete type is isolated when some formula isolates it. -/
def IsIsolated (p : T.CompleteType α) : Prop :=
  ∃ φ : L.Formula α, p.IsolatedBy φ

/-- A type is isolated exactly when some formula isolates it. -/
theorem isIsolated_iff_exists_isolatedBy (p : T.CompleteType α) :
    p.IsIsolated ↔ ∃ φ : L.Formula α, p.IsolatedBy φ := by
  rfl

namespace IsolatedBy

variable {p : T.CompleteType α} {φ : L.Formula α}

/-- An isolating formula belongs to the complete type that it isolates. -/
theorem mem (h : p.IsolatedBy φ) : Formula.equivSentence φ ∈ p := h.1

/-- Any complete type containing an isolating formula is the type that it isolates. -/
theorem eq_of_mem (h : p.IsolatedBy φ)
    {q : T.CompleteType α} (hq : Formula.equivSentence φ ∈ q) :
    q = p :=
  h.2 q hq

/-- Membership of an isolating formula characterizes the isolated complete type. -/
theorem mem_iff (h : p.IsolatedBy φ) (q : T.CompleteType α) :
    Formula.equivSentence φ ∈ q ↔ q = p :=
  ⟨fun a ↦ eq_of_mem h a,fun heq => heq ▸ mem h⟩

/-- A complete type admitting a specified isolating formula is isolated. -/
theorem isIsolated (h : p.IsolatedBy φ) : p.IsIsolated := ⟨φ,h⟩

end IsolatedBy

/-! ## Topological and semantic characterizations -/

/-- A type is isolated by a formula exactly when its basic clopen neighborhood is its singleton.
-/
theorem isolatedBy_iff_typesWith_eq_singleton (p : T.CompleteType α) (φ : L.Formula α) :
    p.IsolatedBy φ ↔ T.typesWith (Formula.equivSentence φ) = {p} := by
  simp [IsolatedBy, typesWith, Set.eq_singleton_iff_unique_mem]
  rfl

/-- A type is isolated exactly when one of its basic clopen neighborhoods is its singleton. -/
theorem isIsolated_iff_typesWith_eq_singleton (p : T.CompleteType α) :
    p.IsIsolated ↔ ∃ φ : L.Formula α, T.typesWith (Formula.equivSentence φ) = {p} := by
  simp only [isIsolated_iff_exists_isolatedBy,
      isolatedBy_iff_typesWith_eq_singleton]

/-- Formula isolation agrees with topological isolation in the Stone space of complete types. -/
theorem isIsolated_iff_isOpen_singleton (p : T.CompleteType α) :
    p.IsIsolated ↔ IsOpen ({p} : Set (T.CompleteType α)) := by
  rw [isIsolated_iff_typesWith_eq_singleton]
  constructor
  · rintro ⟨φ, hφ⟩
    exact hφ ▸ CompleteType.isOpen_typesWith (T := T) (Formula.equivSentence φ)
  · intro h
    obtain ⟨_, ⟨φ, rfl⟩, hpφ, hφp⟩ :=
      (CompleteType.isTopologicalBasis_range_typesWith).exists_subset_of_mem_open
        (Set.mem_singleton p) h
    exact ⟨Formula.equivSentence.symm φ,
      by simpa using Set.Subset.antisymm hφp (Set.singleton_subset_iff.mpr hpφ)⟩

/-- A basic open set is a singleton exactly when its defining sentence semantically entails every
sentence in that type over the ambient theory. -/
theorem typesWith_eq_singleton_iff (p : T.CompleteType α) (φ : L[[α]].Sentence) :
    T.typesWith φ = {p} ↔
      φ ∈ p ∧ ∀ ψ ∈ p, (L.lhomWithConstants α).onTheory T ⊨ᵇ φ.imp ψ := by
  rw [Set.eq_singleton_iff_unique_mem, mem_typesWith_iff]
  refine and_congr_right fun _ ↦ ?_
  constructor
  · intro hp ψ hψ
    simpa [← setOf_mem_eq_univ_iff, Set.eq_univ_iff_forall, imp_mem_iff] using
      fun q hφq ↦ hp q hφq ▸ hψ
  · intro hφp q hφq
    exact (eq_of_le (fun ψ hψ ↦ mem_of_mem_of_models_imp q hφq (hφp ψ hψ))).symm

namespace IsolatedBy

variable {p : T.CompleteType α} {φ : L.Formula α}

/-- The basic clopen set defined by an isolating formula is the singleton of the isolated type. -/
theorem typesWith_eq_singleton
    (h : p.IsolatedBy φ) : T.typesWith (Formula.equivSentence φ) = {p} :=
  (p.isolatedBy_iff_typesWith_eq_singleton φ).mp h

/-- An isolating formula semantically entails every sentence in the isolated type. -/
theorem models_imp
    (h : p.IsolatedBy φ) {ψ : L[[α]].Sentence} (hψ : ψ ∈ p) :
    (L.lhomWithConstants α).onTheory T ⊨ᵇ (Formula.equivSentence φ).imp ψ := by
  exact
      ((typesWith_eq_singleton_iff p (Formula.equivSentence φ)).mp
        h.typesWith_eq_singleton).2 ψ hψ

/-- Membership in an isolated type is equivalent to semantic consequence of its isolating
formula. -/
theorem mem_iff_models_imp
    (h : p.IsolatedBy φ) (ψ : L[[α]].Sentence) :
    ψ ∈ p ↔
      (L.lhomWithConstants α).onTheory T ⊨ᵇ
        (Formula.equivSentence φ).imp ψ := by
  constructor
  · exact h.models_imp
  · exact p.mem_of_mem_of_models_imp h.mem

variable {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T]

/-- A tuple realizes an isolating formula exactly when it realizes the isolated type. -/
theorem realize_iff_realizedBy
    (h : p.IsolatedBy φ) (v : α → M) :
    φ.Realize v ↔ p.RealizedBy v := by
  rw [RealizedBy]
  constructor
  · intro hφb
    rwa [← propext (h.mem_iff (T.typeOf v)), formula_mem_typeOf]
  · intro hb
    rwa [← propext (h.mem_iff (T.typeOf v)), formula_mem_typeOf] at hb

/-- A tuple realizes an isolating formula exactly when its complete type is the isolated type. -/
theorem realize_iff_typeOf_eq
    (h : p.IsolatedBy φ) (v : α → M) :
    φ.Realize v ↔ T.typeOf v = p :=
  h.realize_iff_realizedBy v

/-- Any tuple realizing a formula that isolates `T.typeOf a` has the same type as `a`. -/
theorem typeOf_eq_of_realize
    {a : α → M} {b : α → M}
    (h : (T.typeOf a).IsolatedBy φ) (hφb : φ.Realize b) :
    T.typeOf b = T.typeOf a :=
  (h.realize_iff_typeOf_eq b).mp hφb

/-! ### Calculus of isolating formulas -/

variable {ψ : L.Formula α}

/-- A stronger formula in an isolated type also isolates that type. -/
theorem of_mem_of_models_imp
    (hφ : p.IsolatedBy φ) (hψ : Formula.equivSentence ψ ∈ p)
    (himp :
      (L.lhomWithConstants α).onTheory T ⊨ᵇ
        (Formula.equivSentence ψ).imp
          (Formula.equivSentence φ)) :
    p.IsolatedBy ψ :=
  ⟨hψ, fun q hψq ↦ hφ.eq_of_mem (q.mem_of_mem_of_models_imp hψq himp)⟩

/-- Conjoining an isolating formula with any formula in its type preserves isolation. -/
theorem inf (hφ : p.IsolatedBy φ) (hψ : Formula.equivSentence ψ ∈ p) :
    p.IsolatedBy (φ ⊓ ψ) := by
  apply of_mem_of_models_imp hφ ?_ ?_
  · rw [@Formula.equivSentence_inf]
    refine (inf_mem_iff p (Formula.equivSentence φ) (Formula.equivSentence ψ)).mpr ?_
    exact And.imp_right (fun a ↦ hψ) hφ
  · refine models_sentence_iff.mpr ?_
    intro M
    simp; intro hM
    simp [Formula.equivSentence_inf] at hM
    exact hM.1

/-- A formula semantically equivalent to an isolating formula isolates the same type. -/
theorem congr (hφ : p.IsolatedBy φ) (hφψ : φ ⇔[T] ψ) :
    p.IsolatedBy ψ := by
  apply hφ.of_mem_of_models_imp
  · exact (hφ.mem_iff_models_imp _).2 (imp_iff_imp_of_equivSentence.1 hφψ.mp)
  · exact imp_iff_imp_of_equivSentence.1 hφψ.mpr

/-- A formula cannot isolate two different complete types. -/
theorem eq
    (hp : p.IsolatedBy φ) {q : T.CompleteType α} (hq : q.IsolatedBy φ) :
      p = q :=
  (hp.eq_of_mem hq.mem).symm

/-- Two formulas isolating the same complete type are semantically equivalent. -/
theorem siff (hφ : p.IsolatedBy φ) (hψ : p.IsolatedBy ψ) :
    φ ⇔[T] ψ := by
  rw [iff_iff_iff_of_equivSentence, iff_iff_imp_and_imp]
  refine ⟨models_imp hφ hψ.1,models_imp hψ hφ.1⟩

end IsolatedBy

variable {p : T.CompleteType α} {φ : L.Formula α}

/-- A formula isolates a complete type exactly when it belongs to that type and semantically
entails every sentence in it. -/
theorem isolatedBy_iff_models_imp :
    p.IsolatedBy φ ↔
      Formula.equivSentence φ ∈ p ∧
        ∀ ψ ∈ p,
          (L.lhomWithConstants α).onTheory T ⊨ᵇ
            (Formula.equivSentence φ).imp ψ := by
  refine ⟨?_,?_⟩
  · refine fun a ↦ ?_
    refine (typesWith_eq_singleton_iff p (Formula.equivSentence φ)).mp ?_
    exact (isolatedBy_iff_typesWith_eq_singleton p φ).mp a
  · refine fun a ↦ ?_
    refine (isolatedBy_iff_typesWith_eq_singleton p φ).mpr ?_
    exact (typesWith_eq_singleton_iff p (Formula.equivSentence φ)).mpr a

/-- A formula isolates a complete type exactly when every realization of the formula in every
canonical bundled model has that complete type. -/
theorem isolatedBy_iff_forall_modelType :
    p.IsolatedBy φ ↔
      Formula.equivSentence φ ∈ p ∧
        ∀ (N : Theory.ModelType.{u, v, max u v w} T) (b : α → N),
          φ.Realize b → T.typeOf b = p := by
  constructor
  · intro hpφ
    refine ⟨hpφ.1,?_⟩
    intro N b hφb
    rwa [← propext (IsolatedBy.realize_iff_typeOf_eq hpφ b)]
  · rintro ⟨hφp,h⟩
    refine ⟨hφp, ?_⟩
    intro q hφq
    rcases T.exists_modelType_is_realized_in q with ⟨N, b, hb⟩
    have hφb : φ.Realize b :=
      formula_mem_typeOf.mp (hb ▸ hφq)
    exact hb.symm.trans (h N b hφb)

/-- A complete type is isolated exactly when one of its formulas uniquely determines its type in
every canonical bundled model. -/
theorem isIsolated_iff_exists_forall_modelType :
    p.IsIsolated ↔
      ∃ φ,
        Formula.equivSentence φ ∈ p ∧
          ∀ (N : Theory.ModelType.{u, v, max u v w} T) (b : α → N),
            φ.Realize b → T.typeOf b = p :=
  exists_congr fun _ ↦ isolatedBy_iff_forall_modelType

/-! ## Splitting non-isolated basic open sets -/

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
  simp only [IsIsolated, IsolatedBy] at hni
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

/-! ## Projection of isolated types -/

/-- The type of the left tuple of a pair of tuples is isolated whenever their joint type is
isolated. -/
theorem isIsolated_typeOf_left {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T] (a : α → M) (b : β → M)
    (h : (T.typeOf (Sum.elim a b)).IsIsolated) : (T.typeOf a).IsIsolated := by
  classical
  rw [isIsolated_iff_exists_isolatedBy] at h ⊢
  obtain ⟨φ, hφ⟩ := h
  refine ⟨φ.existsRight, ?_⟩
  rw [isolatedBy_iff_forall_modelType]
  refine ⟨?_, ?_⟩
  · exact formula_mem_typeOf.mpr
      ((Formula.realize_existsRight φ a).2 ⟨b, formula_mem_typeOf.mp hφ.mem⟩)
  · intro N c hψc
    obtain ⟨d, hφcd⟩ := (Formula.realize_existsRight φ c).1 hψc
    exact (typeOf_left_of_typeOf_sum_eq (a := a) (b := b) (c := c) (d := d)
      ((IsolatedBy.realize_iff_typeOf_eq hφ (Sum.elim c d)).mp hφcd).symm).symm

/-! ## Isolation in a fixed model of a complete theory -/

/-- Over a complete theory, a formula isolates the type of a realized tuple exactly when it
realizes there and isolates it among all tuples of a single fixed model. -/
theorem typeOf_isolatedBy_iff_of_isComplete (hT : T.IsComplete)
    {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (a : α → M) (φ : L.Formula α) :
    (T.typeOf a).IsolatedBy φ ↔
      φ.Realize a ∧ ∀ b : α → M, φ.Realize b → T.typeOf b = T.typeOf a := by
  classical
  constructor
  · rintro ⟨hφ, hφ'⟩
    exact ⟨formula_mem_typeOf.mp hφ, fun b hφb ↦ hφ' (T.typeOf b) (formula_mem_typeOf.mpr hφb)⟩
  · rintro ⟨hφa, hφ⟩
    refine ⟨formula_mem_typeOf.mpr hφa, fun q hφq ↦ eq_of_le (fun ψ hψ ↦ ?_)⟩
    rcases T.exists_modelType_is_realized_in q with ⟨N, b, hb⟩
    rw [← hb, SetLike.mem_coe, mem_typeOf] at hψ
    rw [← hb, formula_mem_typeOf] at hφq
    rcases hT.exists_realize_of_isComplete b (φ ⊓ Formula.equivSentence.symm ψ)
        (Formula.realize_inf.mpr ⟨hφq, hψ⟩) M with ⟨c, hc⟩
    simpa [← hφ c (Formula.realize_inf.mp hc).1] using (Formula.realize_inf.mp hc).2

/-- Over a complete theory, a type realized by a tuple is isolated exactly when one of its
formulas isolates it among all tuples of a single fixed model. -/
theorem isIsolated_typeOf_iff_of_isComplete (hT : T.IsComplete)
    {M : Type w'} [L.Structure M] [Nonempty M] [M ⊨ T] (a : α → M) :
    (T.typeOf a).IsIsolated ↔
      ∃ φ : L.Formula α, φ.Realize a ∧
          ∀ b : α → M, φ.Realize b → T.typeOf b = T.typeOf a := by
  rw [isIsolated_iff_exists_isolatedBy]
  exact exists_congr (fun φ ↦ typeOf_isolatedBy_iff_of_isComplete hT a φ)

/-! ## Transitivity over parameter sets -/

/-- Isolation is transitive from a larger parameter set to a smaller one when finite tuples from
the larger set have isolated types over the smaller set. -/
theorem isIsolated_typeOf_trans
    {L : Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]
    {A B : Set M} (hAB : A ⊆ B) {α : Type w'} (a : α → M)
    (hB : ∀ (n : ℕ) (b : Fin n → B),
      ((L[[A]].completeTheory M).typeOf (fun i ↦ (b i : M))).IsIsolated)
    (ha : ((L[[B]].completeTheory M).typeOf a).IsIsolated) :
    ((L[[A]].completeTheory M).typeOf a).IsIsolated := by
  classical
  let T_A := L[[A]].completeTheory M
  let T_B := L[[B]].completeTheory M
  have hT_A : T_A.IsComplete := by
    simpa [T_A] using completeTheory.isComplete (L := L[[A]]) M
  have hT_B : T_B.IsComplete := by
    simpa [T_B] using completeTheory.isComplete (L := L[[B]]) M
  change (T_B.typeOf a).IsIsolated at ha
  change (T_A.typeOf a).IsIsolated
  rw [isIsolated_typeOf_iff_of_isComplete hT_B] at ha
  rw [isIsolated_typeOf_iff_of_isComplete hT_A]
  obtain ⟨θ, hθa, hθunique⟩ := ha
  -- Replace the finitely many parameters from `B` occurring in `θ` by free variables: the
  -- constant-free formula `φ' : L.Formula (α ⊕ Fin n)` realizes at `Sum.elim v (fun i ↦ (b i : M))`
  -- exactly when `θ` realizes at `v`, with `b : Fin n → B` listing those parameters.
  rcases Formula.exists_fin_params θ with ⟨n, b, φ', hθ'⟩
  let bm : Fin n → M := fun i ↦ (b i : M)
  -- An isolating formula `ψ` for the type of the finite tuple `bm` over `A`.
  obtain ⟨ψ, hψbm, hψunique⟩ :
      ∃ ψ : (L[[A]]).Formula (Fin n), ψ.Realize bm ∧
        ∀ d : Fin n → M, ψ.Realize d → T_A.typeOf d = T_A.typeOf bm := by
    rw [← isIsolated_typeOf_iff_of_isComplete hT_A]
    simpa [T_A, bm] using hB n b
  -- Existentially projecting a formula controlling the joint tuple gives the desired formula.
  let θA : (L[[A]]).Formula (α ⊕ Fin n) := (L.lhomWithConstants A).onFormula φ'
  let χ : (L[[A]]).Formula (α ⊕ Fin n) := θA ⊓ ψ.relabel Sum.inr
  have hθA_realize (x : α → M) : θA.Realize (Sum.elim x bm) ↔ θ.Realize x := by
    unfold θA
    rw [LHom.realize_onFormula]
    simpa [bm] using (hθ' x).symm
  refine ⟨χ.existsRight, ?_, ?_⟩
  · apply (Formula.realize_existsRight χ a).2
    refine ⟨bm, ?_⟩
    simp only [χ, Formula.realize_inf, Formula.realize_relabel]
    exact ⟨(hθA_realize a).2 hθa, by simpa using hψbm⟩
  · intro c hc
    obtain ⟨d, hχcd⟩ := (Formula.realize_existsRight χ c).1 hc
    simp only [χ, Formula.realize_inf, Formula.realize_relabel] at hχcd
    have hd : T_A.typeOf d = T_A.typeOf bm := hψunique d (by simpa using hχcd.2)
    apply typeOf_eq_of_realize_imp
    intro σ hσc
    let τ : (L[[A]]).Formula (α ⊕ Fin n) := σ.relabel Sum.inl ⊓ θA
    have hτcd : τ.Realize (Sum.elim c d) := by
      simp only [τ, Formula.realize_inf, Formula.realize_relabel]
      exact ⟨by simpa using hσc, hχcd.1⟩
    obtain ⟨x₀, hτx₀⟩ := exists_realize_sum_of_typeOf_eq c d bm hd hτcd
    simp only [τ, Formula.realize_inf, Formula.realize_relabel] at hτx₀
    have hx₀ : T_B.typeOf x₀ = T_B.typeOf a :=
      hθunique x₀ ((hθA_realize x₀).1 hτx₀.2)
    have hx₀A : T_A.typeOf x₀ = T_A.typeOf a := by
      simpa [T_A, T_B] using typeOf_eq_of_typeOf_eq_of_subset hAB x₀ a hx₀
    exact (realize_iff_of_typeOf_eq x₀ a hx₀A σ).1 (by simpa using hτx₀.1)

end CompleteType

end Theory

end Language

end FirstOrder
