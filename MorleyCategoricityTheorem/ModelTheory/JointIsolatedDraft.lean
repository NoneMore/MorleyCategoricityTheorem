import MorleyCategoricityTheorem.ModelTheory.Types

/-!
# Draft: joint type isolation

This is a scratch file working toward a proof of

```lean
theorem joint_isolated_iff_of_realizedBy {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T]
    (p : T.CompleteType (α ⊕ β)) (a : α → M) (b : β → M)
    (hp : p.RealizedBy (Sum.elim a b)) :
    p.IsIsolated ↔
      (T.typeOf a).IsIsolated ∧ (typeOfOverType (T := T) a b).IsIsolated
```

from `MorleyCategoricityTheorem.ModelTheory.Types`.
-/

universe u v w w' x y

namespace FirstOrder

namespace Language

open Theory

namespace Theory

namespace CompleteType

variable {L : Language.{u, v}} {T : L.Theory} {α : Type w}

/-- Sentences with constants for `α ⊕ β` are in natural bijection with sentences with constants
for `α` followed by constants for `β`: read the joint constants back as free variables, split
them into the `α`- and `β`-parts, and turn them into constants again. -/
def typeOfOverTypeEquiv {β : Type w'} : (L[[α ⊕ β]]).Sentence ≃ ((L[[α]])[[β]]).Sentence :=
  Formula.equivSentence.symm.trans (BoundedFormula.constantsVarsEquiv.symm.trans Formula.equivSentence)

/-- Membership in the type of `b` over the type of `a` is realization of the formula. -/
lemma mem_typeOfOverType_iff_formula {N : Type w'} [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type x} (a : α → N) (b : β → N) (φ : (L[[α]]).Formula β) :
    letI : (constantsOn α).Structure N := constantsOn.structure a
    letI : L[[α]].Structure N := inferInstance
    Formula.equivSentence φ ∈ (typeOfOverType (T := T) a b) ↔ φ.Realize b := by
  letI : (constantsOn α).Structure N := constantsOn.structure a
  haveI : N ⊨ (T.typeOf a).toTheory := by
    dsimp [Theory.typeOf]
    infer_instance
  exact CompleteType.formula_mem_typeOf

/-- Realization of a formula is invariant under having the same complete type, possibly in
different models. -/
lemma realize_iff_of_typeOf_eq {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type x} [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type w'} {v : β → M} {w : β → N} (h : T.typeOf v = T.typeOf w) (φ : L.Formula β) :
    φ.Realize v ↔ φ.Realize w := by
  rw [← CompleteType.formula_mem_typeOf (M := M) (T := T)]
  rw [h]
  rw [CompleteType.formula_mem_typeOf (M := N) (T := T)]

/-- A formula isolating a type is satisfied by exactly the tuples whose type is that type. -/
lemma typeOf_eq_of_isolating_witness {β : Type w'}
    (ψ : L.Formula β) {p : T.CompleteType β} (hisol : p.IsolatedBy ψ)
    {N : Type x} [L.Structure N] [Nonempty N] [N ⊨ T] {v : β → N}
    (hv : ψ.Realize v) : T.typeOf v = p := by
  exact hisol.2 (T.typeOf v) ((CompleteType.formula_mem_typeOf).mpr hv)

/-- Realizing an `L`-formula on the pair `(a, b)` is equivalent to membership of the corresponding
formula with constants in the type of `b` over the type of `a`. -/
lemma realize_sum_iff_mem_typeOfOverType {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : α → M) (b : β → M) (δ : L.Formula (α ⊕ β)) :
    δ.Realize (Sum.elim a b) ↔
      Formula.equivSentence (BoundedFormula.constantsVarsEquiv.symm δ) ∈
        typeOfOverType (T := T) a b := by
  classical
  let ε : (L[[α]]).Formula β := BoundedFormula.constantsVarsEquiv.symm δ
  letI : (constantsOn α).Structure M := constantsOn.structure a
  rw [mem_typeOfOverType_iff_formula (a := a) (b := b) (φ := ε)]
  rw [← show (Sum.elim (fun x : α ↦ (L.con x : M)) b) = Sum.elim a b from by congr 1]
  rw [show δ = BoundedFormula.constantsVarsEquiv ε from (by simp [ε])]
  exact BoundedFormula.realize_constantsVarsEquiv (φ := ε) (v := b)

/-- A sentence with constants for `α ⊕ β` belongs to the joint type of `(a, b)` exactly when the
corresponding nested sentence belongs to the type of `b` over the type of `a`. -/
lemma mem_typeOf_sum_iff_mem_typeOfOverType {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : α → M) (b : β → M) (σ : (L[[α ⊕ β]]).Sentence) :
    σ ∈ T.typeOf (Sum.elim a b) ↔
      typeOfOverTypeEquiv σ ∈ typeOfOverType (T := T) a b := by
  rw [mem_typeOf]
  exact realize_sum_iff_mem_typeOfOverType a b (Formula.equivSentence.symm σ)

/-- A joint type is determined by the conditional type of the second tuple over the first. The two
pairs of tuples may live in different models. -/
lemma joint_typeOf_eq_of_typeOfOverType_eq {β : Type w'} {M : Type x} {N : Type y}
    [L.Structure M] [Nonempty M] [M ⊨ T] [L.Structure N] [Nonempty N] [N ⊨ T]
    (a : α → M) (b : β → M) (a' : α → N) (b' : β → N)
    (h2 : ∀ τ : ((L[[α]])[[β]]).Sentence,
      τ ∈ typeOfOverType (T := T) a' b' ↔ τ ∈ typeOfOverType (T := T) a b) :
    T.typeOf (Sum.elim a' b') = T.typeOf (Sum.elim a b) := by
  apply SetLike.ext
  intro σ
  rw [mem_typeOf_sum_iff_mem_typeOfOverType (T := T) a' b',
      mem_typeOf_sum_iff_mem_typeOfOverType (T := T) a b]
  exact h2 (typeOfOverTypeEquiv σ)

/-- If the joint type of `(a, b)` is isolated, then the type of `b` over the type of `a` is
isolated. -/
lemma isIsolated_typeOfOverType_of_isIsolated_joint {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : α → M) (b : β → M)
    (h : (T.typeOf (Sum.elim a b)).IsIsolated) :
    (typeOfOverType (T := T) a b).IsIsolated := by
  classical
  let T' : (L[[α]]).Theory := (T.typeOf a : L[[α]].Theory)
  let q : T'.CompleteType β := typeOfOverType (T := T) a b
  rcases h with ⟨Φ, hΦisol⟩
  let ψ : (L[[α]]).Formula β := BoundedFormula.constantsVarsEquiv.symm Φ
  rw [isIsolated_iff_typesWith_eq_singleton]
  refine ⟨ψ, ?_⟩
  rw [singleton_eq_typesWith_iff]
  constructor
  · -- Membership: `Formula.equivSentence ψ ∈ q`.
    change Formula.equivSentence ψ ∈ q
    letI : (constantsOn α).Structure M := constantsOn.structure a
    have hΦab : Φ.Realize (Sum.elim a b) :=
      (CompleteType.formula_mem_typeOf).mp hΦisol.1
    have hψb : ψ.Realize b := by
      change BoundedFormula.Realize ψ b default
      rw [← BoundedFormula.realize_constantsVarsEquiv (φ := ψ) (v := b)]
      rw [show (Sum.elim (fun x : α ↦ (L.con x : M)) b) = Sum.elim a b from by congr 1]
      simpa [ψ, Formula.Realize] using hΦab
    exact (mem_typeOfOverType_iff_formula a b ψ).mpr hψb
  · -- Isolation: for `χ ∈ q`, the pushed theory entails `ψ → χ`.
    intro χ hχq
    rw [models_sentence_iff]
    intro N
    rw [Sentence.realize_imp]
    intro hψN
    letI : (L[[α]]).Structure N := ((L[[α]]).lhomWithConstants β).reduct N
    haveI : ((L[[α]]).lhomWithConstants β).IsExpansionOn N :=
      LHom.isExpansionOn_reduct ((L[[α]]).lhomWithConstants β) N
    letI : L.Structure N := (L.lhomWithConstants α).reduct N
    haveI : (L.lhomWithConstants α).IsExpansionOn N :=
      LHom.isExpansionOn_reduct (L.lhomWithConstants α) N
    haveI : N ⊨ T' := (LHom.onTheory_model ((L[[α]]).lhomWithConstants β) T').1 inferInstance
    haveI : N ⊨ T := by
      have hTα : N ⊨ (L.lhomWithConstants α).onTheory T :=
        (inferInstance : N ⊨ T').mono (CompleteType.subset (T.typeOf a))
      exact (LHom.onTheory_model (L.lhomWithConstants α) T).1 hTα
    let u : α → N := fun x ↦ (L.con x : N)
    let w : β → N := fun y ↦ ((L[[α]]).con y : N)
    have hψw : ψ.Realize w := by
      simpa [w] using (Formula.realize_equivSentence N ψ).1 hψN
    have hΦuw : Φ.Realize (Sum.elim u w) := by
      simpa [ψ, u, Formula.Realize] using
        (BoundedFormula.realize_constantsVarsEquiv (φ := ψ) (v := w)).2 hψw
    have hpuw : T.typeOf (Sum.elim u w) = T.typeOf (Sum.elim a b) :=
      hΦisol.2 (T.typeOf (Sum.elim u w))
        ((CompleteType.formula_mem_typeOf).mpr hΦuw)
    letI : (constantsOn α).Structure M := constantsOn.structure a
    have hχb : (Formula.equivSentence.symm χ).Realize b := by
      exact (mem_typeOfOverType_iff_formula a b (Formula.equivSentence.symm χ)).mp
        (by simpa using hχq)
    let χ' : L.Formula (α ⊕ β) := BoundedFormula.constantsVarsEquiv (Formula.equivSentence.symm χ)
    have hχ'b : χ'.Realize (Sum.elim a b) := by
      rw [show Sum.elim a b = Sum.elim (fun x : α ↦ (L.con x : M)) b from by congr 1]
      simpa [χ', Formula.Realize] using
        (BoundedFormula.realize_constantsVarsEquiv (φ := Formula.equivSentence.symm χ) (v := b)).2 hχb
    have hχ'uw : χ'.Realize (Sum.elim u w) :=
      (realize_iff_of_typeOf_eq (T := T) hpuw χ').mpr hχ'b
    have hχw : (Formula.equivSentence.symm χ).Realize w := by
      exact (BoundedFormula.realize_constantsVarsEquiv (φ := Formula.equivSentence.symm χ) (v := w)).1
        (by simpa [χ', u, Formula.Realize] using hχ'uw)
    simpa [w] using (Formula.realize_equivSentence N (Formula.equivSentence.symm χ)).2 hχw

/-- If the marginal type of `a` and the conditional type of `b` over the type of `a` are both
isolated, then the joint type of `(a, b)` is isolated. -/
lemma joint_isIsolated_of_isIsolated_marginal_conditional {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T]
    (a : α → M) (b : β → M)
    (hr : (T.typeOf a).IsIsolated)
    (hq : (typeOfOverType (T := T) a b).IsIsolated) :
    (T.typeOf (Sum.elim a b)).IsIsolated := by
  obtain ⟨φ,hφ⟩ := (T.typeOf a).isIsolated_iff_typesWith_eq_singleton.mp hr
  rw [singleton_eq_typesWith_iff] at hφ
  rcases hφ with ⟨hφa,hpa⟩
  rw [formula_mem_typeOf] at hφa
  obtain ⟨ψ,hψ⟩ := (typeOfOverType a b).isIsolated_iff_typesWith_eq_singleton.mp hq
  rw [singleton_eq_typesWith_iff] at hψ
  rcases hψ with ⟨hψab,hqab⟩
  simp [typeOfOverType] at hψab
  let ψ' : L.Formula (α ⊕ β) :=
    (φ.relabel (Sum.inl : α → α ⊕ β)) ⊓ (BoundedFormula.constantsVarsEquiv ψ)
  rw [isIsolated_iff_typesWith_eq_singleton]
  exists ψ'
  rw [singleton_eq_typesWith_iff]
  refine ⟨?_,?_⟩
  · simp [ψ', Formula.Realize, Formula.relabel]
    refine ⟨by simpa,?_⟩
    · simp [Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv] at hψab
      convert! hψab
  · intro χ hχ
    rw [models_sentence_iff]
    rintro N
    simp
    intro hψN
    haveI : (L.lhomWithConstants (α ⊕ β)).IsExpansionOn ↑N :=
      LHom.isExpansionOn_reduct (L.lhomWithConstants (α ⊕ β)) ↑N
    haveI : N ⊨ T := (LHom.onTheory_model (L.lhomWithConstants (α ⊕ β)) T).1 N.is_model
    simp only [Formula.realize_equivSentence, Formula.realize_inf, Formula.realize_relabel,
      ψ'] at hψN
    let v : α ⊕ β → N := fun i => L.con i
    let a' : α → N := v ∘ Sum.inl
    let b' : β → N := v ∘ Sum.inr
    letI := constantsOn.structure a'
    suffices T.typeOf (Sum.elim a' b') = T.typeOf (Sum.elim a b) by
      simpa [← this, a', b', v] using hχ
    apply joint_typeOf_eq_of_typeOfOverType_eq a b a' b'
    intro σ
    have hma : T.typeOf a' = T.typeOf a := by
      have hisol : (T.typeOf a).IsolatedBy φ := by
        sorry
      refine typeOf_eq_of_isolating_witness φ hisol ?_
      convert hψN.1
    have hψab : Formula.equivSentence ψ ∈ typeOfOverType (T := T) a' b' := by
      simp [mem_typeOfOverType_iff_formula]
      rcases hψN with ⟨_,hψN⟩
      simp [Formula.Realize] at hψN
      rw [Formula.Realize, ←BoundedFormula.realize_constantsVarsEquiv]
      convert hψN with i
      cases i <;> rfl
    constructor
    · intro hσ'
      by_contra hσ
      rw [← not_mem_iff] at hσ
      specialize hqab ∼σ hσ
      rw [← hma] at hqab
      revert hσ'
      change ¬_
      rw [← not_mem_iff]
      apply (typeOfOverType (T := T) a' b').mem_of_mem_of_models_imp hψab hqab
    · intro hσ
      specialize hqab σ hσ
      rw [← hma] at hqab
      refine CompleteType.mem_of_mem_of_models_imp
        (typeOfOverType (T := T) a' b') hψab hqab


/-- A realized joint type is isolated exactly when its marginal type and its conditional type over
the marginal are both isolated. -/
theorem joint_isolated_iff_of_realizedBy_draft {β : Type w'} {M : Type x}
    [L.Structure M] [Nonempty M] [M ⊨ T]
    (p : T.CompleteType (α ⊕ β)) (a : α → M) (b : β → M)
    (hp : p.RealizedBy (Sum.elim a b)) :
    p.IsIsolated ↔
      (T.typeOf a).IsIsolated ∧ (typeOfOverType (T := T) a b).IsIsolated := by
  constructor
  · intro hisol
    have hpis : (T.typeOf (Sum.elim a b)).IsIsolated := hp ▸ hisol
    exact ⟨isIsolated_typeOf_left a b hpis,
      isIsolated_typeOfOverType_of_isIsolated_joint a b hpis⟩
  · intro h
    have hjoint : (T.typeOf (Sum.elim a b)).IsIsolated :=
      joint_isIsolated_of_isIsolated_marginal_conditional a b h.1 h.2
    exact hp.symm ▸ hjoint

end CompleteType

end Theory

end Language

end FirstOrder
