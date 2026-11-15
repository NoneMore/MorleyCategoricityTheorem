/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Skolem

/-!
# Skolem expansions of a language and theory

For a language `L`, Mathlib's `Language.skolem₁` adjoins one function symbol for every `L`-formula
with a distinguished last free variable.  This file turns that syntactic device into a theory:
`skolemTheory T` is `T` together with the *Skolem axioms*, which say that each new function symbol
picks a witness whenever a witness exists.

This is the first step of Skolemization: the Skolem symbols range over `L`-formulas only.  Iterating
the construction would add Skolem symbols for formulas of the expanded language, which is not needed
for the Skolem-hull argument: there only existential `L`-formulas have to be witnessed in the
`L`-reduct.

The main structural results are:

* every nonempty model of `T` expands to a model of `skolemTheory T`, by interpreting each Skolem
  symbol with `Classical.epsilon` (`model_skolemTheory`).  Nonemptiness is needed because the
  expansion introduces constant symbols;
* every model of `skolemTheory T` has an `L`-reduct modelling `T`
  (`Theory.model_of_model_skolemTheory`);
* the expansion has exactly `max ℵ₀ L.card` symbols (`card_skolemExpansion`);
* in a model of the Skolem theory, every substructure of the expansion has an elementary `L`-reduct
  (`Substructure.isElementary_reduct`), the Tarski–Vaught form of the Skolem property.

## Main definitions

- `FirstOrder.Language.skolemExpansion`: the language `L.sum L.skolem₁`.
- `FirstOrder.Language.skolemFunction`, `FirstOrder.Language.skolemTerm`: the Skolem function
  symbol for a formula and the term obtained by applying it to the free variables.
- `FirstOrder.Language.skolemAxiom`: the Skolem axiom for a formula.
- `FirstOrder.Language.skolemTheory`: `T` together with all Skolem axioms.

## Main results

- `FirstOrder.Language.realize_skolemAxiom`: the semantic form of the Skolem axiom.
- `FirstOrder.Language.model_skolemTheory` and
  `FirstOrder.Language.Theory.model_of_model_skolemTheory`: models of `T` expand to models of
  `skolemTheory T`, and models of `skolemTheory T` have `L`-reducts modelling `T`.
- `FirstOrder.Language.card_skolemExpansion`: the Skolem expansion has exactly `max ℵ₀ L.card`
  symbols; `card_functions_skolemExpansion_le` bounds its number of function symbols by the same
  cardinal.
- `FirstOrder.Language.Substructure.isElementary_reduct`: the Skolem axioms give the Tarski–Vaught
  condition for the `L`-reduct of any substructure of an expansion.
-/

universe u v w w'

open Cardinal

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-! ### The Skolem expansion language -/

/-- The one-step Skolem expansion of a language: the language `L` together with a function symbol
for every `L`-formula with one distinguished free variable. -/
abbrev skolemExpansion (L : Language.{u, v}) : Language :=
  L.sum L.skolem₁

/-- The inclusion of a language in its Skolem expansion. -/
abbrev skolemExpansionLHom (L : Language.{u, v}) : L →ᴸ skolemExpansion L :=
  LHom.sumInl

/-- The function symbol of the Skolem expansion associated with a formula. -/
abbrev skolemFunction {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    (skolemExpansion L).Functions n :=
  Sum.inr φ

/-- The Skolem term for `φ`, i.e. the Skolem function symbol applied to the free variables. -/
noncomputable def skolemTerm {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    (skolemExpansion L).Term (Fin n) :=
  Term.func (skolemFunction φ) fun i => Term.var i

/-! ### The Skolem axiom -/

/-- Reindexing `Empty ⊕ Fin (n + 1)` as `Fin n ⊕ Fin 1`, which splits off the witness variable. -/
def skolemVarEquiv (n : ℕ) : Empty ⊕ Fin (n + 1) ≃ Fin n ⊕ Fin 1 :=
  (Equiv.emptySum Empty (Fin (n + 1))).trans (finSumFinEquiv (m := n) (n := 1)).symm

/-- The formula `φ` in the free variables `x₀, …, x_{n-1}` and the witness `y`. -/
noncomputable def skolemFormula {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    (skolemExpansion L).Formula (Fin n ⊕ Fin 1) :=
  ((skolemExpansionLHom L).onBoundedFormula φ).toFormula.relabel (skolemVarEquiv n)

/-- The substitution sending the free variables of `skolemFormula` to the free variables of `φ`
and to the Skolem term. -/
noncomputable def skolemSubst {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    Fin n ⊕ Fin 1 → (skolemExpansion L).Term (Fin n) :=
  Sum.elim (fun i => Term.var i) fun _ => skolemTerm φ

/-- The instance `φ(x₀, …, x_{n-1}, f_φ(x₀, …, x_{n-1}))` of `φ` at the Skolem term. -/
noncomputable def skolemInstance {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    (skolemExpansion L).Formula (Fin n) :=
  (skolemFormula φ).subst (skolemSubst φ)

/-- The Skolem axiom for `φ`: if `φ(x̄, ·)` has a witness, then `f_φ(x̄)` is one. -/
noncomputable def skolemAxiom {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    (skolemExpansion L).Sentence :=
  (BoundedFormula.relabel Sum.inr
    (((skolemFormula φ).iExs (Fin 1)).imp (skolemInstance φ))).alls

/-- The theory `T` together with all Skolem axioms. -/
def skolemTheory (T : L.Theory) : (skolemExpansion L).Theory :=
  (skolemExpansionLHom L).onTheory T ∪
    {σ | ∃ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)), σ = skolemAxiom φ}

/-- The transported theory is contained in the Skolem theory. -/
theorem onTheory_subset_skolemTheory {T : L.Theory} :
    (skolemExpansionLHom L).onTheory T ⊆ skolemTheory T :=
  Set.subset_union_left

/-- Every Skolem axiom is an axiom of the Skolem theory. -/
@[simp]
theorem skolemAxiom_mem_skolemTheory {T : L.Theory} {n : ℕ}
    (φ : L.BoundedFormula Empty (n + 1)) : skolemAxiom φ ∈ skolemTheory T :=
  Set.mem_union_right _ ⟨n, φ, rfl⟩

/-! ### Semantic form of the axioms -/

section Realize

variable {M : Type w} [L.Structure M] [(skolemExpansion L).Structure M]
  [(skolemExpansionLHom L).IsExpansionOn M]

/-- Realization of the formula `φ(x₀, …, x_{n-1}, y)` with the witness variable last. -/
theorem realize_skolemFormula {n : ℕ} (φ : L.BoundedFormula Empty (n + 1))
    (v : Fin n ⊕ Fin 1 → M) :
    (skolemFormula φ).Realize v ↔
      φ.Realize (default : Empty → M) (Fin.snoc (v ∘ Sum.inl) (v (Sum.inr 0))) := by
  have h : (v ∘ ⇑(skolemVarEquiv n)) ∘ Sum.inr = Fin.snoc (v ∘ Sum.inl) (v (Sum.inr 0)) := by
    ext i
    induction i using Fin.lastCases <;> simp [skolemVarEquiv]
  simp only [skolemFormula, Formula.realize_relabel, BoundedFormula.realize_toFormula,
    LHom.realize_onBoundedFormula]
  rw [Subsingleton.elim ((v ∘ ⇑(skolemVarEquiv n)) ∘ Sum.inl) (default : Empty → M), h]

/-- Realization of the existential quantification `∃ y, φ(x̄, y)`. -/
theorem realize_skolemEx {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) :
    ((skolemFormula φ).iExs (Fin 1)).Realize x ↔
      ∃ y : M, φ.Realize (default : Empty → M) (Fin.snoc x y) := by
  simp only [Formula.realize_iExs, realize_skolemFormula, Sum.elim_comp_inl]
  exact ⟨fun ⟨i, hi⟩ => ⟨i 0, hi⟩, fun ⟨y, hy⟩ => ⟨fun _ => y, hy⟩⟩

/-- Realization of the instance of `φ` at the Skolem term. -/
theorem realize_skolemInstance {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) :
    (skolemInstance φ).Realize x ↔
      φ.Realize (default : Empty → M) (Fin.snoc x (Structure.funMap (skolemFunction φ) x)) := by
  simp only [skolemInstance, Formula.Realize, BoundedFormula.realize_subst]
  -- `skolemSubst` sends the witness variable to the Skolem term, so the arguments agree definitionally.
  exact realize_skolemFormula φ fun a => (skolemSubst φ a).realize x

/-- The semantic form of the Skolem axiom: the Skolem function picks a witness whenever one
 exists. -/
theorem realize_skolemAxiom {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    M ⊨ skolemAxiom φ ↔ ∀ x : Fin n → M,
      (∃ y : M, φ.Realize (default : Empty → M) (Fin.snoc x y)) →
        φ.Realize (default : Empty → M) (Fin.snoc x (Structure.funMap (skolemFunction φ) x)) := by
  simp only [skolemAxiom, Sentence.Realize, BoundedFormula.realize_alls,
    Formula.realize_relabel_sumInr, Formula.realize_imp, realize_skolemEx, realize_skolemInstance]
  rfl

end Realize

/-! ### Models of the Skolem theory -/

/-- Every nonempty model of `T` expands to a model of the Skolem theory, using the canonical
choice-function interpretation of the Skolem symbols. -/
theorem model_skolemTheory {M : Type w} [Nonempty M] [L.Structure M] {T : L.Theory}
    (hT : M ⊨ T) : M ⊨ skolemTheory T := by
  refine Theory.Model.union ((LHom.onTheory_model _ T).mpr hT) ?_
  rw [Theory.model_iff]
  rintro σ ⟨n, φ, rfl⟩
  rw [realize_skolemAxiom]
  -- The canonical expansion interprets `f_φ` by `Classical.epsilon`, so the axiom holds by choice.
  exact fun x hx => Classical.epsilon_spec hx

/-- A model of the Skolem theory has an `L`-reduct modelling `T`. -/
theorem Theory.model_of_model_skolemTheory {M : Type w} [L.Structure M]
    [(skolemExpansion L).Structure M] [(skolemExpansionLHom L).IsExpansionOn M] {T : L.Theory}
    (h : M ⊨ skolemTheory T) : M ⊨ T :=
  (LHom.onTheory_model _ T).mp (h.mono (onTheory_subset_skolemTheory (L := L)))

/-! ### Size of the Skolem expansion -/

/-- The Skolem expansion adds at most `max ℵ₀ L.card` many function symbols. -/
theorem card_functions_skolemExpansion_le {L : Language.{u, v}} :
    Cardinal.mk (Σ n, (skolemExpansion L).Functions n) ≤ max ℵ₀ L.card :=
  card_functions_sum_skolem₁_le

/-- The symbols of the Skolem expansion are the symbols of `L` together with the Skolem function
symbols. -/
private def skolemSymbolEquiv (L : Language.{u, v}) :
    (skolemExpansion L).Symbols ≃ L.Symbols ⊕ (Σ n, L.BoundedFormula Empty (n + 1)) :=
  (Equiv.sumCongr
    (Equiv.sigmaSumDistrib (fun n => L.Functions n)
      (fun n => L.BoundedFormula Empty (n + 1)))
    (Equiv.sigmaCongrRight fun n => Equiv.sumEmpty (L.Relations n) Empty)).trans
  ((Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (_root_.Equiv.refl _) (Equiv.sumComm _ _)).trans
      (Equiv.sumAssoc _ _ _).symm))

/-- The Skolem expansion has at most `|L| + ℵ₀` symbols; this is one half of the sharp
`card_skolemExpansion`. -/
theorem card_skolemExpansion_le {L : Language.{u, v}} :
    (skolemExpansion L).card ≤ max ℵ₀ L.card := by
  have hB : Cardinal.mk (Σ n, L.BoundedFormula Empty (n + 1)) ≤ max ℵ₀ L.card :=
    (card_functions_sum_skolem₁ (L := L)).symm.le.trans card_functions_sum_skolem₁_le
  rw [Language.card, Cardinal.mk_congr (skolemSymbolEquiv L), Cardinal.mk_sum, Cardinal.lift_id,
    Cardinal.lift_id]
  exact (Cardinal.add_le_max _ _).trans (max_le (max_le (le_max_right _ _) hB) (le_max_left _ _))

/-- The Skolem expansion has at least `max ℵ₀ L.card` symbols: the symbols of `L` embed into the
expansion, and the Skolem function symbols alone are infinite. -/
theorem le_card_skolemExpansion {L : Language.{u, v}} :
    max ℵ₀ L.card ≤ (skolemExpansion L).card := by
  refine max_le ?_ ?_
  · -- the formulas of `L` give an infinite supply of Skolem function symbols
    simp only [card]
    refine Cardinal.aleph0_le_mk_iff.mpr (Infinite.of_injective
      (fun n : ℕ => (Sum.inl ⟨n, Sum.inr (⊥ : L.BoundedFormula Empty (n + 1))⟩ :
        (L.sum L.skolem₁).Symbols)) ?_)
    intro n m h
    exact congrArg Sigma.fst (Sum.inl_injective h)
  · -- the symbols of `L` are also symbols of the expansion
    simp only [card]
    refine ⟨Function.Embedding.sumMap
      (Function.Embedding.sigmaMap (Function.Embedding.refl ℕ) fun _ => Function.Embedding.inl)
      (Function.Embedding.sigmaMap (Function.Embedding.refl ℕ) fun _ => Function.Embedding.inl)⟩

/-- The Skolem expansion has exactly `|L| + ℵ₀` symbols. -/
theorem card_skolemExpansion {L : Language.{u, v}} :
    (skolemExpansion L).card = max ℵ₀ L.card :=
  le_antisymm card_skolemExpansion_le le_card_skolemExpansion

/-! ### The Skolem property -/

/-- The Skolem axioms supply the Tarski–Vaught witnesses: the `L`-reduct of any substructure of a
model of the Skolem theory is an elementary `L`-substructure. -/
theorem Substructure.isElementary_reduct {M : Type w} [L.Structure M]
    [(skolemExpansion L).Structure M] [(skolemExpansionLHom L).IsExpansionOn M] {T : L.Theory}
    [M ⊨ skolemTheory T] (S : (skolemExpansion L).Substructure M) :
    ((skolemExpansionLHom L).substructureReduct S).IsElementary := by
  refine Substructure.isElementary_of_exists _ fun n φ x a h => ?_
  refine ⟨⟨Structure.funMap (skolemFunction φ) fun i => (x i : M),
    S.fun_mem _ _ fun i => (x i).2⟩, ?_⟩
  exact (realize_skolemAxiom φ).mp
    (Theory.realize_sentence_of_mem (skolemTheory T) (skolemAxiom_mem_skolemTheory φ)) _ ⟨a, h⟩

end Language

end FirstOrder
