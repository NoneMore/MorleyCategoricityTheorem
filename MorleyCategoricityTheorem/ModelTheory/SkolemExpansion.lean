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
* the expansion adds at most `|L| + ℵ₀` symbols (`card_skolemExpansion_le`);
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
- `FirstOrder.Language.card_functions_skolemExpansion_le` and
  `FirstOrder.Language.card_skolemExpansion_le`: the Skolem expansion has at most `max ℵ₀ L.card`
  function symbols, and at most `max ℵ₀ L.card` symbols in total.
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
  BoundedFormula.relabelEquiv (skolemVarEquiv n)
    ((skolemExpansionLHom L).onBoundedFormula φ.toFormula)

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
  simp only [Formula.Realize, skolemFormula, BoundedFormula.realize_relabelEquiv,
    LHom.realize_onBoundedFormula]
  change Formula.Realize (BoundedFormula.toFormula φ) (v ∘ ⇑(skolemVarEquiv n)) ↔
    φ.Realize default (Fin.snoc (v ∘ Sum.inl) (v (Sum.inr 0)))
  rw [BoundedFormula.realize_toFormula]
  have h1 : (v ∘ ⇑(skolemVarEquiv n)) ∘ Sum.inl = (default : Empty → M) :=
    Subsingleton.elim _ _
  have h2 : (v ∘ ⇑(skolemVarEquiv n)) ∘ Sum.inr = Fin.snoc (v ∘ Sum.inl) (v (Sum.inr 0)) := by
    funext i
    refine Fin.lastCases ?_ ?_ i <;> simp [skolemVarEquiv]
  rw [h1, h2]

/-- Realization of the existential quantification `∃ y, φ(x̄, y)`. -/
theorem realize_skolemEx {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) :
    ((skolemFormula φ).iExs (Fin 1)).Realize x ↔
      ∃ y : M, φ.Realize (default : Empty → M) (Fin.snoc x y) := by
  rw [Formula.realize_iExs]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y 0, by simpa using (realize_skolemFormula φ (Sum.elim x y)).mp hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨fun _ => y, (realize_skolemFormula φ (Sum.elim x fun _ => y)).mpr (by simpa using hy)⟩

/-- Realization of the instance of `φ` at the Skolem term. -/
theorem realize_skolemInstance {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) :
    (skolemInstance φ).Realize x ↔
      φ.Realize (default : Empty → M) (Fin.snoc x (Structure.funMap (skolemFunction φ) x)) := by
  change BoundedFormula.Realize (skolemInstance φ) x default ↔ _
  rw [skolemInstance]
  change BoundedFormula.Realize ((skolemFormula φ).subst (skolemSubst φ)) x default ↔ _
  rw [BoundedFormula.realize_subst]
  change Formula.Realize (skolemFormula φ)
    (fun a : Fin n ⊕ Fin 1 => (skolemSubst φ a).realize x) ↔ _
  rw [realize_skolemFormula]
  have h1 : (fun a : Fin n ⊕ Fin 1 => (skolemSubst φ a).realize x) ∘ Sum.inl = x := by
    funext i
    rfl
  have h2 : (skolemSubst φ (Sum.inr 0)).realize x = Structure.funMap (skolemFunction φ) x :=
    rfl
  rw [h1, h2]

/-- The semantic form of the Skolem axiom: the Skolem function picks a witness whenever one
 exists. -/
theorem realize_skolemAxiom {n : ℕ} (φ : L.BoundedFormula Empty (n + 1)) :
    M ⊨ skolemAxiom φ ↔ ∀ x : Fin n → M,
      (∃ y : M, φ.Realize (default : Empty → M) (Fin.snoc x y)) →
        φ.Realize (default : Empty → M) (Fin.snoc x (Structure.funMap (skolemFunction φ) x)) := by
  rw [skolemAxiom]
  change Formula.Realize
    (BoundedFormula.relabel Sum.inr (((skolemFormula φ).iExs (Fin 1)).imp (skolemInstance φ))).alls
    (default : Empty → M) ↔ _
  rw [BoundedFormula.realize_alls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel_sumInr, Formula.realize_imp, realize_skolemEx,
    realize_skolemInstance]

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
  intro x hx
  have h : Structure.funMap (skolemFunction φ) x =
      Classical.epsilon fun a => φ.Realize (default : Empty → M) (Fin.snoc x a) := rfl
  rw [h]
  exact Classical.epsilon_spec hx

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

/-- The Skolem expansion has at most `|L| + ℵ₀` symbols. -/
theorem card_skolemExpansion_le {L : Language.{u, v}} :
    (skolemExpansion L).card ≤ max ℵ₀ L.card := by
  have hB : Cardinal.mk (Σ n, L.BoundedFormula Empty (n + 1)) ≤ max ℵ₀ L.card :=
    (card_functions_sum_skolem₁ (L := L)).symm.le.trans card_functions_sum_skolem₁_le
  have hcard : (skolemExpansion L).card =
      Cardinal.mk (L.Symbols ⊕ (Σ n, L.BoundedFormula Empty (n + 1))) :=
    Cardinal.mk_congr (skolemSymbolEquiv L)
  rw [hcard, Cardinal.mk_sum, Cardinal.lift_id, Cardinal.lift_id]
  refine (Cardinal.add_le_max _ _).trans (le_of_eq ?_)
  exact le_antisymm
    (max_le (max_le (le_max_right _ _) hB) (le_max_left _ _))
    (max_le (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _)))

/-! ### The Skolem property -/

/-- The Skolem axioms supply the Tarski–Vaught witnesses: the `L`-reduct of any substructure of a
model of the Skolem theory is an elementary `L`-substructure. -/
theorem Substructure.isElementary_reduct {M : Type w} [L.Structure M]
    [(skolemExpansion L).Structure M] [(skolemExpansionLHom L).IsExpansionOn M] {T : L.Theory}
    [M ⊨ skolemTheory T] (S : (skolemExpansion L).Substructure M) :
    ((skolemExpansionLHom L).substructureReduct S).IsElementary := by
  refine Substructure.isElementary_of_exists _ fun n φ x a h => ?_
  refine ⟨⟨Structure.funMap (skolemFunction φ) fun i => (x i : M), S.fun_mem _ _ fun i => (x i).2⟩, ?_⟩
  exact (realize_skolemAxiom φ).mp
    (Theory.realize_sentence_of_mem (skolemTheory T) (skolemAxiom_mem_skolemTheory φ))
    (fun i => (x i : M)) ⟨a, h⟩

end Language

end FirstOrder
