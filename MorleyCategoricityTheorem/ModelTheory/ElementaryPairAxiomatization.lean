/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.ElementarySubstructures
import MorleyCategoricityTheorem.ModelTheory.PairLanguage

/-!
# First-order axiomatization of elementary pairs

Given a theory `T` in a language `L`, this file defines a theory `elementaryPairTheory T` in the
pair language `L₀ = L ∪ {U}` whose models are exactly the structures `(N, U)` in which `N ⊨ T`, the
predicate `U` is the universe of an `L`-substructure of `N`, and that substructure is elementary in
`N`.

The theory is the union of three parts:

* the sentences of `T`, transported to `L₀`;
* closure axioms, saying that `U` contains the constants of `L` and is closed under the function
  symbols of `L`;
* the relativization scheme: for every `L`-formula `φ` with free variables `x₁, …, xₙ`,
  `∀ x₁ … xₙ ∈ U, (φ(x̄) ↔ φ^U(x̄))`.

The closure axioms make the `U`-part a substructure; the scheme then makes it elementary.  Neither
part is redundant: relativization leaves atomic formulas unchanged, so the scheme does not force
`U` to be closed under functions.  Both implications are proved by relativizing in the `L₀`-structure
at hand, whose `U`-part is the `L`-substructure `S`:
`FirstOrder.Language.Formula.realize_relativize_of_pairPart`, from `PairLanguage`.

Since `elementaryPairTheory T` is a first-order theory, `L₀`-elementary substructures and elementary
extensions of an elementary pair are again elementary pairs, on their `U`-part and their ambient
`L`-reduct.

## Main definitions

- `FirstOrder.Language.IsElementaryPair`: an `L₀`-structure whose `U`-part is the universe of an
  `L`-elementary substructure of its `L`-reduct.
- `FirstOrder.Language.elementaryPairTheory`: the `L₀`-theory of elementary pairs for `T`.

## Main results

- `FirstOrder.Language.realize_funAxiom`, `FirstOrder.Language.realize_relativizationAxiom`: the
  semantic form of the axioms.
- `FirstOrder.Language.isElementaryPair_of_model`: a model of `elementaryPairTheory T` is an
  elementary pair, and `FirstOrder.Language.Theory.model_of_model_elementaryPairTheory`: its ambient
  reduct is a model of `T`.
- `FirstOrder.Language.model_of_isElementaryPair`: conversely, an elementary pair over a model of
  `T` is a model of `elementaryPairTheory T`, giving
  `FirstOrder.Language.model_elementaryPairTheory_iff`: the models of `elementaryPairTheory T` are
  exactly the structures `(N, U)` with `N ⊨ T` and `U` the universe of an `L`-elementary
  substructure.
- `FirstOrder.Language.pairStructure_model_elementaryPairTheory`: the pair structure `(M, S)` of an
  elementary substructure `S` of a model of `T` is a model of `elementaryPairTheory T`.
- `FirstOrder.Language.ElementarySubstructure.model_elementaryPairTheory` and
  `FirstOrder.Language.ElementaryEmbedding.model_elementaryPairTheory`: an `L₀`-elementary
  substructure or elementary extension of a model of `elementaryPairTheory T` is again a model, so
  by the characterization above it is again an elementary pair; see also
  `FirstOrder.Language.ElementarySubstructure.isElementaryPair`.

`IsElementaryPair` refers to the canonical `L`-reduct of the `L₀`-structure rather than to a
separately given `L`-structure.  In the presence of an expansion hypothesis, the two readings agree
by `LHom.IsExpansionOn.reduct_eq` and `isElementaryPair_iff`.

## TODO

- If multiple downstream uses need the elementary-pair condition independently of a background
  theory, factor the closure and relativization schemes into a theory-independent
  `elementaryPairAxioms L`; keep `elementaryPairTheory T` as their union with the transported
  theory, adding monotonicity lemmas when needed.
- If downstream proofs repeatedly extract the elementary substructure from `IsElementaryPair`,
  provide a canonical `L.ElementarySubstructure` whose carrier is `pairPart L M`. Avoid a parallel
  representation or unnecessary choice until a concrete consumer needs this API.
- Develop transport of elementary pairs along pair-preserving embeddings and equivalences when
  required by downstream results. Coordinate with the existing TODOs in `PairLanguage` rather
  than introducing a bundled pair-map hierarchy prematurely.
-/

universe u v w w'

namespace FirstOrder

namespace Language

/-! ### The `L`-reduct of an `L₀`-structure -/

/-- The reduct of a structure along a language map that is an expansion is the given structure. -/
theorem LHom.IsExpansionOn.reduct_eq {L L' : Language} {ϕ : L →ᴸ L'} {M : Type*}
    [L.Structure M] [L'.Structure M] (h : ϕ.IsExpansionOn M) :
    ϕ.reduct M = (inferInstance : L.Structure M) := by
  apply Structure.ext
  · funext n f xs
    exact h.map_onFunction f xs
  · funext n R xs
    exact h.map_onRelation R xs

/-! ### Elementary pairs -/

/-- An elementary pair: an `L₀`-structure whose `U`-part is the universe of an `L`-elementary
substructure of its `L`-reduct.  Taking the `L`-structure to be the canonical reduct makes this a
property of the `L₀`-structure alone, rather than of an unrelated `L`-structure on the same type. -/
def IsElementaryPair (L : Language.{u, v}) (M : Type w) [(PairLanguage L).Structure M] : Prop :=
  letI : L.Structure M := (LHom.sumInl : L →ᴸ PairLanguage L).reduct M
  ∃ S : L.ElementarySubstructure M, (S : Set M) = pairPart L M

/-! ### Quantifying the free variables of a formula -/

/-- Universally quantify the free variables of an `L`-formula indexed by `Fin n`, producing an
`L`-sentence. -/
noncomputable def allFin {L : Language.{u, v}} {n : ℕ} (φ : L.Formula (Fin n)) : L.Sentence :=
  (φ.relabel (Sum.inr : Fin n → Empty ⊕ Fin n)).iAlls (Fin n)

/-- `allFin φ` holds in `M` if and only if `φ` holds of every tuple. -/
@[simp]
theorem realize_allFin {L : Language.{u, v}} {M : Type w} [L.Structure M] {n : ℕ}
    (φ : L.Formula (Fin n)) : M ⊨ allFin φ ↔ ∀ x : Fin n → M, φ.Realize x := by
  change Formula.Realize (allFin φ) (default : Empty → M) ↔ _
  simp [allFin]

/-! ### The axioms -/

/-- The guard `⋀ i, U(xᵢ)` of the relativization scheme, a formula with free variables `Fin n`. -/
noncomputable def uGuard {L : Language.{u, v}} (n : ℕ) : (PairLanguage L).Formula (Fin n) :=
  Formula.iInf fun i => (pairPredicate L).boundedFormula₁ (Term.var (Sum.inl i))

/-- The guard holds exactly when every entry of the tuple lies in the `U`-part. -/
@[simp]
theorem realize_uGuard {L : Language.{u, v}} {M : Type w} [(PairLanguage L).Structure M] {n : ℕ}
    (x : Fin n → M) : (uGuard (L := L) n).Realize x ↔ ∀ i, x i ∈ pairPart L M := by
  rw [uGuard, Formula.realize_iInf]
  refine forall_congr' fun i => ?_
  simp [pairPart, Formula.Realize, Matrix.vec_single_eq_const]

/-- The `L₀`-term `f(x₁, …, xₙ)` of the closure axiom, for `f` a function symbol of `L`. -/
noncomputable def funTerm {L : Language.{u, v}} {n : ℕ} (f : L.Functions n) :
    (PairLanguage L).Term (Fin n ⊕ Fin 0) :=
  (LHom.sumInl : L →ᴸ PairLanguage L).onTerm (Term.func f fun i => Term.var (Sum.inl i))

/-- The closure axiom for a function symbol `f`: `U` is closed under `f`. -/
noncomputable def funAxiom {L : Language.{u, v}} {n : ℕ} (f : L.Functions n) :
    (PairLanguage L).Sentence :=
  allFin ((uGuard (L := L) n).imp
    ((pairPredicate L).boundedFormula₁ (funTerm (L := L) f)))

/-- The relativization axiom for an `L`-formula `φ`: on tuples from `U`, `φ` and `φ^U` agree. -/
noncomputable def relativizationAxiom {L : Language.{u, v}} {n : ℕ} (φ : L.Formula (Fin n)) :
    (PairLanguage L).Sentence :=
  allFin ((uGuard (L := L) n).imp
    (((LHom.sumInl : L →ᴸ PairLanguage L).onFormula φ).iff φ.relativize))

/-- The `L₀`-theory of elementary pairs for `T`. -/
def elementaryPairTheory {L : Language.{u, v}} (T : L.Theory) : (PairLanguage L).Theory :=
  (LHom.sumInl : L →ᴸ PairLanguage L).onTheory T ∪
    {σ | ∃ (n : ℕ) (f : L.Functions n), σ = funAxiom f} ∪
    {σ | ∃ (n : ℕ) (φ : L.Formula (Fin n)), σ = relativizationAxiom φ}

/-- The closure axioms are axioms of the elementary-pair theory. -/
@[simp]
theorem funAxiom_mem_elementaryPairTheory {L : Language.{u, v}} {T : L.Theory} {n : ℕ}
    (f : L.Functions n) : funAxiom (L := L) f ∈ elementaryPairTheory (L := L) T :=
  Or.inl (Or.inr ⟨n, f, rfl⟩)

/-- The relativization axioms are axioms of the elementary-pair theory. -/
@[simp]
theorem relativizationAxiom_mem_elementaryPairTheory {L : Language.{u, v}} {T : L.Theory} {n : ℕ}
    (φ : L.Formula (Fin n)) :
    relativizationAxiom (L := L) φ ∈ elementaryPairTheory (L := L) T :=
  Or.inr ⟨n, φ, rfl⟩

/-! ### Semantic form of the axioms -/

/-- The term of the closure axiom realizes to the value of the function symbol. -/
@[simp]
theorem realize_funTerm {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [(PairLanguage L).Structure M] [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M] {n : ℕ}
    (f : L.Functions n) {x : Fin n → M} (y : Fin 0 → M) :
    (funTerm (L := L) f).realize (Sum.elim x y) = Structure.funMap f x := by
  rw [funTerm, LHom.realize_onTerm, Term.realize_func]
  simp

/-- Semantic form of the closure axiom. -/
theorem realize_funAxiom {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [(PairLanguage L).Structure M] [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M] {n : ℕ}
    (f : L.Functions n) :
    M ⊨ funAxiom (L := L) f ↔
      ∀ x : Fin n → M, (∀ i, x i ∈ pairPart L M) → Structure.funMap f x ∈ pairPart L M := by
  rw [funAxiom, realize_allFin]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_imp, realize_uGuard]
  refine imp_congr Iff.rfl ?_
  simp [Formula.Realize, BoundedFormula.realize_rel₁, realize_funTerm, pairPart,
    Matrix.vec_single_eq_const]

/-- Semantic form of the relativization axiom. -/
theorem realize_relativizationAxiom {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [(PairLanguage L).Structure M] [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M] {n : ℕ}
    (φ : L.Formula (Fin n)) :
    M ⊨ relativizationAxiom φ ↔
      ∀ x : Fin n → M,
        (∀ i, x i ∈ pairPart L M) → (φ.Realize x ↔ Formula.Realize φ.relativize x) := by
  simp [relativizationAxiom, Formula.realize_iff, LHom.realize_onFormula]

/-! ### The models of the elementary-pair axioms -/

section Models

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [(PairLanguage L).Structure M]
  [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M]

/-- With an expansion hypothesis, `IsElementaryPair` says that the `U`-part is the universe of an
elementary substructure of the given `L`-structure: the `L`-structure used by `IsElementaryPair` is
the canonical reduct, which agrees with the given one by `LHom.IsExpansionOn.reduct_eq`. -/
theorem isElementaryPair_iff :
    IsElementaryPair L M ↔ ∃ S : L.ElementarySubstructure M, (S : Set M) = pairPart L M := by
  have h := LHom.IsExpansionOn.reduct_eq (ϕ := (LHom.sumInl : L →ᴸ PairLanguage L)) (M := M)
    (inferInstance : (LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M)
  rw [IsElementaryPair, h]

/-- The `T`-part of the elementary-pair axioms: a model of `elementaryPairTheory T` is a model
of `T`. -/
theorem Theory.model_of_model_elementaryPairTheory {T : L.Theory}
    [hT : M ⊨ elementaryPairTheory (L := L) T] : M ⊨ T :=
  (LHom.onTheory_model _ T).mp (hT.mono fun _ hx => Or.inl (Or.inl hx))

/-- The `U`-part of a model of the elementary-pair axioms is closed under the function symbols. -/
theorem funMap_mem_pairPart {T : L.Theory} [M ⊨ elementaryPairTheory (L := L) T] {n : ℕ}
    (f : L.Functions n) {x : Fin n → M} (hx : ∀ i, x i ∈ pairPart L M) :
    Structure.funMap f x ∈ pairPart L M :=
  (realize_funAxiom f).mp
    (Theory.realize_sentence_of_mem (elementaryPairTheory (L := L) T) (by simp)) x hx

/-- The `U`-part of a model of the elementary-pair axioms, as an `L`-substructure. -/
def pairPartSubstructure {T : L.Theory} [M ⊨ elementaryPairTheory (L := L) T] :
    L.Substructure M where
  carrier := pairPart L M
  fun_mem := fun f _ hx => funMap_mem_pairPart (T := T) f hx

/-- A model of the elementary-pair axioms satisfies the relativization scheme. -/
theorem realize_relativization {T : L.Theory} [M ⊨ elementaryPairTheory (L := L) T] {n : ℕ}
    (φ : L.Formula (Fin n)) {x : Fin n → M} (hx : ∀ i, x i ∈ pairPart L M) :
    φ.Realize x ↔ Formula.Realize φ.relativize x :=
  (realize_relativizationAxiom φ).mp
    (Theory.realize_sentence_of_mem (elementaryPairTheory (L := L) T) (by simp)) x hx

/-- The `U`-part of a model of the elementary-pair axioms is an elementary `L`-substructure. -/
theorem pairPartSubstructure_isElementary {T : L.Theory}
    [M ⊨ elementaryPairTheory (L := L) T] :
    (pairPartSubstructure (L := L) (M := M) (T := T)).IsElementary := by
  intro n φ x
  refine (realize_relativization (T := T) φ fun i => (x i).2).trans ?_
  exact Formula.realize_relativize_of_pairPart (fun _ => Iff.rfl) φ

/-- **Elementary-pair axiomatization, completeness direction.**  A model of `elementaryPairTheory T`
is an elementary pair. -/
theorem isElementaryPair_of_model {T : L.Theory} [hT : M ⊨ elementaryPairTheory (L := L) T] :
    IsElementaryPair L M :=
  isElementaryPair_iff.mpr
    ⟨⟨pairPartSubstructure, pairPartSubstructure_isElementary (T := T)⟩, rfl⟩

/-- **Elementary-pair axiomatization, soundness direction.**  An elementary pair whose ambient
reduct is a model of `T` is a model of `elementaryPairTheory T`. -/
theorem model_of_isElementaryPair {T : L.Theory} (hT : M ⊨ T) (h : IsElementaryPair L M) :
    M ⊨ elementaryPairTheory (L := L) T := by
  obtain ⟨S, hS⟩ := isElementaryPair_iff.mp h
  unfold elementaryPairTheory
  refine Theory.Model.union (Theory.Model.union ((LHom.onTheory_model _ T).mpr hT) ?_) ?_
  · rw [Theory.model_iff]
    rintro σ ⟨n, f, rfl⟩
    exact (realize_funAxiom f).mpr fun x hx => by
      rw [← hS] at hx ⊢
      exact (S : L.Substructure M).fun_mem f x hx
  · rw [Theory.model_iff]
    rintro σ ⟨n, φ, rfl⟩
    rw [realize_relativizationAxiom]
    intro x hx
    rw [← hS] at hx
    exact (S.isElementary φ (fun i => (⟨x i, hx i⟩ : S))).trans
      ((Formula.realize_relativize_of_pairPart (fun _ => by rw [← hS]; exact Iff.rfl) φ
        (v := fun i => (⟨x i, hx i⟩ : S))).symm)

/-- The models of `elementaryPairTheory T` are exactly the elementary pairs over models of `T`. -/
theorem isElementaryPair_iff_model {T : L.Theory} (hT : M ⊨ T) :
    IsElementaryPair L M ↔ M ⊨ elementaryPairTheory (L := L) T :=
  ⟨model_of_isElementaryPair hT, fun _ => isElementaryPair_of_model (L := L) (M := M) (T := T)⟩

/-- **Elementary-pair axiomatization.**  The models of `elementaryPairTheory T` are exactly the
structures `(N, U)` in which `N` is a model of `T` and `U` is the universe of an `L`-elementary
substructure of `N`. -/
theorem model_elementaryPairTheory_iff {T : L.Theory} :
    M ⊨ elementaryPairTheory (L := L) T ↔ M ⊨ T ∧ IsElementaryPair L M :=
  ⟨fun h => ⟨Theory.model_of_model_elementaryPairTheory (hT := h),
    isElementaryPair_of_model (hT := h)⟩, fun h => model_of_isElementaryPair h.1 h.2⟩

end Models

/-! ### Pair structures -/

section PairStructure

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {T : L.Theory}

/-- **Elementary-pair axiomatization, pair-structure form.**  If `S` is an elementary
`L`-substructure of a model `M` of `T`, then the pair structure `(M, S)` is a model of
`elementaryPairTheory T`. -/
theorem pairStructure_model_elementaryPairTheory (S : L.ElementarySubstructure M) (hT : M ⊨ T) :
    letI : (PairLanguage L).Structure M := pairStructure (S : L.Substructure M)
    M ⊨ elementaryPairTheory (L := L) T :=
  letI : (PairLanguage L).Structure M := pairStructure (S : L.Substructure M)
  letI : (LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M :=
    pairStructure_isExpansionOn_sumInl (S : L.Substructure M)
  model_of_isElementaryPair hT ⟨S, rfl⟩

end PairStructure

/-! ### Preservation under elementary substructures and extensions -/

section Preservation

variable {L : Language.{u, v}} {T : L.Theory}

/-- An `L₀`-elementary substructure of a model of the elementary-pair axioms is again a model. -/
theorem ElementarySubstructure.model_elementaryPairTheory {M : Type w}
    [(PairLanguage L).Structure M] (S : (PairLanguage L).ElementarySubstructure M)
    [h : M ⊨ elementaryPairTheory (L := L) T] : S ⊨ elementaryPairTheory (L := L) T :=
  ⟨fun φ hφ => (ElementarySubstructure.realize_sentence S φ).2 (h.realize_of_mem φ hφ)⟩

/-- **Elementary-pair axiomatization, preservation.**  An `L₀`-elementary substructure of an
elementary pair is again an elementary pair, on its `U`-part and its ambient `L`-reduct. -/
theorem ElementarySubstructure.isElementaryPair {M : Type w} [(PairLanguage L).Structure M]
    (S : (PairLanguage L).ElementarySubstructure M) [M ⊨ elementaryPairTheory (L := L) T] :
    IsElementaryPair L S :=
  letI : L.Structure S := (LHom.sumInl : L →ᴸ PairLanguage L).reduct S
  isElementaryPair_of_model (L := L) (M := S) (T := T)

/-- An `L₀`-elementary extension of a model of the elementary-pair axioms is again a model. -/
theorem ElementaryEmbedding.model_elementaryPairTheory {M : Type w} {N : Type w'}
    [(PairLanguage L).Structure M] [(PairLanguage L).Structure N]
    (e : M ↪ₑ[PairLanguage L] N) [M ⊨ elementaryPairTheory (L := L) T] :
    N ⊨ elementaryPairTheory (L := L) T :=
  (e.theory_model_iff _).mp inferInstance

end Preservation

end Language

end FirstOrder
