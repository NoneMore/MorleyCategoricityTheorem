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
`U` to be closed under functions.

Since `elementaryPairTheory T` is a first-order theory, `L₀`-elementary substructures and elementary
extensions of an elementary pair are again elementary pairs, on their `U`-part and their ambient
`L`-reduct.

## Main definitions

- `FirstOrder.Language.pairPart`: the `U`-part of a `PairLanguage L`-structure.
- `FirstOrder.Language.IsElementaryPair`: an `L₀`-structure whose `U`-part is the universe of an
  `L`-elementary substructure.
- `FirstOrder.Language.elementaryPairTheory`: the `L₀`-theory of elementary pairs for `T`.

## Main results

- `FirstOrder.Language.BoundedFormula.realize_relativize_of_pairPart` and
  `FirstOrder.Language.Formula.realize_relativize_of_pairPart`: relativization in an arbitrary
  `L₀`-structure whose `U`-part is the universe of an `L`-substructure.
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
- `FirstOrder.Language.ElementarySubstructure.model_elementaryPairTheory` and
  `FirstOrder.Language.ElementaryEmbedding.model_elementaryPairTheory`: an `L₀`-elementary
  substructure or elementary extension of a model of `elementaryPairTheory T` is again a model, so
  by the characterization above it is again an elementary pair; see also
  `FirstOrder.Language.ElementarySubstructure.isElementaryPair`.
-/

universe u v w w'

namespace FirstOrder

namespace Language

/-! ### The `U`-part of a pair structure -/

/-- The underlying set of the `U`-part of a `PairLanguage L`-structure: the elements satisfying the
new unary predicate `U`. -/
def pairPart (L : Language.{u, v}) (M : Type w) [(PairLanguage L).Structure M] : Set M :=
  {x | Structure.RelMap (pairPredicate L) fun _ => x}

/-- Membership in the `U`-part is the interpretation of the predicate `U`. -/
@[simp]
theorem mem_pairPart {L : Language.{u, v}} {M : Type w} [(PairLanguage L).Structure M] {x : M} :
    x ∈ pairPart L M ↔ Structure.RelMap (pairPredicate L) fun _ => x :=
  Iff.rfl

/-- A one-entry vector is the constant function; this bridges `Relations.boundedFormula₁`, which
evaluates relations on one-entry vectors, with `pairPart`, which uses constant functions. -/
private theorem vecCons_eq_const {α : Type*} (a : α) : ![a] = (fun _ => a) := by
  funext i
  exact Matrix.cons_val_fin_one a (fun j => j.elim0) i

/-- An elementary pair: an `L₀`-structure whose `U`-part is the universe of an `L`-elementary
substructure. -/
def IsElementaryPair (L : Language.{u, v}) (M : Type w) [L.Structure M]
    [(PairLanguage L).Structure M] : Prop :=
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
  rw [allFin, Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel]
  exact iff_of_eq (congrArg φ.Realize (funext fun i => by simp))

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
  simp [pairPart, Formula.Realize, vecCons_eq_const]

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
  rw [Formula.Realize, BoundedFormula.realize_rel₁, realize_funTerm]
  simp [pairPart, vecCons_eq_const]

/-- Semantic form of the relativization axiom. -/
theorem realize_relativizationAxiom {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [(PairLanguage L).Structure M] [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M] {n : ℕ}
    (φ : L.Formula (Fin n)) :
    M ⊨ relativizationAxiom φ ↔
      ∀ x : Fin n → M,
        (∀ i, x i ∈ pairPart L M) → (φ.Realize x ↔ Formula.Realize φ.relativize x) := by
  rw [relativizationAxiom, realize_allFin]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_imp, realize_uGuard, Formula.realize_iff, LHom.realize_onFormula]

/-! ### Relativization in an arbitrary pair structure -/

/-- Coercing both components of a `Sum.elim` of subtype-valued tuples agrees with coercing the
`Sum.elim`. -/
private theorem sum_elim_coe {L : Language.{u, v}} {M : Type w} [L.Structure M]
    {S : L.Substructure M} {α : Type*} {n : ℕ} (v : α → S) (xs : Fin n → S) :
    Sum.elim (fun a => (v a : M)) (fun i => (xs i : M)) = Subtype.val ∘ Sum.elim v xs := by
  funext s
  cases s <;> rfl

/-- Coercing a subtype-valued tuple after `Fin.snoc` agrees with `Fin.snoc` of the coerced tuple. -/
private theorem snoc_coe {L : Language.{u, v}} {M : Type w} [L.Structure M] {S : L.Substructure M}
    {n : ℕ} (xs : Fin n → S) (b : S) :
    (fun i => (((Fin.snoc xs b : Fin (n + 1) → S) i) : M)) =
      Fin.snoc (fun i => ((xs i : S) : M)) ((b : S) : M) :=
  Fin.comp_snoc Subtype.val xs b

/-- The guard of the relativized quantifier holds exactly for the entries of the `U`-part. -/
@[simp]
theorem realize_guard_of_pairPart {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [(PairLanguage L).Structure M] {S : L.Substructure M} (hS : ∀ x : M, x ∈ pairPart L M ↔ x ∈ S)
    {α : Type*} {n : ℕ} (v : α → M) (xs : Fin (n + 1) → M) :
    ((pairPredicate L).boundedFormula₁ (Term.var (Sum.inr (Fin.last n)))).Realize v xs ↔
      xs (Fin.last n) ∈ S := by
  rw [BoundedFormula.realize_rel₁]
  simp only [Term.realize_var, Sum.elim_inr, vecCons_eq_const]
  exact hS (xs (Fin.last n))

/-- Relativization in an `L₀`-structure whose `U`-part is an `L`-substructure `S`: `φ^U` holds at a
tuple from `S` exactly when `φ` holds of that tuple in `S`. -/
theorem BoundedFormula.realize_relativize_of_pairPart {L : Language.{u, v}} {M : Type w}
    [L.Structure M] [(PairLanguage L).Structure M]
    [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M] {S : L.Substructure M}
    (hS : ∀ x : M, x ∈ pairPart L M ↔ x ∈ S) :
    ∀ {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) (v : α → S) (xs : Fin n → S),
      φ.relativize.Realize (fun a => (v a : M)) (fun i => (xs i : M)) ↔ φ.Realize v xs := by
  intro α n φ
  induction φ with
  | falsum =>
    intro v xs
    exact Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    show (LHom.sumInl.onTerm t₁).realize
          (Sum.elim (fun a => (v a : M)) (fun i => (xs i : M))) =
        (LHom.sumInl.onTerm t₂).realize
          (Sum.elim (fun a => (v a : M)) (fun i => (xs i : M))) ↔
        t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
    simp only [sum_elim_coe, LHom.realize_onTerm, realize_term_substructure,
      Subtype.coe_injective.eq_iff]
  | rel R ts =>
    intro v xs
    show Structure.RelMap (pairRelationInl R)
        (fun i => (LHom.sumInl.onTerm (ts i)).realize
          (Sum.elim (fun a => (v a : M)) (fun i => (xs i : M)))) ↔
        Structure.RelMap R fun i => (ts i).realize (Sum.elim v xs)
    simp only [sum_elim_coe, LHom.realize_onTerm, realize_term_substructure]
    exact iff_of_eq (LHom.map_onRelation (LHom.sumInl : L →ᴸ PairLanguage L) R _)
  | imp φ ψ ihφ ihψ =>
    intro v xs
    exact imp_congr (ihφ v xs) (ihψ v xs)
  | all φ ih =>
    intro v xs
    rw [relativize_all, BoundedFormula.realize_all, BoundedFormula.realize_all]
    simp only [BoundedFormula.realize_imp, realize_guard_of_pairPart hS, Fin.snoc_last]
    constructor
    · rintro h b
      exact (ih v (Fin.snoc xs b)).mp (by simpa only [snoc_coe] using h ↑b b.2)
    · rintro h a ha
      simpa only [snoc_coe] using (ih v (Fin.snoc xs ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)

/-- Formula-level form of `BoundedFormula.realize_relativize_of_pairPart`: `φ^U` holds at a tuple
from `S` exactly when `φ` holds of that tuple in `S`. -/
theorem Formula.realize_relativize_of_pairPart {L : Language.{u, v}} {M : Type w} [L.Structure M]
    [(PairLanguage L).Structure M] [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M]
    {S : L.Substructure M} (hS : ∀ x : M, x ∈ pairPart L M ↔ x ∈ S) {α : Type*}
    (φ : L.Formula α) {v : α → S} :
    Formula.Realize φ.relativize (fun a => (v a : M)) ↔ φ.Realize v := by
  have h := BoundedFormula.realize_relativize_of_pairPart (S := S) hS (φ := φ) (v := v)
    (xs := (default : Fin 0 → S))
  rw [show (fun i : Fin 0 => ((default : Fin 0 → S) i : M)) = (default : Fin 0 → M) from
    Subsingleton.elim _ _] at h
  exact h

/-! ### The models of the elementary-pair axioms -/

section Models

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [(PairLanguage L).Structure M]
  [(LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M]

/-- The `T`-part of the elementary-pair axioms: a model of `elementaryPairTheory T` is a model
of `T`. -/
theorem Theory.model_of_model_elementaryPairTheory {T : L.Theory}
    [hT : M ⊨ elementaryPairTheory (L := L) T] : M ⊨ T := by
  have h : M ⊨ (LHom.sumInl : L →ᴸ PairLanguage L).onTheory T :=
    Theory.Model.mono hT fun x hx => Or.inl (Or.inl hx)
  exact (LHom.onTheory_model _ T).mp h

/-- The `U`-part of a model of the elementary-pair axioms is closed under the function symbols. -/
theorem funMap_mem_pairPart {T : L.Theory} [M ⊨ elementaryPairTheory (L := L) T] {n : ℕ}
    (f : L.Functions n) {x : Fin n → M} (hx : ∀ i, x i ∈ pairPart L M) :
    Structure.funMap f x ∈ pairPart L M := by
  have hmem : funAxiom (L := L) f ∈ elementaryPairTheory (L := L) T := by
    simp only [elementaryPairTheory, Set.mem_union, Set.mem_ofPred_eq]
    exact Or.inl (Or.inr ⟨n, f, rfl⟩)
  exact (realize_funAxiom f).mp
    (Theory.realize_sentence_of_mem (elementaryPairTheory (L := L) T) hmem) x hx

/-- The `U`-part of a model of the elementary-pair axioms, as an `L`-substructure. -/
def pairPartSubstructure {T : L.Theory} [M ⊨ elementaryPairTheory (L := L) T] :
    L.Substructure M where
  carrier := pairPart L M
  fun_mem := fun f _ hx => funMap_mem_pairPart (T := T) f hx

/-- A model of the elementary-pair axioms satisfies the relativization scheme. -/
theorem realize_relativization {T : L.Theory} [M ⊨ elementaryPairTheory (L := L) T] {n : ℕ}
    (φ : L.Formula (Fin n)) {x : Fin n → M} (hx : ∀ i, x i ∈ pairPart L M) :
    φ.Realize x ↔ Formula.Realize φ.relativize x := by
  have hmem : relativizationAxiom (L := L) φ ∈ elementaryPairTheory (L := L) T := by
    simp only [elementaryPairTheory, Set.mem_union, Set.mem_ofPred_eq]
    exact Or.inr ⟨n, φ, rfl⟩
  exact (realize_relativizationAxiom φ).mp
    (Theory.realize_sentence_of_mem (elementaryPairTheory (L := L) T) hmem) x hx

/-- The `U`-part of a model of the elementary-pair axioms is an elementary `L`-substructure. -/
theorem pairPartSubstructure_isElementary {T : L.Theory}
    [M ⊨ elementaryPairTheory (L := L) T] :
    (pairPartSubstructure (L := L) (M := M) (T := T)).IsElementary := by
  intro n φ x
  have hS : ∀ y : M, y ∈ pairPart L M ↔
      y ∈ pairPartSubstructure (L := L) (M := M) (T := T) := fun _ => Iff.rfl
  have hx : ∀ i, ((x i : pairPartSubstructure (L := L) (M := M) (T := T)) : M) ∈
      pairPart L M := fun i => (x i).2
  refine (realize_relativization (L := L) (M := M) (T := T) φ hx).trans ?_
  exact Formula.realize_relativize_of_pairPart hS φ

/-- **Elementary-pair axiomatization, completeness direction.**  A model of `elementaryPairTheory T`
is an elementary pair. -/
theorem isElementaryPair_of_model {T : L.Theory} [hT : M ⊨ elementaryPairTheory (L := L) T] :
    IsElementaryPair L M :=
  ⟨⟨pairPartSubstructure (L := L) (M := M) (T := T),
      pairPartSubstructure_isElementary (L := L) (M := M) (T := T)⟩, rfl⟩

/-- **Elementary-pair axiomatization, soundness direction.**  An elementary pair whose ambient
reduct is a model of `T` is a model of `elementaryPairTheory T`. -/
theorem model_of_isElementaryPair {T : L.Theory} (hT : M ⊨ T) (h : IsElementaryPair L M) :
    M ⊨ elementaryPairTheory (L := L) T := by
  obtain ⟨S, hS⟩ := h
  rw [Theory.model_iff]
  intro σ hσ
  simp only [elementaryPairTheory, Set.mem_union, Set.mem_ofPred_eq] at hσ
  rcases hσ with (hσ | ⟨n, f, rfl⟩) | ⟨n, φ, rfl⟩
  · have h' : M ⊨ (LHom.sumInl : L →ᴸ PairLanguage L).onTheory T :=
      (LHom.onTheory_model _ T).mpr hT
    exact h'.realize_of_mem σ hσ
  · rw [realize_funAxiom]
    intro x hx
    rw [← hS] at hx ⊢
    exact (S : L.Substructure M).fun_mem f x hx
  · rw [realize_relativizationAxiom]
    intro x hx
    rw [← hS] at hx
    have hElem : φ.Realize x ↔ φ.Realize (fun i => (⟨x i, hx i⟩ : S)) :=
      S.isElementary φ (fun i => (⟨x i, hx i⟩ : S))
    refine hElem.trans ?_
    have hS' : ∀ y : M, y ∈ pairPart L M ↔ y ∈ (S : L.Substructure M) := fun y => by
      rw [← hS]
      exact Iff.rfl
    exact (Formula.realize_relativize_of_pairPart hS' φ
      (v := fun i => (⟨x i, hx i⟩ : S))).symm

/-- The models of `elementaryPairTheory T` are exactly the elementary pairs over models of `T`. -/
theorem isElementaryPair_iff_model {T : L.Theory} (hT : M ⊨ T) :
    IsElementaryPair L M ↔ M ⊨ elementaryPairTheory (L := L) T :=
  ⟨model_of_isElementaryPair hT, fun _ => isElementaryPair_of_model (L := L) (M := M) (T := T)⟩

/-- **Elementary-pair axiomatization.**  The models of `elementaryPairTheory T` are exactly the
structures `(N, U)` in which `N` is a model of `T` and `U` is the universe of an `L`-elementary
substructure of `N`. -/
theorem model_elementaryPairTheory_iff {T : L.Theory} :
    M ⊨ elementaryPairTheory (L := L) T ↔ M ⊨ T ∧ IsElementaryPair L M := by
  refine ⟨fun h => ?_, fun h => model_of_isElementaryPair h.1 h.2⟩
  exact ⟨Theory.model_of_model_elementaryPairTheory (T := T) (hT := h),
    isElementaryPair_of_model (L := L) (M := M) (T := T) (hT := h)⟩

end Models

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
    letI : L.Structure S := (LHom.sumInl : L →ᴸ PairLanguage L).reduct S
    IsElementaryPair L S :=
  -- the `letI` is needed: `S` only carries the `L₀`-structure induced from `M`
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
