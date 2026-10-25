/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.ElementaryMaps

/-!
# The pair language and relativization of formulas

Given an `L`-structure `M` and an `L`-substructure `S ⊆ M`, the *pair language* `L₀ = L ∪ {U}`
adjoins a single unary relation symbol `U` to `L`, and the *pair structure* `(M, S)` interprets `U`
as `S`.  Relativizing an `L`-formula `φ` to `U` gives an `L₀`-formula `φ^U` whose quantifiers all
range over `U`.

On the pair structure, `φ^U` holds of a tuple from `S` exactly when `φ` holds of that tuple in `S`.
Relativization therefore only requires `S` to be an `L`-substructure.  For an embedding
`f : M ↪[L] N` the pair structure is `(N, range f)`, and `φ^U` holds at `f ∘ a` exactly when `M`
satisfies `φ` at `a`; the induced equivalence `M ≃[L] range f` is the only ingredient, so no
elementarity is needed.

## Main definitions

- `FirstOrder.Language.predicateLanguage`: the language with one unary relation symbol.
- `FirstOrder.Language.PairLanguage`: the pair language `L₀ = L ∪ {U}`.
- `FirstOrder.Language.pairPredicate`: the relation symbol `U`.
- `FirstOrder.Language.predicateStructure`, `FirstOrder.Language.pairStructure`: the structures
  interpreting `U`, obtained by composing the given `L`-structure with `sumStructure`.
- `FirstOrder.Language.BoundedFormula.relativize`: relativization `φ ↦ φ^U`.

## Main results

- `FirstOrder.Language.realize_guard`: the predicate `U` holds of the last bound variable of a
  quantifier body exactly when the corresponding tuple entry lies in `S`.
- `FirstOrder.Language.BoundedFormula.realize_relativize`: `φ^U` holds in the pair structure at a
  tuple from `S` if and only if `φ` holds of that tuple in `S`.
- `FirstOrder.Language.embedding_relativization`: for an embedding `f : M ↪[L] N`, the pair
  structure `(N, range f)` satisfies `φ^U` at `f ∘ a` if and only if `M` satisfies `φ` at `a`.
- `FirstOrder.Language.pair_relativization`: the same statement for an elementary embedding.
-/

set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

universe u v w w'

namespace FirstOrder

namespace Language

/-! ### The pair language -/

/-- The language with a single unary relation symbol and no function symbols. -/
def predicateLanguage : Language.{0, 0} where
  Functions _ := Empty
  Relations n := if n = 1 then PUnit else Empty

/-- The pair language `L₀ = L ∪ {U}`: the language `L` together with one new unary predicate. -/
abbrev PairLanguage (L : Language.{u, v}) : Language.{u, v} := L.sum predicateLanguage

/-- The new unary relation symbol `U` of the pair language. -/
def pairPredicate (L : Language.{u, v}) : (PairLanguage L).Relations 1 :=
  Sum.inr PUnit.unit

/-- An `L`-relation symbol, viewed as a relation symbol of the pair language.  The wrapper keeps
the symbol visible to `rw`, which does not unfold the `Language.sum` projection by itself. -/
def pairRelationInl {L : Language.{u, v}} {l : ℕ} (R : L.Relations l) :
    (PairLanguage L).Relations l :=
  Sum.inl R

/-! ### The pair structure -/

variable {L : Language.{u, v}} {M : Type w} {N : Type w'} [L.Structure M]

/-- The structure on `M` for the one-predicate language, interpreting `U` as the set `S`. -/
def predicateStructure (S : Set M) : predicateLanguage.Structure M where
  funMap {_} f _ := nomatch f
  RelMap {n} _ xs := if h : n = 1 then xs (Fin.cast h.symm 0) ∈ S else False

/-- The pair structure `(M, S)`.  It is the `sumStructure` of the given `L`-structure on `M` and
the predicate structure, written field by field so that both projections compute definitionally:
the `L`-part is the given structure and `U` is interpreted as `S`. -/
def pairStructure (S : L.Substructure M) : (PairLanguage L).Structure M where
  funMap {_} f xs :=
    Sum.casesOn f (fun f => Structure.funMap f xs) fun f => nomatch f
  RelMap {_} R xs :=
    Sum.casesOn R (fun R => Structure.RelMap R xs)
      fun R => (predicateStructure (S : Set M)).RelMap R xs

/-- The `L`-reduct of the pair structure is the given `L`-structure. -/
theorem pairStructure_isExpansionOn_sumInl (S : L.Substructure M) :
    @LHom.IsExpansionOn L (PairLanguage L) (LHom.sumInl : L →ᴸ PairLanguage L) M _
      (pairStructure S) := by
  letI : (PairLanguage L).Structure M := pairStructure S
  exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- The predicate `U` holds in the pair structure exactly of the elements of `S`. -/
@[simp]
theorem pairStructure_RelMap_pairPredicate (S : L.Substructure M) (xs : Fin 1 → M) :
    @Structure.RelMap (PairLanguage L) M (pairStructure S) 1 (pairPredicate L) xs ↔ xs 0 ∈ S := by
  letI : predicateLanguage.Structure M := predicateStructure (S : Set M)
  change (if h : 1 = 1 then xs (Fin.cast h.symm 0) ∈ S else False) ↔ xs 0 ∈ S
  simp

/-- The new predicate `U`, applied to the last bound variable of a quantifier body, holds exactly
when the corresponding entry of the tuple lies in `S`. -/
@[simp]
theorem realize_guard (S : L.Substructure M) {α : Type*} {n : ℕ} (v : α → M)
    (xs : Fin (n + 1) → M) :
    @BoundedFormula.Realize (PairLanguage L) M (pairStructure S) α (n + 1)
        ((pairPredicate L).boundedFormula₁ (Term.var (Sum.inr (Fin.last n)))) v xs ↔
      xs (Fin.last n) ∈ S := by
  letI : (PairLanguage L).Structure M := pairStructure S
  rw [BoundedFormula.realize_rel₁]
  simp [pairStructure_RelMap_pairPredicate]

/-! ### Relativization -/

namespace BoundedFormula

variable {α : Type*}

/-- Relativization of a bounded `L`-formula to the new predicate symbol `U`: every quantifier is
restricted to `U`, while terms and relation symbols stay those of `L`. -/
def relativize {n : ℕ} (φ : L.BoundedFormula α n) : (PairLanguage L).BoundedFormula α n :=
  φ.mapTermRel (fun _ t => (LHom.sumInl : L →ᴸ PairLanguage L).onTerm t)
    (fun _ R => pairRelationInl R)
    fun n ψ => ((pairPredicate L).boundedFormula₁ (Term.var (Sum.inr (Fin.last n)))).imp ψ

@[simp]
theorem relativize_falsum {n : ℕ} :
    (BoundedFormula.falsum : L.BoundedFormula α n).relativize = BoundedFormula.falsum := rfl

@[simp]
theorem relativize_equal {n : ℕ} (t₁ t₂ : L.Term (α ⊕ Fin n)) :
    (BoundedFormula.equal t₁ t₂).relativize =
      BoundedFormula.equal ((LHom.sumInl : L →ᴸ PairLanguage L).onTerm t₁)
        ((LHom.sumInl : L →ᴸ PairLanguage L).onTerm t₂) := rfl

@[simp]
theorem relativize_rel {n l : ℕ} (R : L.Relations l) (ts : Fin l → L.Term (α ⊕ Fin n)) :
    (BoundedFormula.rel R ts).relativize =
      BoundedFormula.rel (pairRelationInl R)
        fun i => (LHom.sumInl : L →ᴸ PairLanguage L).onTerm (ts i) := rfl

@[simp]
theorem relativize_imp {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    (φ.imp ψ).relativize = φ.relativize.imp ψ.relativize := rfl

@[simp]
theorem relativize_all {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    (BoundedFormula.all φ).relativize =
      BoundedFormula.all
        (((pairPredicate L).boundedFormula₁ (Term.var (Sum.inr (Fin.last n)))).imp φ.relativize) :=
  rfl

/-- Relativization to `U` computes the truth of the original formula in the substructure `S`. -/
theorem realize_relativize {S : L.Substructure M} :
    ∀ {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n) (v : α → S) (xs : Fin n → S),
      @BoundedFormula.Realize (PairLanguage L) M (pairStructure S) α n φ.relativize
          (fun a => (v a : M)) (fun i => (xs i : M)) ↔
        φ.Realize v xs := by
  letI : predicateLanguage.Structure M := predicateStructure (S : Set M)
  letI : (PairLanguage L).Structure M := pairStructure S
  haveI : (LHom.sumInl : L →ᴸ PairLanguage L).IsExpansionOn M :=
    pairStructure_isExpansionOn_sumInl S
  intro α n φ
  induction φ with
  | falsum =>
    intro v xs
    exact Iff.rfl
  | equal t₁ t₂ =>
    intro v xs
    rw [relativize_equal]
    have hv : Sum.elim (fun a => (v a : M)) (fun i => (xs i : M)) =
        Subtype.val ∘ Sum.elim v xs := by
      ext s
      cases s <;> rfl
    show (LHom.sumInl.onTerm t₁).realize
          (Sum.elim (fun a => (v a : M)) (fun i => (xs i : M))) =
        (LHom.sumInl.onTerm t₂).realize
          (Sum.elim (fun a => (v a : M)) (fun i => (xs i : M))) ↔
        t₁.realize (Sum.elim v xs) = t₂.realize (Sum.elim v xs)
    simp only [LHom.realize_onTerm, hv, realize_term_substructure]
    exact Subtype.coe_injective.eq_iff
  | rel R ts =>
    intro v xs
    rw [relativize_rel]
    have hv : Sum.elim (fun a => (v a : M)) (fun i => (xs i : M)) =
        Subtype.val ∘ Sum.elim v xs := by
      ext s
      cases s <;> rfl
    show Structure.RelMap (pairRelationInl R)
        (fun i => (LHom.sumInl.onTerm (ts i)).realize
          (Sum.elim (fun a => (v a : M)) (fun i => (xs i : M)))) ↔
        Structure.RelMap R fun i => (ts i).realize (Sum.elim v xs)
    simp only [LHom.realize_onTerm, hv, realize_term_substructure]
    exact Iff.rfl
  | imp φ ψ ihφ ihψ =>
    intro v xs
    rw [relativize_imp, BoundedFormula.realize_imp, BoundedFormula.realize_imp, ihφ v xs,
      ihψ v xs]
  | all φ ih =>
    intro v xs
    rw [relativize_all, BoundedFormula.realize_all, BoundedFormula.realize_all]
    simp only [BoundedFormula.realize_imp, realize_guard, Fin.snoc_last]
    constructor
    · intro h b
      have hb := h ↑b b.2
      have hcomp : (fun i => (((Fin.snoc xs b : Fin _ → S) i) : M)) =
          Fin.snoc (fun i => ((xs i : S) : M)) ((b : S) : M) := by
        funext i
        refine Fin.lastCases ?_ ?_ i <;> simp
      rw [← hcomp] at hb
      exact (ih v (Fin.snoc xs b)).mp hb
    · intro h a ha
      have h1 := (ih v (Fin.snoc xs ⟨a, ha⟩)).mpr (h ⟨a, ha⟩)
      have hcomp : (fun i => (((Fin.snoc xs (⟨a, ha⟩ : S) : Fin _ → S) i) : M)) =
          Fin.snoc (fun i => ((xs i : S) : M)) a := by
        funext i
        refine Fin.lastCases ?_ ?_ i <;> simp
      rw [hcomp] at h1
      exact h1

end BoundedFormula

/-- Relativization to `U` computes the truth of the original formula in the substructure `S`. -/
theorem Formula.realize_relativize {S : L.Substructure M} {α : Type*} {φ : L.Formula α}
    {v : α → S} :
    letI : (PairLanguage L).Structure M := pairStructure S
    Formula.Realize (φ.relativize) (fun a => (v a : M)) ↔ φ.Realize v := by
  letI : (PairLanguage L).Structure M := pairStructure S
  have h := BoundedFormula.realize_relativize (S := S) (φ := φ) (v := v) (xs := default)
  have hd : (fun i : Fin 0 => ((default : Fin 0 → S) i : M)) = default := by
    funext i
    exact i.elim0
  rw [hd] at h
  exact h

/-! ### Elementary pairs -/

variable [L.Structure N]

/-- Relativization in a pair given by an embedding: the pair structure `(N, range f)` satisfies
`φ^U` at `f ∘ a` exactly when the source structure satisfies `φ` at `a`. -/
theorem embedding_relativization (f : M ↪[L] N) {α : Type*} (φ : L.Formula α) (a : α → M) :
    letI : (PairLanguage L).Structure N := pairStructure f.toHom.range
    Formula.Realize (φ.relativize) (f ∘ a) ↔ φ.Realize a := by
  letI : (PairLanguage L).Structure N := pairStructure f.toHom.range
  have h := Formula.realize_relativize (S := f.toHom.range) (φ := φ) (v := f.equivRange ∘ a)
  have hcoe : (fun x => ((f.equivRange ∘ a) x : N)) = f ∘ a := by
    funext x
    exact Embedding.equivRange_apply f (a x)
  rw [hcoe] at h
  exact h.trans (StrongHomClass.realize_formula (g := f.equivRange) φ (v := a))

/-- Relativization in an elementary pair, the case used by Vaughtian pairs: the pair structure
`(N, range e)` satisfies `φ^U` at `e ∘ a` exactly when `M` satisfies `φ` at `a`. -/
theorem pair_relativization (e : M ↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (a : α → M) :
    letI : (PairLanguage L).Structure N := pairStructure e.toEmbedding.toHom.range
    Formula.Realize (φ.relativize) (e ∘ a) ↔ φ.Realize a :=
  embedding_relativization e.toEmbedding φ a

end Language

end FirstOrder
