/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Skolem

/-!
# Small elementary substructures of a structure

Downward Löwenheim–Skolem: for a specified family of parameters in a structure `N`, there is an
elementary substructure containing them whose size is bounded by the language and parameter-index
universes.  Mathlib's `exists_small_elementarySubstructure` provides such a substructure with
no parameters; this file adds parameters relative to a fixed language `L`.

The construction is the standard one: adjoin a constant symbol for each parameter, take a small
elementary hull in the expanded language, and pass back to `L` by forgetting the constants.  The
passage back is legitimate because elementarity in a richer language restricts to elementarity in
a poorer one (`LHom.isElementary_substructureReduct`).  Its proof reduces the Tarski–Vaught
condition for the reduct language to the one for the richer language, using
`Substructure.IsElementary.exists_realize`.

## Main definitions

- `FirstOrder.Language.LHom.elementarySubstructureReduct`: the reduct of an elementary substructure
  along a language homomorphism, bundled again as an elementary substructure.
- `FirstOrder.Language.ElementaryEmbedding.codRestrict`: corestriction of an elementary embedding to
  an elementary substructure containing its range.

## Main results

- `FirstOrder.Language.exists_small_elementarySubstructure_containing`: a small elementary
  substructure containing a prescribed family of elements.
- `FirstOrder.Language.ElementaryEmbedding.exists_small_factorization`: an elementary embedding
  `M ↪ₑ[L] N` and a family of parameters in `N` factor through a small elementary
  substructure of `N`.

## TODO

- If a concrete caller needs a bound based on the cardinality of the parameter *image*, rather
  than the universe of its index type, consider a set/cardinality-based wrapper around Mathlib's
  `exists_elementarySubstructure_card_eq`. Keep the current universe-polymorphic `Small` API.
- If the generic Tarski–Vaught, language-reduct, and embedding-corestriction helpers acquire other
  callers, consider moving them to their respective foundational modules or upstreaming them to
  Mathlib; avoid a speculative module split here.
-/

universe u v u' v' w w' p

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

/-! ### The Tarski–Vaught condition -/

/-- An elementary substructure satisfies the Tarski–Vaught condition: a formula with one free
variable that holds of a tuple from the hull and an arbitrary element is already satisfied by some
element of the hull. -/
theorem Substructure.IsElementary.exists_realize {M : Type w} [L.Structure M]
    {S : L.Substructure M} (hS : S.IsElementary)
    {n : ℕ} {φ : L.BoundedFormula Empty (n + 1)} {x : Fin n → S} {a : M}
    (h : φ.Realize default (Fin.snoc (fun i => (x i : M)) a)) :
    ∃ b : S, φ.Realize default (Fin.snoc (fun i => (x i : M)) (b : M)) := by
  let S' : L.ElementarySubstructure M := ⟨S, hS⟩
  -- `Empty`-indexed assignments are unique, so coercing one along `S'.subtype` changes nothing
  have hcoe : (⇑S'.subtype ∘ (default : Empty → ↥S')) = (default : Empty → M) :=
    Subsingleton.elim _ _
  -- `∃ y, φ(x, y)` holds in `M`, hence in the hull, which yields the desired witness
  have hexM : (φ.ex).Realize (⇑S'.subtype ∘ (default : Empty → ↥S')) (⇑S'.subtype ∘ x) := by
    rw [hcoe]
    exact BoundedFormula.realize_ex.mpr ⟨a, h⟩
  obtain ⟨b, hb⟩ :=
    BoundedFormula.realize_ex.mp ((S'.subtype.map_boundedFormula (φ.ex) default x).mp hexM)
  -- and `φ(x, b)` holds in the hull, hence in `M`
  refine ⟨b, ?_⟩
  have hφM : φ.Realize (⇑S'.subtype ∘ (default : Empty → ↥S'))
      (⇑S'.subtype ∘ Fin.snoc x b) :=
    (S'.subtype.map_boundedFormula φ default (Fin.snoc x b)).mpr hb
  rw [Fin.comp_snoc, hcoe] at hφM
  exact hφM

/-! ### Passing to a reduct language -/

/-- The reduct of an elementary substructure to a smaller language is elementary. -/
theorem LHom.isElementary_substructureReduct {L' : Language.{u', v'}} {M : Type w}
    [L.Structure M] [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    {S : L'.ElementarySubstructure M} :
    (φ.substructureReduct (S : L'.Substructure M)).IsElementary := by
  refine Substructure.isElementary_of_exists _ fun n ψ x a h => ?_
  -- the Tarski–Vaught condition in the richer language holds by elementarity of `S`
  obtain ⟨b, hb⟩ := S.isElementary.exists_realize (φ := φ.onBoundedFormula ψ)
    ((φ.realize_onBoundedFormula ψ).mpr h)
  exact ⟨b, (φ.realize_onBoundedFormula ψ).mp hb⟩

/-- The reduct of an elementary substructure along a language homomorphism, bundled again as an
elementary substructure. -/
def LHom.elementarySubstructureReduct {L' : Language.{u', v'}} {M : Type w}
    [L.Structure M] [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (S : L'.ElementarySubstructure M) : L.ElementarySubstructure M where
  toSubstructure := φ.substructureReduct (S : L'.Substructure M)
  isElementary' := φ.isElementary_substructureReduct (S := S)

@[simp]
theorem LHom.coe_elementarySubstructureReduct {L' : Language.{u', v'}} {M : Type w}
    [L.Structure M] [L'.Structure M] (φ : L →ᴸ L') [φ.IsExpansionOn M]
    (S : L'.ElementarySubstructure M) :
    (φ.elementarySubstructureReduct S : Set M) = (S : Set M) :=
  rfl

/-! ### Small elementary substructures containing parameters -/

/-- Corestriction of an elementary embedding to an elementary substructure of the target that
contains its range. -/
def ElementaryEmbedding.codRestrict {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
    (P : L.ElementarySubstructure N) (e : M ↪ₑ[L] N) (h : ∀ x, e x ∈ P) : M ↪ₑ[L] P where
  toFun x := ⟨e x, h x⟩
  map_formula' := by
    intro n ψ x
    exact (P.subtype.map_formula ψ (fun i => ⟨e (x i), h (x i)⟩)).symm.trans
      (e.map_formula ψ x)

@[simp]
theorem ElementaryEmbedding.codRestrict_apply {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] (P : L.ElementarySubstructure N) (e : M ↪ₑ[L] N) {h : ∀ x, e x ∈ P}
    (x : M) : (codRestrict P e h x : N) = e x :=
  rfl

@[simp]
theorem ElementaryEmbedding.codRestrict_apply' {M : Type w} {N : Type w'} [L.Structure M]
    [L.Structure N] (P : L.ElementarySubstructure N) (e : M ↪ₑ[L] N) {h : ∀ x, e x ∈ P}
    (x : M) : codRestrict P e h x = ⟨e x, h x⟩ :=
  rfl

/-- Corestricting an elementary embedding and then including it into the target recovers the
original elementary embedding. -/
@[simp]
theorem ElementaryEmbedding.subtype_comp_codRestrict {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (P : L.ElementarySubstructure N)
    (e : M ↪ₑ[L] N) (h : ∀ x, e x ∈ P) :
    P.subtype.comp (ElementaryEmbedding.codRestrict P e h) = e := by
  ext x
  rfl

/-- A small elementary substructure containing every element of a specified family. -/
theorem exists_small_elementarySubstructure_containing {N : Type w} [L.Structure N]
    {ι : Type p} (b : ι → N) :
    ∃ P : L.ElementarySubstructure N, (∀ i, b i ∈ P) ∧ Small.{max u v p} P := by
  -- adjoin a constant for each parameter
  let L' : Language.{max u p, v} := L.sum (constantsOn ι)
  let : (constantsOn ι).Structure N := constantsOn.structure b
  obtain ⟨S, hS⟩ := exists_small_elementarySubstructure L' (M := N)
  exact ⟨LHom.elementarySubstructureReduct LHom.sumInl S,
    fun i => Substructure.constants_mem (S := (S : L'.Substructure N))
      (c := (Sum.inr i : L'.Constants)), hS⟩

/-- An elementary embedding and a family of parameters in the target factor through a small
elementary substructure of the target. -/
theorem ElementaryEmbedding.exists_small_factorization {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] {ι : Type p} (e : M ↪ₑ[L] N) (b : ι → N) :
    ∃ (P : L.ElementarySubstructure N) (eP : M ↪ₑ[L] P) (c : ι → P),
      (∀ x, (eP x : N) = e x) ∧ (∀ i, (c i : N) = b i) ∧ Small.{max u v w p} P := by
  -- adjoin a constant for every element of `M` (via `e`) and every parameter
  obtain ⟨P, hP, hsmall⟩ :=
    exists_small_elementarySubstructure_containing (L := L) (Sum.elim e b)
  exact ⟨P, ElementaryEmbedding.codRestrict P e fun x => hP (Sum.inl x),
    fun i => ⟨b i, hP (Sum.inr i)⟩, fun _ => rfl, fun _ => rfl, hsmall⟩

/-- Regression: a subtype-indexed parameter family may live in a universe independent of both the
source and target model universes, while factorization still recovers the embedding exactly. -/
example {M : Type w} {N : Type w'} [L.Structure M] [L.Structure N]
    {α : Type p} (A : Set α) (e : M ↪ₑ[L] N) (b : ↥A → N) :
    ∃ (P : L.ElementarySubstructure N) (eP : M ↪ₑ[L] P) (c : ↥A → P),
      P.subtype.comp eP = e ∧ (∀ i, (c i : N) = b i) ∧ Small.{max u v w p} P := by
  obtain ⟨P, eP, c, he, hc, hsmall⟩ := e.exists_small_factorization b
  refine ⟨P, eP, c, ?_, hc, hsmall⟩
  ext x
  exact he x

end Language

end FirstOrder
