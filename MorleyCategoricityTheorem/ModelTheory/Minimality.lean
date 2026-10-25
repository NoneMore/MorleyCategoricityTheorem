/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.ElementaryMaps
import MorleyCategoricityTheorem.ModelTheory.SkolemHull

/-!
# Minimal unary definable sets

An infinite unary definable set `D` in an `L`-structure `M` is *minimal* when every subset of `D`
that is definable with parameters from `M` is finite or cofinite in `D` (blueprint
`def:minimality`).  Strong minimality, the requirement that this hold in every elementary
extension, is built on this local predicate.

The definability condition allows every parameter of the ambient model: `univ.Definable₁` admits any
finite tuple of elements of `M`.  The base over which `D` itself is defined, such as a set `A` with
`A.Definable₁ L D`, is recorded separately and does not restrict the parameters of the subsets being
tested.  Minimality is therefore a property of a set in a model, not of a formula or a theory.

## Main definitions

- `FirstOrder.Language.IsMinimal`: minimality of a set in a structure.
- `FirstOrder.Language.Formula.IsMinimal`: the formula-level wrapper, evaluating a one-variable
  formula at an assigned parameter tuple.

## Main results

- `FirstOrder.Language.isMinimal_iff`: the split form of the definition, testing `D ∩ S` and
  `D \ S` against an arbitrary definable set `S` without requiring `S ⊆ D`.
- `FirstOrder.Language.IsMinimal.finite_or_sdiff_finite`: the defining dichotomy for a definable
  subset.
- `FirstOrder.Language.IsMinimal.sdiff_finite_of_infinite`: an infinite definable subset of a
  minimal set is cofinite in it.
- `FirstOrder.Language.not_isMinimal_of_finite`: a finite set is not minimal.
- `FirstOrder.Language.IsMinimal.not_exists_definable_split`: the split form of minimality: a
  minimal set admits no definable split into two infinite pieces.
- `FirstOrder.Language.not_isMinimal_iff_exists_definable_split`: the failure form of minimality for
  an infinite definable set: not minimal exactly when such a definable split exists.
- `FirstOrder.Language.isMinimal_of_image_equiv`: minimality is reflected along a first-order
  equivalence.
- `FirstOrder.Language.Formula.exists_formula_split_of_not_isMinimal`: the formula-level split of a
  non-minimal unary formula into two unary formulas with infinite realization sets.
- `FirstOrder.Language.Formula.isMinimal_congr` and
  `FirstOrder.Language.Formula.isStronglyMinimal_congr`: minimality and strong minimality depend only
  on the unary set defined, not on the defining presentation, even across parameter universes.
- `FirstOrder.Language.Formula.IsStronglyMinimal.realizationSet₁_infinite`: a strongly minimal formula
  has an infinite source realization set.
- `FirstOrder.Language.Formula.IsStronglyMinimal.isMinimal`: strong minimality implies minimality
  after an elementary embedding into an arbitrary target universe.
- `FirstOrder.Language.Formula.IsStronglyMinimal.isMinimal_source`: strong minimality implies
  minimality in the source model.
- `FirstOrder.Language.Formula.IsStronglyMinimal.comp`: strong minimality is preserved along
  elementary embeddings.
-/

universe u v w w' p

namespace FirstOrder

namespace Language

/-- A set `D` is minimal in `M` when it is infinite, definable with parameters from `M`, and every
definable subset of `D` is finite or cofinite in `D`.

This is blueprint `def:minimality`.  Definability is tested over all of `M`, so the subsets tested
may use any parameters; the base over which `D` is defined can be recorded separately by
`A.Definable₁ L D`.  Minimality is a property of the set in its model, not of a chosen defining
formula. -/
def IsMinimal (L : Language.{u, v}) {M : Type w} [L.Structure M] (D : Set M) : Prop :=
  D.Infinite ∧
    (Set.univ : Set M).Definable₁ L D ∧
    ∀ S : Set M, (Set.univ : Set M).Definable₁ L S → S ⊆ D →
      S.Finite ∨ (D \ S).Finite

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {D : Set M}

/-- Minimality can be tested by splitting `D` along an arbitrary definable set: one of
`D ∩ S` and `D \ S` is finite.  The hypothesis `S ⊆ D` of the definition is not needed here. -/
theorem isMinimal_iff (D : Set M) :
    L.IsMinimal D ↔
      D.Infinite ∧ (Set.univ : Set M).Definable₁ L D ∧
        ∀ S : Set M, (Set.univ : Set M).Definable₁ L S →
          (D ∩ S).Finite ∨ (D \ S).Finite := by
  constructor
  · rintro ⟨hDinf, hDdef, hDichotomy⟩
    refine ⟨hDinf, hDdef, fun S hS => ?_⟩
    simpa using hDichotomy (D ∩ S) (hDdef.inter hS) Set.inter_subset_left
  · rintro ⟨hDinf, hDdef, hSplit⟩
    refine ⟨hDinf, hDdef, fun S hS hSD => ?_⟩
    simpa [Set.inter_eq_right.mpr hSD] using hSplit S hS

/-- A minimal set is infinite. -/
theorem IsMinimal.infinite (hD : L.IsMinimal D) : D.Infinite :=
  hD.1

/-- A minimal set is definable with parameters from the ambient model. -/
theorem IsMinimal.definable (hD : L.IsMinimal D) :
    (Set.univ : Set M).Definable₁ L D :=
  hD.2.1

/-- Every definable subset of a minimal set is finite or cofinite in it. -/
theorem IsMinimal.finite_or_sdiff_finite (hD : L.IsMinimal D) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ D) :
    S.Finite ∨ (D \ S).Finite :=
  hD.2.2 S hS hSD

/-- The split form of the defining dichotomy: for any definable set `S`, the part of `D` inside
`S` and the part of `D` outside `S` are not both infinite. -/
theorem IsMinimal.inter_finite_or_sdiff_finite (hD : L.IsMinimal D) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) :
    (D ∩ S).Finite ∨ (D \ S).Finite :=
  ((isMinimal_iff D).mp hD).2.2 S hS

/-- An infinite definable subset of a minimal set is cofinite in it. -/
theorem IsMinimal.sdiff_finite_of_infinite (hD : L.IsMinimal D) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ D) (hSinf : S.Infinite) :
    (D \ S).Finite :=
  (hD.finite_or_sdiff_finite hS hSD).resolve_left hSinf.not_finite

/-- A minimal set admits no definable split into two infinite pieces. -/
theorem IsMinimal.not_exists_definable_split (hD : L.IsMinimal D) :
    ¬ ∃ S : Set M, (Set.univ : Set M).Definable₁ L S ∧ S ⊆ D ∧
      S.Infinite ∧ (D \ S).Infinite := by
  rintro ⟨S, hS, hSD, hSinf, hDSinf⟩
  exact hSinf ((hD.finite_or_sdiff_finite hS hSD).resolve_right hDSinf)

/-- A finite set is not minimal. -/
theorem not_isMinimal_of_finite (hD : D.Finite) : ¬ L.IsMinimal D :=
  fun h => h.infinite.not_finite hD

/-- Failure form of minimality for an infinite definable set: a definable split with both sides
infinite exists exactly when the set is not minimal.

Infinitude and definability cannot be dropped, because a finite set is never minimal yet admits no
such split. -/
theorem not_isMinimal_iff_exists_definable_split (hinf : D.Infinite)
    (hdef : (Set.univ : Set M).Definable₁ L D) :
    ¬ L.IsMinimal D ↔ ∃ S : Set M, (Set.univ : Set M).Definable₁ L S ∧ S ⊆ D ∧
      S.Infinite ∧ (D \ S).Infinite := by
  simp only [IsMinimal, hinf, hdef, true_and]
  constructor
  · intro h
    push Not at h
    exact h
  · rintro ⟨S, hS, hSD, hSinf, hDSinf⟩ hcon
    exact hSinf ((hcon S hS hSD).resolve_right hDSinf)

namespace Formula

/-- A one-variable formula with assigned parameters is minimal when its unary realization set is a
minimal set. -/
def IsMinimal {L : Language.{u, v}} {M : Type w} [L.Structure M] {β : Type p}
    (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  L.IsMinimal (φ.realizationSet₁ a)

variable {β : Type p} {φ : L.Formula (β ⊕ Fin 1)} {a : β → M}

/-- Minimality of a formula with assigned parameters is minimality of its unary realization set. -/
theorem isMinimal_iff (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) :
    φ.IsMinimal a ↔ L.IsMinimal (φ.realizationSet₁ a) :=
  Iff.rfl

/- The following four lemmas exist so that the set-level API is reachable by dot notation from a
formula-level hypothesis: `φ.IsMinimal a` is definitionally `L.IsMinimal (φ.realizationSet₁ a)`,
and the `Language.IsMinimal` namespace has no `realizationSet₁_*` names. -/
/-- The realization set of a minimal formula with assigned parameters is infinite. -/
theorem IsMinimal.realizationSet₁_infinite (h : φ.IsMinimal a) :
    (φ.realizationSet₁ a).Infinite :=
  h.infinite

/-- The realization set of a minimal formula with assigned parameters is definable with parameters
from the ambient model. -/
theorem IsMinimal.realizationSet₁_definable (h : φ.IsMinimal a) :
    (Set.univ : Set M).Definable₁ L (φ.realizationSet₁ a) :=
  h.definable

/-- Every definable subset of the realization set of a minimal formula is finite or cofinite in
that realization set. -/
theorem IsMinimal.finite_or_sdiff_finite (h : φ.IsMinimal a) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ φ.realizationSet₁ a) :
    S.Finite ∨ (φ.realizationSet₁ a \ S).Finite :=
  Language.IsMinimal.finite_or_sdiff_finite h hS hSD

/-- An infinite definable subset of the realization set of a minimal formula is cofinite in it. -/
theorem IsMinimal.sdiff_finite_of_infinite (h : φ.IsMinimal a) {S : Set M}
    (hS : (Set.univ : Set M).Definable₁ L S) (hSD : S ⊆ φ.realizationSet₁ a)
    (hSinf : S.Infinite) :
    (φ.realizationSet₁ a \ S).Finite :=
  (h.finite_or_sdiff_finite hS hSD).resolve_left hSinf.not_finite

end Formula

/-- Minimality is reflected along a first-order equivalence: if the image of `D` under `f` is
minimal, then `D` is minimal. -/
theorem isMinimal_of_image_equiv {L : Language.{u, v}} {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (f : M ≃[L] N) {D : Set M}
    (h : L.IsMinimal ((f : M → N) '' D)) : L.IsMinimal D := by
  refine ⟨fun hD => h.infinite (hD.image f), (Equiv.definable₁_image_iff f).mp h.definable, ?_⟩
  intro S hS hSD
  rcases h.finite_or_sdiff_finite ((Equiv.definable₁_image_iff f).mpr hS) (Set.image_mono hSD) with
    hfin | hfin
  · exact Or.inl ((Set.finite_image_iff f.injective.injOn).mp hfin)
  · exact Or.inr ((Set.finite_image_iff f.injective.injOn).mp
      (by rwa [← Set.image_sdiff f.injective] at hfin))

namespace Formula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {β : Type p}
variable {φ : L.Formula (β ⊕ Fin 1)} {a : β → M}

/-- A non-minimal unary formula splits, at the formula level, into two unary formulas whose
realization sets are infinite.

This is the split shape consumed by `Theory.IsOmegaStable.false_of_formula_splitting`.  The
parameter type `↥Set.univ` ranges over the whole model, which is exactly the parameter world that
`IsMinimal` tests. -/
theorem exists_formula_split_of_not_isMinimal
    {φ : L.Formula (↥(Set.univ : Set M) ⊕ Fin 1)}
    (hinf : (φ.realizationSet₁ Subtype.val).Infinite)
    (h : ¬ φ.IsMinimal Subtype.val) :
    ∃ ψ : L.Formula (↥(Set.univ : Set M) ⊕ Fin 1),
      (φ.realizationSet₁ Subtype.val ∩ ψ.realizationSet₁ Subtype.val).Infinite ∧
      (φ.realizationSet₁ Subtype.val \ ψ.realizationSet₁ Subtype.val).Infinite := by
  obtain ⟨S, hSdef, hSD, hSinf, hDSinf⟩ :=
    (not_isMinimal_iff_exists_definable_split hinf
      (Formula.realizationSet₁_definable φ Subtype.val)).mp h
  obtain ⟨ψ, hψ⟩ := Set.definable₁_iff_exists_realizationSet₁.mp hSdef
  refine ⟨ψ, ?_, ?_⟩
  · rw [← hψ, Set.inter_eq_right.mpr hSD]
    exact hSinf
  · rw [← hψ]
    exact hDSinf

/-- A one-variable formula with assigned parameters is strongly minimal when its interpretation is
minimal in every elementary extension (blueprint `def:minimality`).

The extension condition is quantified over the canonical universe `Type (max u v w)`;
`IsStronglyMinimal.isMinimal` turns it into minimality of the interpretation after an elementary
embedding into any universe.  Strong minimality concerns a formula, its parameters and its model,
not a theory. -/
def IsStronglyMinimal (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  ∀ (N : Type (max u v w)) [L.Structure N] (e : M ↪ₑ[L] N), φ.IsMinimal (e ∘ a)

/-- The source realization set of a strongly minimal formula is infinite, by interpreting in a
universe-lifted copy of the source. -/
theorem IsStronglyMinimal.realizationSet₁_infinite (h : φ.IsStronglyMinimal a) :
    (φ.realizationSet₁ a).Infinite := by
  let N := ULift.{max u v w, w} M
  let : L.Structure N := Equiv.inducedStructure (Equiv.ulift.symm : M ≃ N)
  let e : M ↪ₑ[L] N :=
    (Equiv.inducedStructureEquiv (Equiv.ulift.symm : M ≃ N)).toElementaryEmbedding
  have h1 : (φ.realizationSet₁ (e ∘ a)).Infinite := (h N e).realizationSet₁_infinite
  have h2 : (φ.realizationSet (e ∘ a)).Infinite :=
    (infinite_realizationSet_fin_one_iff φ (e ∘ a)).mpr h1
  exact (infinite_realizationSet_fin_one_iff φ a).mp
    ((ElementaryEmbedding.infinite_realizations_iff e φ a).mp h2)

/-- Minimality depends only on the unary set, not on the chosen presentation, even when the two
presentations use parameter types in different universes. -/
theorem isMinimal_congr {γ : Type*} {ψ : L.Formula (γ ⊕ Fin 1)} {c : γ → M}
    (h : φ.realizationSet₁ a = ψ.realizationSet₁ c) : φ.IsMinimal a ↔ ψ.IsMinimal c :=
  iff_of_eq (congrArg L.IsMinimal h)

/-- **Arbitrary-target interface of strong minimality.**  A formula that is strongly minimal in the
canonical universe is minimal after any elementary embedding `e : M ↪ₑ[L] N`, whatever the universe
of `N`.

The proof reflects a putative definable subset into a small elementary hull of `N` that contains the
image of `M` and the parameters, transports that hull to the canonical universe, and uses strong
minimality there. -/
theorem IsStronglyMinimal.isMinimal {N : Type w'} [L.Structure N] (e : M ↪ₑ[L] N)
    (h : φ.IsStronglyMinimal a) : φ.IsMinimal (e ∘ a) := by
  classical
  have hsrc : (φ.realizationSet₁ a).Infinite := h.realizationSet₁_infinite
  have hXd : (φ.realizationSet (e ∘ a)).Infinite :=
    (ElementaryEmbedding.infinite_realizations_iff e φ a).mpr
      ((Formula.infinite_realizationSet_fin_one_iff φ a).mpr hsrc)
  refine ⟨(Formula.infinite_realizationSet_fin_one_iff φ (e ∘ a)).mp hXd,
    Formula.realizationSet₁_definable φ (e ∘ a), ?_⟩
  intro S hSdef hSD
  by_contra hcon
  simp only [not_or, Set.not_finite] at hcon
  obtain ⟨hSinf, hDSinf⟩ := hcon
  obtain ⟨n, ψ, b, rfl⟩ := definable₁_iff_exists_fin_realizationSet₁.mp hSdef
  -- A small elementary hull of `N` containing the image of `e` and the parameters of `ψ`.
  obtain ⟨P, eP, c, heP, hc, hP⟩ := e.exists_small_factorization (L := L) b
  have hc' : (Subtype.val : ↥P → N) ∘ c = b := funext hc
  have heP' : (Subtype.val : ↥P → N) ∘ (eP ∘ a) = e ∘ a := funext fun i => heP (a i)
  have hsc : (Subtype.val : ↥P → N) ∘ Sum.elim (eP ∘ a) c = Sum.elim (e ∘ a) b := by
    rw [Sum.comp_elim, heP', hc']
  -- Realization inside the hull agrees with realization in `N`.
  have mem_ψ : ∀ x : ↥P, x ∈ ψ.realizationSet₁ c ↔ (x : N) ∈ ψ.realizationSet₁ b := by
    intro x
    simpa only [hc', ElementarySubstructure.coe_subtype] using
      ElementaryEmbedding.mem_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L] N) ψ c x
  have mem_φ : ∀ x : ↥P,
      x ∈ φ.realizationSet₁ (eP ∘ a) ↔ (x : N) ∈ φ.realizationSet₁ (e ∘ a) := by
    intro x
    simpa only [heP', ElementarySubstructure.coe_subtype] using
      ElementaryEmbedding.mem_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L] N) φ (eP ∘ a) x
  have hsub : ψ.realizationSet₁ c ⊆ φ.realizationSet₁ (eP ∘ a) := by
    intro x hx
    rw [mem_ψ x] at hx
    rw [mem_φ x]
    exact hSD hx
  have hSPinf : (ψ.realizationSet₁ c).Infinite :=
    (ElementaryEmbedding.infinite_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L] N) ψ c).mp
      (by simpa only [ElementarySubstructure.coe_subtype, hc'] using hSinf)
  -- The difference of the two pieces is again a unary realization set, so its infinitude
  -- transports along the hull as well.
  have hDPSinf : (φ.realizationSet₁ (eP ∘ a) \ ψ.realizationSet₁ c).Infinite := by
    have hN : (((Formula.relabel (Sum.map Sum.inl id) φ) ⊓
        (Formula.relabel (Sum.map Sum.inr id) ψ).not).realizationSet₁
        (Sum.elim (e ∘ a) b)).Infinite := by
      simpa only [Formula.realizationSet₁_sdiff] using hDSinf
    have hPinf := (ElementaryEmbedding.infinite_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L] N)
      ((Formula.relabel (Sum.map Sum.inl id) φ) ⊓
        (Formula.relabel (Sum.map Sum.inr id) ψ).not)
      (Sum.elim (eP ∘ a) c)).mp
      (by simpa only [ElementarySubstructure.coe_subtype, hsc] using hN)
    simpa only [Formula.realizationSet₁_sdiff] using hPinf

  have hnotmin : ¬ L.IsMinimal (φ.realizationSet₁ (eP ∘ a)) := by
    intro hmin
    rcases hmin.finite_or_sdiff_finite (Formula.realizationSet₁_definable ψ c) hsub with
      hfin | hfin
    · exact hSPinf.not_finite hfin
    · exact hDPSinf.not_finite hfin
  -- Transport the hull into the canonical universe and apply strong minimality there.
  let P' : Type (max u v w) := Shrink ↥P
  let σ : ↥P ≃ P' := equivShrink ↥P
  let : L.Structure P' := Equiv.inducedStructure σ
  have hσe : ↥P ≃[L] P' := Equiv.inducedStructureEquiv σ
  have himg : L.IsMinimal ((hσe : ↥P → P') '' φ.realizationSet₁ (eP ∘ a)) := by
    rw [Equiv.image_realizationSet₁ hσe φ (eP ∘ a)]
    exact h P' (hσe.toElementaryEmbedding.comp eP)
  exact hnotmin (isMinimal_of_image_equiv hσe himg)

/-- Strong minimality implies minimality in the source model, by applying the arbitrary-target
interface to the identity embedding. -/
theorem IsStronglyMinimal.isMinimal_source (h : φ.IsStronglyMinimal a) : φ.IsMinimal a :=
  h.isMinimal (ElementaryEmbedding.refl L M)

/-- Strong minimality is preserved along elementary embeddings: interpreting a strongly minimal
formula in a target universe with the transported parameters is again strongly minimal. -/
theorem IsStronglyMinimal.comp {N : Type w'} [L.Structure N] (e : M ↪ₑ[L] N)
    (h : φ.IsStronglyMinimal a) : φ.IsStronglyMinimal (e ∘ a) := by
  intro N' _ e'
  exact h.isMinimal (e'.comp e)

/-- Strong minimality depends only on the unary set, not on the chosen presentation, even when the
two presentations use parameter types in different universes. -/
theorem isStronglyMinimal_congr {γ : Type*} {ψ : L.Formula (γ ⊕ Fin 1)} {c : γ → M}
    (h : φ.realizationSet₁ a = ψ.realizationSet₁ c) :
    φ.IsStronglyMinimal a ↔ ψ.IsStronglyMinimal c :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun e =>
    isMinimal_congr (realizationSet₁_congr h e)

/-- A representative application: two source presentations of the same strongly minimal set, with
different parameter types, remain strongly minimal in a target universe `N` of an unrelated universe
level; the defining dichotomy then holds for a definable subset presented with target parameters
`b : γ → N`, which need not lie in the image of `e`. -/
example {N : Type w'} [L.Structure N] (e : M ↪ₑ[L] N) (h : φ.IsStronglyMinimal a)
    {γ : Type*} {ψ : L.Formula (γ ⊕ Fin 1)} {c : γ → M}
    (hpres : φ.realizationSet₁ a = ψ.realizationSet₁ c) (b : γ → N)
    (hsub : ψ.realizationSet₁ b ⊆ ψ.realizationSet₁ (e ∘ c)) :
    (ψ.realizationSet₁ b).Finite ∨ (ψ.realizationSet₁ (e ∘ c) \ ψ.realizationSet₁ b).Finite :=
  (((isStronglyMinimal_congr hpres).mp h).comp e).isMinimal_source.finite_or_sdiff_finite
    (Formula.realizationSet₁_definable ψ b) hsub

/-- Regression test for independent parameter universes: presentation independence applies when the
two parameter index types live at different universe levels, here the subtype presentation
`↥A : Type w` compared with its finite-parameter normalization indexed by `Fin n : Type 0`. -/
example (A : Set M) {φ' : L.Formula (↥A ⊕ Fin 1)} {a' : ↥A → M}
    {n : ℕ} {ψ' : L.Formula (Fin n ⊕ Fin 1)} {c' : Fin n → M}
    (h : φ'.realizationSet₁ a' = ψ'.realizationSet₁ c') {N : Type w'} [L.Structure N]
    (e : M ↪ₑ[L] N) :
    φ'.realizationSet₁ (e ∘ a') = ψ'.realizationSet₁ (e ∘ c') ∧
      (φ'.IsMinimal a' ↔ ψ'.IsMinimal c') ∧
      (φ'.IsStronglyMinimal a' ↔ ψ'.IsStronglyMinimal c') :=
  ⟨realizationSet₁_congr h e, isMinimal_congr h, isStronglyMinimal_congr h⟩

end Formula

end Language

end FirstOrder
