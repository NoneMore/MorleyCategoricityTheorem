/-
Copyright (c) 2026 NoneMore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NoneMore
-/
import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Skolem
import MorleyCategoricityTheorem.ModelTheory.Definability
import MorleyCategoricityTheorem.ModelTheory.ElementaryMaps

/-!
# Minimal unary definable sets

An infinite unary definable set `D` in an `L`-structure `M` is *minimal* when every subset of `D`
that is definable with parameters from `M` is finite or cofinite in `D` (blueprint
`def:minimality`).  Strong minimality, the requirement that this hold in every elementary
extension, is built on this local predicate.

The parameters allowed in a defining formula are those of the whole model: `univ.Definable₁` admits
any finite tuple of elements of `M`.  The base over which `D` itself is defined is recorded
separately, for example by `A.Definable₁ L D`, and does not restrict the parameters of the subsets
being tested.  Consequently minimality is a predicate on a model and a set, not on a formula or a
theory, which is why `L` is explicit in `Language.IsMinimal` and implicit where the formula
determines it.

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
- `FirstOrder.Language.Formula.realizationSet₁_definable`: a unary realization set is definable over
  the whole ambient model.
- `FirstOrder.Language.definable₁_iff_exists_fin_realizationSet₁`: a unary set definable over the
  whole model is a realization set with a finite parameter tuple.
- `FirstOrder.Language.Formula.IsStronglyMinimal`: the canonical-target strong minimality predicate.
- `FirstOrder.Language.Formula.IsStronglyMinimal.realizationSet₁_infinite`: a strongly minimal formula
  has an infinite source realization set.
-/

universe u v w w' p

namespace FirstOrder

namespace Language

/-- A set `D` is minimal in `M` when it is infinite, definable with parameters from `M`, and every
definable subset of `D` is finite or cofinite in `D`.

This is blueprint `def:minimality`.  Definability is tested over all of `M`, so the subsets tested
below may use any parameters; the base over which `D` is defined can be recorded separately by
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

/-- A finite set is not minimal. -/
theorem not_isMinimal_of_finite (hD : D.Finite) : ¬ L.IsMinimal D :=
  fun h => h.infinite.not_finite hD

namespace Formula

/-- A one-variable formula with assigned parameters is minimal when its unary realization set is a
minimal set.

The formula determines the language, so `L` is implicit here, unlike in `Language.IsMinimal`. -/
def IsMinimal {L : Language.{u, v}} {M : Type w} [L.Structure M] {β : Type p}
    (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  L.IsMinimal (φ.realizationSet₁ a)

variable {β : Type p} {φ : L.Formula (β ⊕ Fin 1)} {a : β → M}

/-- Minimality of a formula with assigned parameters is minimality of its unary realization set. -/
theorem isMinimal_iff (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) :
    φ.IsMinimal a ↔ L.IsMinimal (φ.realizationSet₁ a) :=
  Iff.rfl

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

variable {β : Type p}

/-- A unary realization set of a formula with assigned parameters is definable with parameters from
the whole ambient model. -/
theorem Formula.realizationSet₁_definable (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) :
    (Set.univ : Set M).Definable₁ L (φ.realizationSet₁ a) := by
  rw [Set.definable₁_iff_exists_realizationSet₁]
  let g : β ⊕ Fin 1 → (Set.univ : Set M) ⊕ Fin 1 :=
    Sum.map (fun i => ⟨a i, Set.mem_univ _⟩) id
  refine ⟨Formula.relabel g φ, ?_⟩
  ext x
  have h : (Sum.elim (fun y : {y : M // y ∈ (Set.univ : Set M)} => y.1)
        (fun _ : Fin 1 => x)) ∘ g = Sum.elim a (fun _ : Fin 1 => x) := by
    funext i
    rcases i with i | j <;> rfl
  simp only [Formula.mem_realizationSet₁, Formula.realize_relabel, h]

/-- A unary set is definable over the whole model exactly when it is the unary realization set of a
one-variable formula with a finite tuple of parameters. -/
theorem definable₁_iff_exists_fin_realizationSet₁ {s : Set M} :
    (Set.univ : Set M).Definable₁ L s ↔
      ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (b : Fin n → M), s = φ.realizationSet₁ b := by
  constructor
  · intro hs
    obtain ⟨A0, -, hA0⟩ := Set.definable_iff_finitely_definable.mp hs
    obtain ⟨θ, hθ⟩ := hA0
    obtain ⟨n, b, φ', hφ'⟩ := Formula.exists_fin_params θ
    refine ⟨n, Formula.relabel (Equiv.sumComm (Fin 1) (Fin n)) φ', fun i => (b i : M), ?_⟩
    ext x
    simp only [Formula.mem_realizationSet₁, Formula.realize_relabel]
    rw [show (Sum.elim (fun i => (b i : M)) (fun _ : Fin 1 => x)) ∘
        Equiv.sumComm (Fin 1) (Fin n) = Sum.elim (fun _ : Fin 1 => x) (fun i => (b i : M)) from by
      funext i
      rcases i with i | j <;> rfl]
    rw [← hφ' (fun _ : Fin 1 => x)]
    have hx : ((fun _ : Fin 1 => x) ∈ ({y : Fin 1 → M | y 0 ∈ s} : Set (Fin 1 → M))) ↔ x ∈ s :=
      Iff.rfl
    rw [← hx, hθ]
    rfl
  · rintro ⟨n, φ, b, rfl⟩
    exact Formula.realizationSet₁_definable φ b

/-- Minimality is reflected along a first-order equivalence: if the image of `D` under `f` is
minimal, then `D` is minimal.

This is the forward transport used to compare a small elementary hull with its copy in the canonical
universe; the converse is not needed here. -/
theorem isMinimal_of_image_equiv {L : Language.{u, v}} {M : Type w} {N : Type w'}
    [L.Structure M] [L.Structure N] (f : M ≃[L] N) {D : Set M}
    (h : L.IsMinimal ((f : M → N) '' D)) : L.IsMinimal D := by
  have hfin_pre : ∀ {T : Set M}, ((f : M → N) '' T).Finite → T.Finite := by
    intro T hT
    have hsub : T ⊆ (f.symm : N → M) '' ((f : M → N) '' T) := by
      intro x hx
      exact ⟨f x, ⟨x, hx, rfl⟩, f.symm_apply_apply x⟩
    exact (hT.image f.symm).subset hsub
  have hdef_image : ∀ {T : Set M}, (Set.univ : Set M).Definable₁ L T →
      (Set.univ : Set N).Definable₁ L ((f : M → N) '' T) := by
    intro T hT
    obtain ⟨m, χ, c, rfl⟩ := definable₁_iff_exists_fin_realizationSet₁.mp hT
    rw [Equiv.image_realizationSet₁ f χ c]
    exact Formula.realizationSet₁_definable χ (f ∘ c)
  have hdef_pre : (Set.univ : Set N).Definable₁ L ((f : M → N) '' D) →
      (Set.univ : Set M).Definable₁ L D := by
    intro hD
    obtain ⟨m, χ, c, hc⟩ := definable₁_iff_exists_fin_realizationSet₁.mp hD
    have hDD : D = (f.symm : N → M) '' ((f : M → N) '' D) := by
      ext x
      constructor
      · intro hx
        exact ⟨f x, ⟨x, hx, rfl⟩, f.symm_apply_apply x⟩
      · rintro ⟨y, ⟨z, hz, rfl⟩, hxy⟩
        rw [← hxy, f.symm_apply_apply]
        exact hz
    rw [hDD, hc, Equiv.image_realizationSet₁ f.symm χ c]
    exact Formula.realizationSet₁_definable χ (f.symm ∘ c)
  refine ⟨?_, hdef_pre h.definable, ?_⟩
  · exact fun hD => h.infinite (hD.image f)
  · intro S hS hSD
    have hS' : (Set.univ : Set N).Definable₁ L ((f : M → N) '' S) := hdef_image hS
    have hSD' : ((f : M → N) '' S) ⊆ ((f : M → N) '' D) := Set.image_mono hSD
    have hdiff : ((f : M → N) '' D) \ ((f : M → N) '' S) = (f : M → N) '' (D \ S) := by
      ext y
      constructor
      · rintro ⟨⟨x, hxD, rfl⟩, hyS⟩
        exact ⟨x, ⟨hxD, fun hxS => hyS ⟨x, hxS, rfl⟩⟩, rfl⟩
      · rintro ⟨x, ⟨hxD, hxS⟩, rfl⟩
        refine ⟨⟨x, hxD, rfl⟩, ?_⟩
        rintro ⟨z, hzS, hzx⟩
        have : z = x := f.injective hzx
        rw [this] at hzS
        exact hxS hzS
    rcases h.finite_or_sdiff_finite hS' hSD' with hfin | hfin
    · exact Or.inl (hfin_pre hfin)
    · exact Or.inr (hfin_pre (by rwa [hdiff] at hfin))

namespace Formula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] {β : Type p}
variable {φ : L.Formula (β ⊕ Fin 1)} {a : β → M}

/-- A one-variable formula with assigned parameters is strongly minimal when its interpretation is
minimal in every elementary extension (blueprint `def:minimality`).

The canonical target universe is `Type (max u v w)`, which contains the source universe and the
symbol universes of `L`; its adequacy is a proof obligation of the arbitrary-target interface, not a
consequence of this definition.  This is a predicate on a formula, its parameters and its model, not
on a theory. -/
def IsStronglyMinimal (φ : L.Formula (β ⊕ Fin 1)) (a : β → M) : Prop :=
  ∀ (N : Type (max u v w)) [L.Structure N] (e : M ↪ₑ[L] N), φ.IsMinimal (e ∘ a)

/-- The source realization set of a strongly minimal formula is infinite, by interpreting in a
universe-lifted copy of the source. -/
theorem IsStronglyMinimal.realizationSet₁_infinite (h : φ.IsStronglyMinimal a) :
    (φ.realizationSet₁ a).Infinite := by
  let N := ULift.{max u v w, w} M
  letI : L.Structure N := Equiv.inducedStructure (Equiv.ulift.symm : M ≃ N)
  let e : M ↪ₑ[L] N :=
    (Equiv.inducedStructureEquiv (Equiv.ulift.symm : M ≃ N)).toElementaryEmbedding
  have h1 : (φ.realizationSet₁ (e ∘ a)).Infinite := (h N e).realizationSet₁_infinite
  have h2 : (φ.realizationSet (e ∘ a)).Infinite :=
    (infinite_realizationSet_fin_one_iff φ (e ∘ a)).mpr h1
  exact (infinite_realizationSet_fin_one_iff φ a).mp
    ((ElementaryEmbedding.infinite_realizations_iff e φ a).mp h2)

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
  let L' : Language.{max u w, v} := L.sum (constantsOn (M ⊕ Fin n))
  letI : (constantsOn (M ⊕ Fin n)).Structure N := constantsOn.structure (Sum.elim e b)
  obtain ⟨P, hP⟩ := exists_small_elementarySubstructure L' (M := N)
  have hmem : ∀ x : M, e x ∈ P := by
    intro x
    have h' := Substructure.constants_mem (S := (P : L'.Substructure N))
      (Sum.inr (Sum.inl x) : L'.Constants)
    change Sum.elim e b (Sum.inl x : M ⊕ Fin n) ∈ (P : Set N) at h'
    simpa using h'
  have hmemb : ∀ i : Fin n, b i ∈ P := by
    intro i
    have h' := Substructure.constants_mem (S := (P : L'.Substructure N))
      (Sum.inr (Sum.inr i) : L'.Constants)
    change Sum.elim e b (Sum.inr i : M ⊕ Fin n) ∈ (P : Set N) at h'
    simpa using h'
  letI hPL' : L'.Structure ↥P := (P : L'.Substructure N).inducedStructure
  letI hPL : L.Structure ↥P := (LHom.sumInl : L →ᴸ L').reduct ↥P
  let ePfun : M → ↥P := fun x => ⟨e x, hmem x⟩
  have hePval : ∀ x : M, (ePfun x : N) = e x := fun x => rfl
  let eP : M ↪ₑ[L] ↥P :=
    { toFun := ePfun
      map_formula' := fun k χ x => by
        have h1 : ((LHom.sumInl : L →ᴸ L').onFormula χ).Realize (ePfun ∘ x) ↔
            χ.Realize (ePfun ∘ x) :=
          (LHom.sumInl : L →ᴸ L').realize_onFormula χ
        have h2 : ((LHom.sumInl : L →ᴸ L').onFormula χ).Realize
              ((P.subtype : ↥P ↪ₑ[L'] N) ∘ (ePfun ∘ x)) ↔
            ((LHom.sumInl : L →ᴸ L').onFormula χ).Realize (ePfun ∘ x) :=
          (P.subtype : ↥P ↪ₑ[L'] N).map_formula _ _
        have h3 : ((LHom.sumInl : L →ᴸ L').onFormula χ).Realize (e ∘ x) ↔
            χ.Realize (e ∘ x) :=
          (LHom.sumInl : L →ᴸ L').realize_onFormula χ
        exact h1.symm.trans (h2.symm.trans (h3.trans (e.map_formula χ x))) }
  let c : Fin n → ↥P := fun i => ⟨b i, hmemb i⟩
  have hcval : ∀ i, (c i : N) = b i := fun i => rfl
  have mem_ψ : ∀ x : ↥P, x ∈ ψ.realizationSet₁ c ↔ (x : N) ∈ ψ.realizationSet₁ b := by
    intro x
    have h1 : x ∈ ψ.realizationSet₁ c ↔
        ((LHom.sumInl : L →ᴸ L').onFormula ψ).Realize (Sum.elim c (fun _ : Fin 1 => x)) := by
      simp only [Formula.mem_realizationSet₁]
      exact ((LHom.sumInl : L →ᴸ L').realize_onFormula ψ).symm
    have h2 : ((LHom.sumInl : L →ᴸ L').onFormula ψ).Realize
          (Sum.elim c (fun _ : Fin 1 => x)) ↔
        ((LHom.sumInl : L →ᴸ L').onFormula ψ).Realize
          ((P.subtype : ↥P ↪ₑ[L'] N) ∘ Sum.elim c (fun _ : Fin 1 => x)) :=
      ((P.subtype : ↥P ↪ₑ[L'] N).map_formula _ _).symm
    have h3 : ((LHom.sumInl : L →ᴸ L').onFormula ψ).Realize
          ((P.subtype : ↥P ↪ₑ[L'] N) ∘ Sum.elim c (fun _ : Fin 1 => x)) ↔
        ((LHom.sumInl : L →ᴸ L').onFormula ψ).Realize
          (Sum.elim b (fun _ : Fin 1 => (x : N))) := by
      have harg : (⇑(P.subtype : ↥P ↪ₑ[L'] N)) ∘ Sum.elim c (fun _ : Fin 1 => x) =
          Sum.elim b (fun _ : Fin 1 => (x : N)) := by
        funext i
        rcases i with i | j <;> rfl
      rw [harg]
    have h4 : ((LHom.sumInl : L →ᴸ L').onFormula ψ).Realize
          (Sum.elim b (fun _ : Fin 1 => (x : N))) ↔ (x : N) ∈ ψ.realizationSet₁ b := by
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula ψ
    exact h1.trans (h2.trans (h3.trans h4))
  have mem_φ : ∀ x : ↥P,
      x ∈ φ.realizationSet₁ (eP ∘ a) ↔ (x : N) ∈ φ.realizationSet₁ (e ∘ a) := by
    intro x
    have h1 : x ∈ φ.realizationSet₁ (eP ∘ a) ↔
        ((LHom.sumInl : L →ᴸ L').onFormula φ).Realize
          (Sum.elim (eP ∘ a) (fun _ : Fin 1 => x)) := by
      simp only [Formula.mem_realizationSet₁]
      exact ((LHom.sumInl : L →ᴸ L').realize_onFormula φ).symm
    have h2 : ((LHom.sumInl : L →ᴸ L').onFormula φ).Realize
          (Sum.elim (eP ∘ a) (fun _ : Fin 1 => x)) ↔
        ((LHom.sumInl : L →ᴸ L').onFormula φ).Realize
          ((P.subtype : ↥P ↪ₑ[L'] N) ∘ Sum.elim (eP ∘ a) (fun _ : Fin 1 => x)) :=
      ((P.subtype : ↥P ↪ₑ[L'] N).map_formula _ _).symm
    have h3 : ((LHom.sumInl : L →ᴸ L').onFormula φ).Realize
          ((P.subtype : ↥P ↪ₑ[L'] N) ∘ Sum.elim (eP ∘ a) (fun _ : Fin 1 => x)) ↔
        ((LHom.sumInl : L →ᴸ L').onFormula φ).Realize
          (Sum.elim (e ∘ a) (fun _ : Fin 1 => (x : N))) := by
      have harg : (⇑(P.subtype : ↥P ↪ₑ[L'] N)) ∘ Sum.elim (eP ∘ a) (fun _ : Fin 1 => x) =
          Sum.elim (e ∘ a) (fun _ : Fin 1 => (x : N)) := by
        funext i
        rcases i with i | j <;> rfl
      rw [harg]
    have h4 : ((LHom.sumInl : L →ᴸ L').onFormula φ).Realize
          (Sum.elim (e ∘ a) (fun _ : Fin 1 => (x : N))) ↔
        (x : N) ∈ φ.realizationSet₁ (e ∘ a) := by
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula φ
    exact h1.trans (h2.trans (h3.trans h4))
  have hsub : ψ.realizationSet₁ c ⊆ φ.realizationSet₁ (eP ∘ a) := by
    intro x hx
    rw [mem_ψ x] at hx
    rw [mem_φ x]
    exact hSD hx
  have hSPinf : (ψ.realizationSet₁ c).Infinite := by
    have hψ' : ((LHom.sumInl : L →ᴸ L').onFormula ψ).realizationSet₁ c =
        ψ.realizationSet₁ c := by
      ext y
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula (M := ↥P) ψ
    rw [← hψ']
    rw [← ElementaryEmbedding.infinite_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L'] N)
      ((LHom.sumInl : L →ᴸ L').onFormula ψ) c]
    have hcomp : (⇑(P.subtype : ↥P ↪ₑ[L'] N)) ∘ c = b := by
      funext i
      rfl
    rw [hcomp]
    have hset : ((LHom.sumInl : L →ᴸ L').onFormula ψ).realizationSet₁ b =
        ψ.realizationSet₁ b := by
      ext y
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula (M := N) ψ
    rw [hset]
    exact hSinf
  have hDPinf : (φ.realizationSet₁ (eP ∘ a)).Infinite := by
    have hφ' : ((LHom.sumInl : L →ᴸ L').onFormula φ).realizationSet₁ (eP ∘ a) =
        φ.realizationSet₁ (eP ∘ a) := by
      ext y
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula (M := ↥P) φ
    rw [← hφ']
    rw [← ElementaryEmbedding.infinite_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L'] N)
      ((LHom.sumInl : L →ᴸ L').onFormula φ) (eP ∘ a)]
    have hcomp : (⇑(P.subtype : ↥P ↪ₑ[L'] N)) ∘ (eP ∘ a) = e ∘ a := rfl
    rw [hcomp]
    have hset : ((LHom.sumInl : L →ᴸ L').onFormula φ).realizationSet₁ (e ∘ a) =
        φ.realizationSet₁ (e ∘ a) := by
      ext y
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula (M := N) φ
    rw [hset]
    exact (Formula.infinite_realizationSet_fin_one_iff φ (e ∘ a)).mp hXd
  let g₁ : β ⊕ Fin 1 → (β ⊕ Fin n) ⊕ Fin 1 := Sum.map Sum.inl id
  let g₂ : Fin n ⊕ Fin 1 → (β ⊕ Fin n) ⊕ Fin 1 := Sum.map Sum.inr id
  let θ : L.Formula ((β ⊕ Fin n) ⊕ Fin 1) := (Formula.relabel g₁ φ) ⊓ (Formula.relabel g₂ ψ).not
  have hθdef : θ = (Formula.relabel g₁ φ) ⊓ (Formula.relabel g₂ ψ).not := rfl
  have hθN : θ.realizationSet₁ (Sum.elim (e ∘ a) b) =
      φ.realizationSet₁ (e ∘ a) \ ψ.realizationSet₁ b := by
    ext y
    simp only [hθdef, Formula.mem_realizationSet₁, Formula.realize_inf, Formula.realize_not,
      Formula.realize_relabel, Set.mem_sdiff]
    have h1 : (Sum.elim (Sum.elim (e ∘ a) b) (fun _ : Fin 1 => y)) ∘ g₁ =
        Sum.elim (e ∘ a) (fun _ : Fin 1 => y) := by
      funext i
      rcases i with i | j <;> rfl
    have h2 : (Sum.elim (Sum.elim (e ∘ a) b) (fun _ : Fin 1 => y)) ∘ g₂ =
        Sum.elim b (fun _ : Fin 1 => y) := by
      funext i
      rcases i with i | j <;> rfl
    rw [h1, h2]
  have hθP : θ.realizationSet₁ (Sum.elim (eP ∘ a) c) =
      φ.realizationSet₁ (eP ∘ a) \ ψ.realizationSet₁ c := by
    ext y
    simp only [hθdef, Formula.mem_realizationSet₁, Formula.realize_inf, Formula.realize_not,
      Formula.realize_relabel, Set.mem_sdiff]
    have h1 : (Sum.elim (Sum.elim (eP ∘ a) c) (fun _ : Fin 1 => y)) ∘ g₁ =
        Sum.elim (eP ∘ a) (fun _ : Fin 1 => y) := by
      funext i
      rcases i with i | j <;> rfl
    have h2 : (Sum.elim (Sum.elim (eP ∘ a) c) (fun _ : Fin 1 => y)) ∘ g₂ =
        Sum.elim c (fun _ : Fin 1 => y) := by
      funext i
      rcases i with i | j <;> rfl
    rw [h1, h2]
  have hDPSinf : (φ.realizationSet₁ (eP ∘ a) \ ψ.realizationSet₁ c).Infinite := by
    rw [← hθP]
    have hθ' : ((LHom.sumInl : L →ᴸ L').onFormula θ).realizationSet₁ (Sum.elim (eP ∘ a) c) =
        θ.realizationSet₁ (Sum.elim (eP ∘ a) c) := by
      ext y
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula (M := ↥P) θ
    rw [← hθ']
    rw [← ElementaryEmbedding.infinite_realizationSet₁_iff (P.subtype : ↥P ↪ₑ[L'] N)
      ((LHom.sumInl : L →ᴸ L').onFormula θ) (Sum.elim (eP ∘ a) c)]
    have hcomp : (⇑(P.subtype : ↥P ↪ₑ[L'] N)) ∘ Sum.elim (eP ∘ a) c =
        Sum.elim (e ∘ a) b := by
      funext i
      rcases i with i | j <;> rfl
    rw [hcomp]
    have hset : ((LHom.sumInl : L →ᴸ L').onFormula θ).realizationSet₁ (Sum.elim (e ∘ a) b) =
        θ.realizationSet₁ (Sum.elim (e ∘ a) b) := by
      ext y
      simp only [Formula.mem_realizationSet₁]
      exact (LHom.sumInl : L →ᴸ L').realize_onFormula θ
    rw [hset, hθN]
    exact hDSinf
  have hnotmin : ¬ L.IsMinimal (φ.realizationSet₁ (eP ∘ a)) := by
    intro hmin
    rcases hmin.finite_or_sdiff_finite (Formula.realizationSet₁_definable ψ c) hsub with
      hfin | hfin
    · exact hSPinf.not_finite hfin
    · exact hDPSinf.not_finite hfin
  let P' : Type (max u v w) := Shrink ↥P
  let σ : ↥P ≃ P' := equivShrink ↥P
  letI : L.Structure P' := Equiv.inducedStructure σ
  have hσe : ↥P ≃[L] P' := Equiv.inducedStructureEquiv σ
  have hstrong := h P' (hσe.toElementaryEmbedding.comp eP)
  have himg : L.IsMinimal ((hσe : ↥P → P') '' φ.realizationSet₁ (eP ∘ a)) := by
    rw [Equiv.image_realizationSet₁ hσe φ (eP ∘ a)]
    exact hstrong
  exact hnotmin (isMinimal_of_image_equiv hσe himg)

end Formula

end Language

end FirstOrder
