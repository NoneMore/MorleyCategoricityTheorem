import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Rank.Cardinal
import Mathlib.ModelTheory.Definability

/-!
Reconnaissance draft for the matroid bridge discussed in `docs/plan/algebraic-closure.md`.

`Scratch/` is outside the Lake library, so `lake build MorleyCategoricityTheorem` and
`lake exe mk_all --check` ignore this file.  Everything here compiles except one deliberate
`sorry`, which marks the finite Steinitz augmentation obligation.

Two corrections that came out of review and are now built into the statements below:

* Finite augmentation is **false** for a general structure: `acl` need not have exchange.  On
  `M = ℕ × ℕ` with the unary function `f (i, j) = (i, 0)`, `A = ∅`, `D = M`, `I = {(0, 0)}` and
  `J = {(0, 1), (0, 2)}` are both `RelIndep` with `|I| < |J|`, but no `e ∈ J \ I` can be added to
  `I`, because `f e = (0, 0)` is algebraic over `I ∪ {e}`.  The augmentation statement therefore
  takes the exchange hypothesis `RelExchange`, which `lem:strongly-minimal-exchange` supplies on a
  strongly minimal `D`.
* The exchange hypothesis itself must be **restricted to `D`**.  Quantifying `c : M` freely makes
  the statement false even for a strongly minimal `D`: on `M = ℕ × Bool` with `f (n, t) = (n,
  false)`, the set `D = {x | f x = x} = ℕ × {false}` is strongly minimal, and with `A = X = ∅`,
  `b = (0, false) ∈ D`, `c = (0, true) ∉ D` we have `b = f c ∈ acl {c} ∩ D` and `b ∉ acl ∅`, yet
  `c ∉ D` and hence `c ∉ relClosure ∅ D {b}`.  `RelExchange` below therefore assumes `X ⊆ D` and
  `c ∈ D`, which is also what the standard exchange lemma gives and what finite augmentation
  needs.  The blueprint text of `lem:strongly-minimal-exchange` omits those hypotheses; the plan
  records that its formal statement must carry them.
* The cardinal-valued dimension must be `Matroid.cRk` (from `Rank/Cardinal.lean`, available for
  `Finitary` matroids through `InvariantCardinalRank`), not the `ℕ∞`-valued `Matroid.eRk`:
  `eRk` collapses all infinite cardinalities, while the blueprint needs `dim_A Y` to be a
  `Cardinal`.

The `Payoff` section shows that `IndepMatroid.ofFinitaryCardAugment` accepts the obligations once
augmentation is available, and records the cardinal-ranked API that then applies.
-/

universe u v w

open FirstOrder FirstOrder.Language

namespace FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- Algebraic over `A`: lies in a finite `A`-definable set.  Duplicates the draft in
`Scratch/AlgebraicClosure.lean`; both are scratch and are removed when the module lands. -/
def IsAlgebraicOver (A : Set M) (b : M) : Prop :=
  ∃ s : Set M, s.Finite ∧ A.Definable₁ L s ∧ b ∈ s

/-- The algebraic closure of a parameter set. -/
def algebraicClosure (A : Set M) : Set M := {b | IsAlgebraicOver (L := L) A b}

theorem subset_algebraicClosure (A : Set M) : A ⊆ algebraicClosure (L := L) A := by
  intro a ha
  exact ⟨{a}, Set.finite_singleton a, Set.Definable.singleton_of_mem L ha, rfl⟩

theorem algebraicClosure_mono {A B : Set M} (hAB : A ⊆ B) :
    algebraicClosure (L := L) A ⊆ algebraicClosure (L := L) B := by
  rintro b ⟨s, hfin, hdef, hb⟩
  exact ⟨s, hfin, Set.Definable.mono hdef hAB, hb⟩

theorem definable₁_iff_definable {A : Set M} {s : Set M} :
    A.Definable₁ L s ↔ A.Definable L {x : Fin 1 → M | x 0 ∈ s} := Iff.rfl

theorem mem_algebraicClosure_iff_exists_finset {A : Set M} {b : M} :
    b ∈ algebraicClosure (L := L) A ↔
      ∃ A₀ : Finset M, (A₀ : Set M) ⊆ A ∧ b ∈ algebraicClosure (L := L) (A₀ : Set M) := by
  constructor
  · rintro ⟨s, hfin, hdef, hb⟩
    obtain ⟨A₀, hA₀, hdef₀⟩ := (Set.definable_iff_finitely_definable).1
      ((definable₁_iff_definable).1 hdef)
    exact ⟨A₀, hA₀, ⟨s, hfin, (definable₁_iff_definable).2 hdef₀, hb⟩⟩
  · rintro ⟨A₀, hA₀, ⟨s, hfin, hdef, hb⟩⟩
    exact ⟨s, hfin, Set.Definable.mono hdef hA₀, hb⟩

variable (A D : Set M)

/-- The relative closure of `def:strongly-minimal-pregeometry`: `cl_A X = acl (A ∪ X) ∩ D`. -/
def relClosure (X : Set M) : Set M := algebraicClosure (L := L) (A ∪ X) ∩ D

/-- Independence in the relative pregeometry: no element lies in the closure of the rest. -/
def RelIndep (X : Set M) : Prop :=
  X ⊆ D ∧ ∀ x ∈ X, x ∉ algebraicClosure (L := L) (A ∪ (X \ {x}))

/-- The exchange hypothesis for the relative closure, in the restricted form the standard exchange
lemma supplies: `X ⊆ D` and the exchanged element `c` lies in `D`.  The unrestricted form is false
(see the counterexample in the file header), and this restricted form still suffices for finite
augmentation because independent sets are subsets of `D`. -/
def RelExchange : Prop :=
  ∀ ⦃X : Set M⦄, X ⊆ D → ∀ ⦃b c : M⦄, c ∈ D →
    b ∈ relClosure (L := L) A D (insert c X) → b ∉ relClosure (L := L) A D X →
      c ∈ relClosure (L := L) A D (insert b X)

theorem relIndep_empty : RelIndep (L := L) A D ∅ := by
  refine ⟨Set.empty_subset _, ?_⟩
  intro x hx
  exact absurd hx (Set.notMem_empty x)

theorem relIndep_subset {X Y : Set M} (hY : RelIndep (L := L) A D Y) (hXY : X ⊆ Y) :
    RelIndep (L := L) A D X := by
  refine ⟨hXY.trans hY.1, ?_⟩
  intro x hx hxcl
  refine hY.2 x (hXY hx) (algebraicClosure_mono (L := L) ?_ hxcl)
  intro y hy
  rcases hy with hy | hy
  · exact Or.inl hy
  · exact Or.inr ⟨hXY hy.1, hy.2⟩

/-- Compactness of independence follows from finite character of `acl`. -/
theorem relIndep_compact {I : Set M}
    (h : ∀ J, J ⊆ I → J.Finite → RelIndep (L := L) A D J) :
    RelIndep (L := L) A D I := by
  refine ⟨fun x hx => (h {x} ?_ (Set.finite_singleton x)).1 (Set.mem_singleton x), ?_⟩
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    simpa [hy] using hx
  · intro x hxI hxcl
    obtain ⟨A₀, hA₀, hxA₀⟩ := (mem_algebraicClosure_iff_exists_finset (L := L)).1 hxcl
    set J : Set M := ((A₀ : Set M) ∩ (I \ {x})) ∪ {x} with hJdef
    have hJfin : J.Finite :=
      (A₀.finite_toSet.subset Set.inter_subset_left).union (Set.finite_singleton x)
    have hJI : J ⊆ I := by
      intro y hy
      rcases hy with hy | hy
      · exact hy.2.1
      · rw [Set.mem_singleton_iff] at hy
        simpa [hy] using hxI
    have hIndep := h J hJI hJfin
    refine hIndep.2 x (by simp [hJdef]) (algebraicClosure_mono (L := L) ?_ hxA₀)
    intro y hy
    rcases hA₀ hy with hyA | hyI
    · exact Or.inl hyA
    · exact Or.inr ⟨Or.inl ⟨hy, hyI⟩, hyI.2⟩

end FirstOrder.Language

namespace TestMatroid

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- The remaining obligation: finite Steinitz augmentation for relative acl-independence, stated
under the exchange hypothesis that makes it true. -/
theorem relIndep_finite_augment (A D : Set M) (hcl : RelExchange (L := L) A D) ⦃I J : Set M⦄
    (hI : RelIndep (L := L) A D I) (hIfin : I.Finite) (hJ : RelIndep (L := L) A D J)
    (hJfin : J.Finite) (hcard : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ RelIndep (L := L) A D (insert e I) := by
  sorry

end TestMatroid

namespace Payoff

open FirstOrder FirstOrder.Language

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]

/-- With exchange (and hence augmentation) supplied, the relative closure is a matroid whose
ground set is `D`, and `ofFinitary` also gives the `Finitary` instance. -/
noncomputable def relMatroid (A D : Set M) (hcl : RelExchange (L := L) A D) : Matroid M :=
  (IndepMatroid.ofFinitaryCardAugment D (RelIndep (L := L) A D)
    (relIndep_empty (L := L) A D) (fun _ _ => relIndep_subset (L := L) A D)
    (TestMatroid.relIndep_finite_augment A D hcl) (fun _ => relIndep_compact (L := L) A D)
    (fun _ hI => hI.1)).matroid

#check @Matroid.Finitary
#check @Matroid.cRk
#check @Matroid.IsBasis'.cardinalMk_eq
#check @Matroid.IsBasis'.cardinalMk_eq_cRk
#check @Matroid.Indep.notMem_closure_iff_of_notMem

end Payoff
