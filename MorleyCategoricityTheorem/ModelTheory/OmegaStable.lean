import Mathlib.Data.Set.Countable
import Mathlib.Logic.Function.Basic
import Mathlib.Topology.Baire.Lemmas
import MorleyCategoricityTheorem.BinaryTree
import MorleyCategoricityTheorem.ModelTheory.IsolatedTypes

/-!
# Omega-stable theories

This file defines omega-stability using complete types over countable parameter sets, and proves
that in an omega-stable theory the isolated types are dense: every nonempty basic open set of
complete types contains an isolated type.  The proof splits a hypothetically isolation-free basic
open set along a binary tree of formulas over the ambient parameter set; the tree only mentions
countably many parameters, and its branches yield uncountably many distinct complete types over
that countable set, contradicting omega-stability.

The binary-tree argument is independent of isolation and is isolated in the theorem
`IsOmegaStable.false_of_formula_splitting`: a property of formulas that holds of a root formula, is
preserved by splitting any formula into a formula and its negation, and implies realizability is
incompatible with omega-stability.  The density theorem is the specialization of this obstruction
to the property of defining a nonempty basic open set with no isolated type.

## Main results

- `CompleteType.exists_isolated_mem_typesWith`: over an omega-stable theory, every nonempty basic
  open set of complete types contains an isolated type.
- `IsOmegaStable.false_of_formula_splitting`: an omega-stable theory admits no formula property
  that can be split indefinitely into contradictory realizable subformulas.

The semantic dictionary relating basic open sets to realization of their defining formulas is
provided by `ModelTheory.Types`.
-/

universe u v w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}}

namespace Theory

variable (T : L.Theory)

/-- A theory is omega-stable if every space of complete positive finite-arity types over a
countable parameter set in a model of the theory is countable. -/
def IsOmegaStable : Prop :=
  ∀ (M : ModelType.{u, v, w} T) (A : Set M), A.Countable →
    ∀ n : ℕ, 1 ≤ n → Countable (L.CompleteTypeOver A (Fin n))

/-- The type `ℕ → Bool` is uncountable, by Cantor's diagonal argument.  This supplies the
inexhaustible family of branches whose distinctness contradicts omega-stability. -/
theorem not_countable_nat_bool : ¬ Countable (ℕ → Bool) := by
  intro h
  letI : Countable (ℕ → Bool) := h
  have h' : Countable (Set ℕ) :=
    Countable.of_equiv _ (Equiv.piCongrRight fun _ ↦ Equiv.propEquivBool.symm)
  obtain ⟨g, hg⟩ := exists_surjective_nat (Set ℕ)
  exact Function.cantor_surjective g hg

section FormulaSplitting

variable {T : L.Theory}

/-- **Binary splitting obstruction.**  If a property `P` of formulas over a parameter set `A` holds
of a root formula `φ`, is preserved by splitting any formula into a formula and its negation, and
only holds of formulas realizable in the fixed model `M`, then `P` is incompatible with
omega-stability.

Indeed, the splitting produces a binary tree of formulas satisfying `P` that uses only countably
many parameters; moving those formulas to the countable parameter set `A₀` of parameters occurring
in the tree yields a binary tree of nonempty basic open sets whose siblings are disjoint.  Choosing
a point in each branch intersection injects the uncountably many branches into the complete types
over `A₀`, contradicting omega-stability.

This is the common core of the arguments that isolated types are dense in an omega-stable theory,
that uncountable definable sets have uncountable definable splits, and that omega-stable theories
have minimal formulas. -/
theorem IsOmegaStable.false_of_formula_splitting
    {M : ModelType.{u, v, w} T} {A : Set M}
    (hT : T.IsOmegaStable.{u, v, w}) (n : ℕ) (hn : 1 ≤ n)
    (P : (L[[A]]).Formula (Fin n) → Prop) (φ : (L[[A]]).Formula (Fin n)) (hφ : P φ)
    (hsplit : ∀ φ, P φ → ∃ ψ, P (φ ⊓ ψ) ∧ P (φ ⊓ ∼ψ))
    (hrealize : ∀ φ, P φ → ∃ v : Fin n → M, φ.Realize v) : False := by
  classical
  -- Recursively split the root formula into a binary tree of formulas satisfying `P`.
  let split (x : {ψ : (L[[A]]).Formula (Fin n) // P ψ}) :
      {ψ : (L[[A]]).Formula (Fin n) // P ψ} × {ψ // P ψ} :=
    let χ := Classical.choose (hsplit x.1 x.2)
    (⟨x.1 ⊓ χ, (Classical.choose_spec (hsplit x.1 x.2)).1⟩,
     ⟨x.1 ⊓ ∼χ, (Classical.choose_spec (hsplit x.1 x.2)).2⟩)
  let tf : BinaryTree {ψ : (L[[A]]).Formula (Fin n) // P ψ} :=
    BinaryTree.ofSplit ⟨φ, hφ⟩ split
  let chi (s : List Bool) : (L[[A]]).Formula (Fin n) :=
    Classical.choose (hsplit (tf.node s).1 (tf.node s).2)
  -- Each child conjoins its parent with `chi s` or with its negation.
  have hchild_false (s : List Bool) :
      (tf.node (s ++ [false])).1 = (tf.node s).1 ⊓ chi s := by
    rw [BinaryTree.ofSplit_node_snoc_false ⟨φ, hφ⟩ split s]
  have hchild_true (s : List Bool) :
      (tf.node (s ++ [true])).1 = (tf.node s).1 ⊓ ∼(chi s) := by
    rw [BinaryTree.ofSplit_node_snoc_true ⟨φ, hφ⟩ split s]
  have hchild_disj (s : List Bool) (v : Fin n → M) :
      ¬ ((tf.node (s ++ [false])).1.Realize v ∧ (tf.node (s ++ [true])).1.Realize v) := by
    rw [hchild_false s, hchild_true s]
    simp only [Formula.realize_inf, Formula.realize_not]
    tauto
  have hchild (s : List Bool) (b : Bool) :
      (tf.node (s ++ [b])).1 = (tf.node s).1 ⊓ (if b then ∼(chi s) else chi s) := by
    cases b
    · simpa using hchild_false s
    · simpa using hchild_true s
  -- Collect the parameters occurring in the tree into one countable set `A₀`.
  let A₀ : Set M := ⋃ s : List Bool,
    Set.range fun c : (tf.node s).1.paramFinset ↦ (c.1 : M)
  have hA₀ : A₀.Countable :=
    Set.countable_iUnion fun _ ↦ Set.countable_range _
  let b (s : List Bool) : (tf.node s).1.paramFinset → A₀ :=
    fun c ↦ ⟨(c.1 : M), Set.mem_iUnion.mpr ⟨s, Set.mem_range_self c⟩⟩
  -- Move every node formula to the smaller parameter set `A₀`.
  let θ (s : List Bool) : (L[[A₀]]).Formula (Fin n) :=
    (tf.node s).1.unbindParam.bindParam (b s)
  have hθ_realize (s : List Bool) (v : Fin n → M) :
      (θ s).Realize v ↔ (tf.node s).1.Realize v :=
    Formula.realize_bind_unbind (tf.node s).1 (b s) (fun _ ↦ rfl) v
  have hθ_realized (s : List Bool) : ∃ v : Fin n → M, (θ s).Realize v :=
    (hrealize (tf.node s).1 (tf.node s).2).imp fun v hv ↦ (hθ_realize s v).mpr hv
  let T₀ : (L[[A₀]]).Theory := (L[[A₀]]).completeTheory M
  have hT₀c : T₀.IsComplete := completeTheory.isComplete (L := L[[A₀]]) M
  have hCnonempty (x : ℕ → Bool) (k : ℕ) :
      (T₀.typesWith (Formula.equivSentence (θ (pref x k)))).Nonempty :=
    (CompleteType.typesWith_nonempty_iff_exists_realize hT₀c _).mpr (hθ_realized (pref x k))
  -- The tree of basic open sets defined by the moved formulas.
  let C : SetBinaryTree (T₀.CompleteType (Fin n)) :=
    { node := fun s ↦ T₀.typesWith (Formula.equivSentence (θ s)) }
  have hCsub : C.ParentChildLaw (fun a b : Set (T₀.CompleteType (Fin n)) ↦ b ⊆ a) := by
    intro s b
    rw [CompleteType.typesWith_subset_iff_realize_imp (N := M) hT₀c]
    intro v hv
    rw [hθ_realize (s ++ [b]) v, hchild s b] at hv
    exact (hθ_realize s v).mpr (Formula.realize_inf.mp hv).1
  have hCdisj : C.SiblingRaw (fun a b : Set (T₀.CompleteType (Fin n)) ↦ Disjoint a b) := by
    intro s
    rw [CompleteType.typesWith_disjoint_iff_not_realize_and (N := M) hT₀c]
    intro v hv hw
    rw [hθ_realize (s ++ [false]) v] at hv
    rw [hθ_realize (s ++ [true]) v] at hw
    exact hchild_disj s v ⟨hv, hw⟩
  have hCne (x : ℕ → Bool) : (⋂ k, C.node (pref x k)).Nonempty :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (fun k ↦ C.node (pref x k))
      (fun k ↦ SetBinaryTree.node_pref_succ_subset C hCsub x k)
      (fun k ↦ hCnonempty x k)
      ((CompleteType.isClosed_typesWith (T := T₀) _).isCompact)
      (fun k ↦ CompleteType.isClosed_typesWith (T := T₀) _)
  obtain ⟨f, hf_inj, _⟩ :=
    SetBinaryTree.exists_injective_of_nonempty_branchInter C hCsub hCdisj hCne
  letI : Countable (T₀.CompleteType (Fin n)) := hT M A₀ hA₀ n hn
  exact not_countable_nat_bool hf_inj.countable

end FormulaSplitting

namespace CompleteType

variable {T} {M : Theory.ModelType.{u, v, w} T}
variable {A : Set M}

/-- Every nonempty basic open set of complete types over an omega-stable theory contains an
isolated type. -/
theorem exists_isolated_mem_typesWith (hT : T.IsOmegaStable.{u, v, w})
    (n : ℕ) (hn : 1 ≤ n) (φ : L[[A]].Formula (Fin n))
    (hne : ((L[[A]].completeTheory M).typesWith (Formula.equivSentence φ)).Nonempty) :
    ∃ p ∈ (L[[A]].completeTheory M).typesWith (Formula.equivSentence φ), p.IsIsolated := by
  classical
  by_contra hcon
  push Not at hcon
  let T' : (L[[A]]).Theory := (L[[A]]).completeTheory M
  have hT'c : T'.IsComplete := completeTheory.isComplete (L := L[[A]]) M
  -- The property specific to this argument: defining a nonempty basic open set with no isolated
  -- type.  The binary splitting obstruction then takes over the rest of the proof.
  let Good : (L[[A]]).Formula (Fin n) → Prop := fun ψ =>
    (T'.typesWith (Formula.equivSentence ψ)).Nonempty ∧
      ∀ p ∈ T'.typesWith (Formula.equivSentence ψ), ¬ p.IsIsolated
  have hsplit : ∀ ψ : (L[[A]]).Formula (Fin n), Good ψ →
      ∃ χ : (L[[A]]).Formula (Fin n), Good (ψ ⊓ χ) ∧ Good (ψ ⊓ ∼χ) := by
    intro ψ hψ
    obtain ⟨χ, h1, h2, h3, h4⟩ :=
      exists_isolated_splitting_formula (T := T') ψ hψ.1 hψ.2
    exact ⟨χ, ⟨h1, h3⟩, ⟨h2, h4⟩⟩
  exact hT.false_of_formula_splitting n hn Good φ ⟨hne, hcon⟩ hsplit fun ψ hψ ↦
    (typesWith_nonempty_iff_exists_realize hT'c ψ).mp hψ.1

end CompleteType

end Theory

end Language

end FirstOrder
