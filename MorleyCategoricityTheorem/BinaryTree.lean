import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Set.Lattice
import Mathlib.Logic.Relation

/-!
# Binary trees

A *binary tree* on a type `α` is a family of elements of `α` indexed by the nodes of the
infinite binary tree, i.e. by the finite binary words `List Bool`.  Such trees appear in
classical proofs of Morley's categoricity theorem when organizing (definable) data indexed
by finite binary sequences: the value `node w` is the datum carried by the node reached by
reading the word `w` from the root.  A *complete* binary tree additionally assigns data to
infinite branches.
-/

universe u v

/-- The prefix of length `n` of an infinite binary branch `x : ℕ → Bool`: the finite binary
word consisting of the first `n` choices of `x`. -/
def pref (x : ℕ → Bool) (n : ℕ) : List Bool :=
  List.ofFn (fun i : Fin n ↦ x i)

/-- The prefix of length `k + 1` is the prefix of length `k` followed by the next bit. -/
theorem pref_succ (x : ℕ → Bool) (k : ℕ) : pref x (k + 1) = pref x k ++ [x k] := by
  unfold pref
  rw [List.ofFn_succ', List.concat_eq_append]
  rfl

/-- A binary tree on `α`: a family of elements of `α` indexed by the finite binary words
`List Bool`, each word naming the node reached from the root by following the entries of
the word (`false` = left child, `true` = right child). -/
structure BinaryTree (α : Type u) where
  node : List Bool → α

namespace BinaryTree

variable {α : Type u} (T : BinaryTree α)

/-- Build a binary tree recursively from a root element `root` and a splitting function
`split : α → α × α`: the root node is `root`, and if a node carries `x`, then its left child
carries `(split x).1` while its right child carries `(split x).2`.  Reading a finite binary word
from the root, each bit selects the left (`false`) or right (`true`) child. -/
def ofSplit (root : α) (split : α → α × α) : BinaryTree α where
  node s := s.foldl (fun x b ↦ if b then (split x).2 else (split x).1) root

/-- The root node of a tree built by `ofSplit` is the given root element. -/
@[simp] lemma ofSplit_node_nil (root : α) (split : α → α × α) :
    (ofSplit root split).node [] = root := by
  rfl

/-- The left child of a node in a tree built by `ofSplit` is the first component of its
split. -/
lemma ofSplit_node_snoc_false (root : α) (split : α → α × α) (s : List Bool) :
    (ofSplit root split).node (s ++ [false]) = (split ((ofSplit root split).node s)).1 := by
  simp [ofSplit, List.foldl_append]

/-- The right child of a node in a tree built by `ofSplit` is the second component of its
split. -/
lemma ofSplit_node_snoc_true (root : α) (split : α → α × α) (s : List Bool) :
    (ofSplit root split).node (s ++ [true]) = (split ((ofSplit root split).node s)).2 := by
  simp [ofSplit, List.foldl_append]

/-- The image of a binary tree under a function `f : α → β`: the node at a finite binary word
`s` in the image tree is `f` applied to the corresponding node of `T`. -/
def map {β : Type v} (f : α → β) (T : BinaryTree α) : BinaryTree β where
  node s := f (T.node s)

/-- The node of `map f T` at word `s` is `f` applied to the node of `T` at `s`. -/
@[simp] lemma map_node {β : Type v} (f : α → β) (T : BinaryTree α) (s : List Bool) :
    (map f T).node s = f (T.node s) := by
  rfl

/-- The *parent–child law*: every node `T.node s` is `R`-related to each of its two children
`T.node (s ++ [false])` and `T.node (s ++ [true])`. -/
def ParentChildLaw (R : α → α → Prop) : Prop :=
  ∀ s b, R (T.node s) (T.node (s ++ [b]))

/-- The *sibling law*: the two children `T.node (s ++ [false])` and `T.node (s ++ [true])` of
every node `T.node s` are `R`-related. -/
def SiblingRaw (R : α → α → Prop) : Prop :=
  ∀ s, R (T.node (s ++ [false])) (T.node (s ++ [true]))

/-- The *fork law*: at every node `T.node s`, the ternary relation `S` relates the node to its
two children. -/
def ForkLaw (S : α → α → α → Prop) : Prop :=
  ∀ s, S (T.node s) (T.node (s ++ [false])) (T.node (s ++ [true]))

/-- The *hereditary property*: whenever a node `T.node s` has property `P`, both of its
children `T.node (s ++ [false])` and `T.node (s ++ [true])` have property `P`.  This is exactly
the parent–child law for the implication relation `fun x y => P x → P y`: unrolling
`ParentChildLaw` yields `∀ s b, P (T.node s) → P (T.node (s ++ [b]))`, the bit `b` ranging over
both children. -/
def Hereditary (P : α → Prop) : Prop :=
  T.ParentChildLaw (fun x y => P x → P y)

/-- A property `P` is hereditary on `T` iff every node satisfying `P` has all of its children
satisfying `P`. -/
lemma hereditary_iff {P : α → Prop} :
    T.Hereditary P ↔ ∀ s b, P (T.node s) → P (T.node (s ++ [b])) := by
  rfl

/-- The property that *every* node of `T` satisfies `P`. -/
def AllNodes (P : α → Prop) : Prop :=
  ∀ s, P (T.node s)

/-- If a binary tree has nodes in the subtype `{x : α // P x}`, then `Subtype.val` induces a
binary tree on `α`, and every node of that induced tree satisfies `P`. -/
lemma subtype_val_allNodes {P : α → Prop} (T : BinaryTree (Subtype P)) :
    (T.map Subtype.val).AllNodes P :=
  fun s => (T.node s).property

/-- If `R` satisfies the parent–child law and is reflexive and transitive, then every node is
`R`-related to all of its descendants: whenever `s` is a prefix of `t`, we have
`R (T.node s) (T.node t)`.  Reflexivity covers the case `s = t`, and transitivity chains the
parent–child law along the path from `s` down to `t`. -/
lemma parentChildLaw_prefix {T : BinaryTree α} {R : α → α → Prop}
    (hT : T.ParentChildLaw R) (hR : Std.Refl R) (hT' : IsTrans α R) :
    ∀ {s t : List Bool}, s <+: t → R (T.node s) (T.node t) := by
  intro s t hpre
  rcases hpre with ⟨r, hr⟩
  rw [← hr]
  clear hr
  revert s
  induction r with
  | nil =>
      intro s
      simpa using hR.refl (T.node s)
  | cons b r ih =>
      intro s
      have hstep : R (T.node s) (T.node (s ++ [b])) := hT s b
      have hrest : R (T.node (s ++ [b])) (T.node ((s ++ [b]) ++ r)) := ih
      exact hT'.trans (T.node s) (T.node (s ++ [b])) (T.node (s ++ b :: r)) hstep
        (by simpa [List.append_assoc] using hrest)

/-- If `P` is hereditary on `T`, then `P` propagates from a node to all of its descendants:
whenever `s` is a prefix of `t` and `P (T.node s)` holds, so does `P (T.node t)`.  This is the
specialization of `parentChildLaw_prefix` to the implication relation `P x → P y`, whose
reflexivity and transitivity are definitional. -/
lemma hereditary_prefix {P : α → Prop} (hP : T.Hereditary P) :
    ∀ {s t : List Bool}, s <+: t → P (T.node s) → P (T.node t) := by
  intro s t hpre hPs
  exact (T.parentChildLaw_prefix (R := fun x y => P x → P y) hP
    ⟨fun x hx => hx⟩
    ⟨fun x y z hxy hyz hx => hyz (hxy hx)⟩) hpre hPs

/-- If the root node `T.node []` has property `P` and `P` is hereditary on `T`, then *every*
node of `T` has property `P`: heredity pushes `P` from the root down along every path. -/
lemma root_hereditary_allNodes {P : α → Prop} (hroot : P (T.node [])) (hP : T.Hereditary P) :
    T.AllNodes P := by
  intro s
  exact (T.hereditary_prefix hP (s := []) (t := s) List.nil_prefix) hroot

/-- If `R` relates every element to both components of its split, then `R` satisfies the
parent–child law on the tree built by `ofSplit`. -/
lemma ofSplit_parentChildLaw (root : α) (split : α → α × α) (R : α → α → Prop)
    (h : ∀ x, R x (split x).1 ∧ R x (split x).2) :
    (ofSplit root split).ParentChildLaw R := by
  intro s b
  rcases h ((ofSplit root split).node s) with ⟨hl, hr⟩
  cases b with
  | false => simpa [ofSplit_node_snoc_false] using hl
  | true => simpa [ofSplit_node_snoc_true] using hr

/-- If `R` relates the two components of every split, then `R` satisfies the sibling law on the
tree built by `ofSplit`. -/
lemma ofSplit_siblingRaw (root : α) (split : α → α × α) (R : α → α → Prop)
    (h : ∀ x, R (split x).1 (split x).2) :
    (ofSplit root split).SiblingRaw R := by
  intro s
  simpa [ofSplit_node_snoc_false, ofSplit_node_snoc_true] using h ((ofSplit root split).node s)

/-- If `S` relates every element to the two components of its split, then `S` satisfies the fork
law on the tree built by `ofSplit`. -/
lemma ofSplit_forkLaw (root : α) (split : α → α × α) (S : α → α → α → Prop)
    (h : ∀ x, S x (split x).1 (split x).2) :
    (ofSplit root split).ForkLaw S := by
  intro s
  simpa [ofSplit_node_snoc_false, ofSplit_node_snoc_true] using h ((ofSplit root split).node s)

/-- If a property is preserved by both components of every split, then it is hereditary on the
tree built by `ofSplit`. -/
lemma ofSplit_hereditary (root : α) (split : α → α × α) (P : α → Prop)
    (h : ∀ x, P x → P (split x).1 ∧ P (split x).2) :
    (ofSplit root split).Hereditary P := by
  intro s b hP
  rcases h ((ofSplit root split).node s) hP with ⟨hl, hr⟩
  cases b with
  | false => simpa [ofSplit_node_snoc_false] using hl
  | true => simpa [ofSplit_node_snoc_true] using hr

/-- If the root satisfies `P` and `P` is preserved by both components of every split, then every
node of the tree built by `ofSplit` satisfies `P`. -/
lemma ofSplit_allNodes (root : α) (split : α → α × α) (P : α → Prop)
    (hroot : P root) (h : ∀ x, P x → P (split x).1 ∧ P (split x).2) :
    (ofSplit root split).AllNodes P := by
  exact root_hereditary_allNodes (ofSplit root split) (by simpa using hroot)
    (ofSplit_hereditary root split P h)

end BinaryTree

/-- A complete binary tree with node data in `α` and branch data in `β`: a binary tree
together with a family of elements of `β` indexed by the infinite branches `ℕ → Bool`.  The
type `β` of branch data is deliberately independent of the type `α` of node data. -/
structure CompleteBinaryTree (α : Type u) (β : Type v) extends BinaryTree α where
  branch : (ℕ → Bool) → β

namespace CompleteBinaryTree

variable {α : Type u} {β : Type v}

/-- The *branch law*: if a node lying on the infinite branch `b` at the prefix of length `n`
satisfies `P`, then the branch datum `T.branch b` satisfies `Q`.  In symbols:
`∀ b, ∀ n, P (T.node (pref b n)) → Q (T.branch b)`. -/
def BranchLaw (T : CompleteBinaryTree α β) (P : α → Prop) (Q : β → Prop) : Prop :=
  ∀ b : ℕ → Bool, (∀ n : ℕ, P (T.node (pref b n))) → Q (T.branch b)

end CompleteBinaryTree

abbrev SetBinaryTree (α : Type u) := BinaryTree (Set α)

namespace SetBinaryTree

variable {α : Type u} (T : SetBinaryTree α)

def CompletionOfInt : CompleteBinaryTree (Set α) (Set α) :=
  CompleteBinaryTree.mk T (fun b => ⋂ n, T.node (pref b n))

/-- If every split produces two subsets of the parent, then the reverse-inclusion relation
satisfies the parent–child law on the tree built by `ofSplit`: every child is a subset of its
parent. -/
lemma ofSplit_parentChildLaw_subset (root : Set α) (split : Set α → Set α × Set α)
    (h : ∀ x, (split x).1 ⊆ x ∧ (split x).2 ⊆ x) :
    (BinaryTree.ofSplit root split).ParentChildLaw (fun a b : Set α ↦ b ⊆ a) :=
  BinaryTree.ofSplit_parentChildLaw root split (fun a b : Set α ↦ b ⊆ a) h

/-- If the two children of every split are disjoint, then siblings are disjoint in the tree
built by `ofSplit`. -/
lemma ofSplit_siblingRaw_disjoint (root : Set α) (split : Set α → Set α × Set α)
    (h : ∀ x, Disjoint (split x).1 (split x).2) :
    (BinaryTree.ofSplit root split).SiblingRaw (fun a b : Set α ↦ Disjoint a b) :=
  BinaryTree.ofSplit_siblingRaw root split (fun a b : Set α ↦ Disjoint a b) h

/-- If the root is nonempty and every split of a nonempty set yields two nonempty children,
then every node of the tree built by `ofSplit` is nonempty. -/
lemma ofSplit_allNodes_nonempty (root : Set α) (split : Set α → Set α × Set α)
    (hroot : root.Nonempty) (h : ∀ x, x.Nonempty → (split x).1.Nonempty ∧ (split x).2.Nonempty) :
    (BinaryTree.ofSplit root split).AllNodes (fun a : Set α ↦ a.Nonempty) :=
  BinaryTree.ofSplit_allNodes root split (fun a : Set α ↦ a.Nonempty) hroot h

/-- If every child is a subset of its parent, then the node of a longer word is a subset of the
node of any of its prefixes. -/
lemma node_subset_of_prefix (hsub : T.ParentChildLaw (fun a b : Set α ↦ b ⊆ a))
    {u v : List Bool} (h : u <+: v) : T.node v ⊆ T.node u := by
  have hrefl : Std.Refl (fun a b : Set α ↦ b ⊆ a) := ⟨fun a ↦ Set.Subset.refl a⟩
  have htrans : IsTrans (Set α) (fun a b : Set α ↦ b ⊆ a) :=
    ⟨fun a b c hab hbc ↦ Set.Subset.trans hbc hab⟩
  exact T.parentChildLaw_prefix (R := fun a b : Set α ↦ b ⊆ a) hsub hrefl htrans h

/-- If every child is a subset of its parent, then along any branch the node at the prefix of
length `k + 1` is a subset of the node at the prefix of length `k`. -/
lemma node_pref_succ_subset (hsub : T.ParentChildLaw (fun a b : Set α ↦ b ⊆ a))
    (x : ℕ → Bool) (k : ℕ) : T.node (pref x (k + 1)) ⊆ T.node (pref x k) := by
  rw [pref_succ]
  exact hsub (pref x k) (x k)

/-- If children are subsets of their parent and siblings are disjoint, then two nodes whose
words share the prefix `s` and then diverge at two distinct bits `b₁ ≠ b₂` are disjoint. -/
lemma disjoint_of_diverge
    (hsub : T.ParentChildLaw (fun a b : Set α ↦ b ⊆ a))
    (hdisj : T.SiblingRaw (fun a b : Set α ↦ Disjoint a b)) :
    ∀ {s : List Bool} {b₁ b₂ : Bool} {s' t' : List Bool},
      b₁ ≠ b₂ → Disjoint (T.node (s ++ b₁ :: s')) (T.node (s ++ b₂ :: t')) := by
  intro s b₁ b₂ s' t' hne
  have h₁ : T.node (s ++ b₁ :: s') ⊆ T.node (s ++ [b₁]) := by
    exact node_subset_of_prefix T hsub (by simp : s ++ [b₁] <+: s ++ b₁ :: s')
  have h₂ : T.node (s ++ b₂ :: t') ⊆ T.node (s ++ [b₂]) := by
    exact node_subset_of_prefix T hsub (by simp : s ++ [b₂] <+: s ++ b₂ :: t')
  have hdisj' : Disjoint (T.node (s ++ [b₁])) (T.node (s ++ [b₂])) := by
    cases b₁ with
    | false =>
        cases b₂ with
        | false => exact (hne rfl).elim
        | true => simpa using hdisj s
    | true =>
        cases b₂ with
        | false => exact (hdisj s).symm
        | true => exact (hne rfl).elim
  exact hdisj'.mono_left h₁ |>.mono_right h₂

/-- *Branch selection*: if every child is a subset of its parent, siblings are disjoint, and
every branch intersection is nonempty, then choosing a point in each branch intersection yields
an injection from the infinite branches into `α`, whose chosen points all lie in the
corresponding nodes.  Two distinct branches first differ at some bit `k`; the chosen points then
lie in the two subtrees below the common prefix, which `disjoint_of_diverge` shows to be
disjoint. -/
theorem exists_injective_of_nonempty_branchInter
    (hsub : T.ParentChildLaw (fun a b : Set α ↦ b ⊆ a))
    (hdisj : T.SiblingRaw (fun a b : Set α ↦ Disjoint a b))
    (hne : ∀ x : ℕ → Bool, (⋂ n, T.node (pref x n)).Nonempty) :
    ∃ f : (ℕ → Bool) → α, Function.Injective f ∧ ∀ x n, f x ∈ T.node (pref x n) := by
  classical
  let f : (ℕ → Bool) → α := fun x ↦ Classical.choose (hne x)
  have hf : ∀ x n, f x ∈ T.node (pref x n) := fun x n ↦
    Set.mem_iInter.mp (Classical.choose_spec (hne x)) n
  refine ⟨f, ?_, hf⟩
  intro x y hxy
  by_contra hne'
  have hdiv : ∃ k, x k ≠ y k := Function.ne_iff.mp hne'
  let k := Nat.find hdiv
  have hk : x k ≠ y k := Nat.find_spec hdiv
  have hpref : pref x k = pref y k := by
    simp only [pref]
    congr 1
    funext i
    exact not_not.mp (Nat.find_min hdiv i.isLt)
  have hx : f x ∈ T.node (pref x k ++ [x k]) := by
    simpa [pref_succ] using hf x (k + 1)
  have hy : f y ∈ T.node (pref x k ++ [y k]) := by
    have h := hf y (k + 1)
    rw [pref_succ, ← hpref] at h
    exact h
  have hdisj' : Disjoint (T.node (pref x k ++ [x k])) (T.node (pref x k ++ [y k])) :=
    T.disjoint_of_diverge hsub hdisj (s := pref x k) (b₁ := x k) (b₂ := y k)
      (s' := []) (t' := []) hk
  exact (Set.disjoint_left.mp hdisj' (hxy ▸ hx)) hy

end SetBinaryTree
