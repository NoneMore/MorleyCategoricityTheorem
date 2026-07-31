import MorleyCategoricityTheorem.ModelTheory.Types

/-! Scratch development for `isIsolated_typeOf_trans`. -/


open FirstOrder Language Theory

universe u v w w' w''

namespace FirstOrder
namespace Language

namespace Formula

variable {L : Language.{u, v}} {α : Type w'} {B : Type w''}

/-- The finite set of constants from `B` used in a formula over `L[[B]]` with `α` free
variables, computed by converting constants to variables and taking the `B`-part of the
free-variable finset. -/
noncomputable def constantsFinset [DecidableEq B] [DecidableEq α]
    (φ : (L[[B]]).Formula α) : Finset B :=
  (BoundedFormula.constantsVarsEquiv φ).freeVarFinset.biUnion
    (fun x => match x with | Sum.inl b => {b} | Sum.inr _ => ∅)

/-- A formula over `L[[B]]` with `α` free variables, rewritten as a formula over `L` with
`α ⊕ Fin (constantsFinset φ).card` free variables, where the `Fin`-variables stand for the
finitely many constants occurring in `φ`. -/
noncomputable def elimConstants [DecidableEq B] [DecidableEq α] (φ : (L[[B]]).Formula α) :
    L.Formula (α ⊕ Fin (constantsFinset φ).card) :=
  let φ₁ : L.BoundedFormula (B ⊕ α) 0 := BoundedFormula.constantsVarsEquiv φ
  let V : Finset (B ⊕ α) := φ₁.freeVarFinset
  let S : Finset B := constantsFinset φ
  let φ₂ : L.BoundedFormula (S ⊕ α) 0 :=
    φ₁.restrictFreeVar (fun x =>
      match x with
      | ⟨Sum.inl b, hb⟩ => Sum.inl ⟨b, by
          rw [show S = V.biUnion (fun x => match x with | Sum.inl b => {b} | Sum.inr _ => ∅) by rfl]
          exact Finset.mem_biUnion.mpr ⟨Sum.inl b, hb, by simp⟩⟩
      | ⟨Sum.inr a, _⟩ => Sum.inr a)
  let e : S ≃ Fin S.card := Finset.equivFin S
  Formula.relabel (fun x =>
    match x with
    | Sum.inl s => Sum.inr (e s)
    | Sum.inr a => Sum.inl a) φ₂

/-- The finite tuple of parameters from `B` corresponding to the `Fin`-variables introduced by
`elimConstants`. -/
noncomputable def elimConstants_params [DecidableEq B] [DecidableEq α]
    (φ : (L[[B]]).Formula α) : Fin (constantsFinset φ).card → B :=
  fun i => ((Finset.equivFin (constantsFinset φ)).symm i : B)

variable {M : Type w} [L.Structure M] {B : Set M}

/-- Realizing `elimConstants φ` at `(a, b̄)` is the same as realizing `φ` at `a`. -/
theorem realize_elimConstants [DecidableEq M] [DecidableEq α]
    (φ : (L[[B]]).Formula α) (a : α → M) :
    φ.Realize a ↔
      (elimConstants φ).Realize
        (Sum.elim a (fun i : Fin (constantsFinset φ).card =>
          (((Finset.equivFin (constantsFinset φ)).symm i : constantsFinset φ) : M))) := by
  classical
  let φ₁ : L.Formula (B ⊕ α) := BoundedFormula.constantsVarsEquiv φ
  let V : Finset (B ⊕ α) := φ₁.freeVarFinset
  let S : Finset B := constantsFinset φ
  let e : S ≃ Fin S.card := Finset.equivFin S
  let g : S ⊕ α → α ⊕ Fin S.card :=
    fun x => match x with | Sum.inl s => Sum.inr (e s) | Sum.inr a => Sum.inl a
  let f : φ₁.freeVarFinset → S ⊕ α := fun x =>
    match x with
    | ⟨Sum.inl b, hb⟩ => Sum.inl ⟨b, by
        simpa [S, V, φ₁, constantsFinset] using
          (Finset.mem_biUnion.mpr ⟨Sum.inl b, hb, by simp⟩ : b ∈
            (BoundedFormula.constantsVarsEquiv φ).freeVarFinset.biUnion
              (fun x => match x with | Sum.inl b => {b} | Sum.inr _ => ∅))⟩
    | ⟨Sum.inr a, _⟩ => Sum.inr a
  let φ₂ : L.Formula (S ⊕ α) := φ₁.restrictFreeVar f
  have hS_def : S = constantsFinset φ := rfl
  have he_def : e = Finset.equivFin S := rfl
  have he_def' : e = Finset.equivFin (constantsFinset φ) := by rfl
  have helim : elimConstants φ = Formula.relabel g φ₂ := by
    unfold elimConstants
    dsimp
    congr 1
    · funext x
      cases x <;> rfl
    · congr 1
      funext x
      cases x with
      | mk val prop =>
        cases val <;> simp [f]
  rw [helim]
  rw [Formula.realize_relabel]
  have hcomp : (Sum.elim a (fun i : Fin S.card => ((Finset.equivFin S).symm i : M))) ∘ g =
      Sum.elim (fun s : S => (s : M)) a := by
    funext x
    cases x with
    | inl s =>
      simp [g, e]
    | inr a' =>
      simp [g]
  rw [hcomp]
  have hrestr : φ₂.Realize (Sum.elim (fun s : S => (s : M)) a) ↔
      φ₁.Realize (Sum.elim (fun b : B => (b : M)) a) := by
    change BoundedFormula.Realize φ₂ (Sum.elim (fun s : S => (s : M)) a) default ↔
      BoundedFormula.Realize φ₁ (Sum.elim (fun b : B => (b : M)) a) default
    change BoundedFormula.Realize (φ₁.restrictFreeVar f) (Sum.elim (fun s : S => (s : M)) a) default ↔
      BoundedFormula.Realize φ₁ (Sum.elim (fun b : B => (b : M)) a) default
    exact BoundedFormula.realize_restrictFreeVar
      (φ := φ₁) (f := f) (v := Sum.elim (fun s : S => (s : M)) a)
      (v' := Sum.elim (fun b : B => (b : M)) a) (by
        intro x
        cases x with
        | mk val prop =>
          cases val with
          | inl b => simp [f]
          | inr a' => rfl)
  rw [hrestr]
  have hconst : φ₁.Realize (Sum.elim (fun b : B => (b : M)) a) ↔ φ.Realize a := by
    change BoundedFormula.Realize φ₁ (Sum.elim (fun b : B => (b : M)) a) default ↔
      BoundedFormula.Realize φ a default
    rw [show φ₁ = BoundedFormula.constantsVarsEquiv φ by rfl]
    simpa using (BoundedFormula.realize_constantsVarsEquiv (φ := φ) (v := a))
  rw [hconst]

/-- Substitutes the `β`-variables of a formula by terms, keeping the `α`-variables. -/
noncomputable def evalTuple {L : Language.{u, v}} {α : Type w} {B : Type w'} {n : ℕ}
    (σ : L.Formula (α ⊕ Fin n)) (b : Fin n → B) : (L[[B]]).Formula α :=
  ((L.lhomWithConstants B).onFormula σ).subst (fun v => match v with
    | Sum.inl y => Term.var y
    | Sum.inr i => (L.con (b i)).term)

/-- Realizing `evalTuple σ b` at `x` is the same as realizing `σ` at `(x, b)`. -/
theorem realize_evalTuple {L : Language.{u, v}} {α : Type w'} {M : Type w} [L.Structure M]
    {B : Set M} {n : ℕ} (σ : L.Formula (α ⊕ Fin n)) (b : Fin n → B) (x : α → M) :
    (σ.evalTuple b).Realize x ↔ σ.Realize (Sum.elim x (fun i => ((b i : B) : M))) := by
  classical
  rw [evalTuple]
  change BoundedFormula.Realize
    (((L.lhomWithConstants B).onFormula σ).subst (fun v => match v with
      | Sum.inl y => Term.var y
      | Sum.inr i => (L.con (b i)).term)) x default ↔
    BoundedFormula.Realize σ (Sum.elim x (fun i => ((b i : B) : M))) default
  rw [BoundedFormula.realize_subst]
  simp only [LHom.onFormula, LHom.realize_onBoundedFormula]
  have h : (fun a : α ⊕ Fin n => Term.realize x (match a with
      | Sum.inl y => (var y : (L[[B]]).Term α)
      | Sum.inr i => (L.con (b i)).term)) = Sum.elim x (fun i => ((b i : B) : M)) := by
    funext a
    cases a with
    | inl y => rfl
    | inr i => simp
  rw [h]

/-- Restricts the `α`-variables of a formula to a finite set `X`, universally quantifies them,
leaving the `β`-variables free. -/
noncomputable def iAllsOn {L : Language.{u, v}} {α : Type w} {β : Type w'}
    [DecidableEq α] [DecidableEq β] (φ : L.Formula (α ⊕ β)) (X : Finset α)
    (h : ∀ a ∈ φ.freeVarFinset, match a with | Sum.inl x => x ∈ X | Sum.inr _ => True) :
    L.Formula β :=
  Formula.iAlls X (Formula.relabel Sum.swap (φ.restrictFreeVar (fun a => match a with
    | ⟨Sum.inl x, hx⟩ => Sum.inl ⟨x, h (Sum.inl x) hx⟩
    | ⟨Sum.inr y, _⟩ => Sum.inr y)))

/-- Realizing `iAllsOn φ X h` at `v` is the same as `φ` holding at every `α`-tuple which agrees
with the chosen `x : X → M` on the variables in `X`. -/
theorem realize_iAllsOn {L : Language.{u, v}} {α : Type w} {β : Type w'}
    [DecidableEq α] [DecidableEq β] {M : Type w''} [L.Structure M] (φ : L.Formula (α ⊕ β))
    (X : Finset α)
    (h : ∀ a ∈ φ.freeVarFinset, match a with | Sum.inl x => x ∈ X | Sum.inr _ => True)
    (v : β → M) (dflt : α → M) :
    (φ.iAllsOn X h).Realize v ↔
      ∀ x : X → M,
        φ.Realize (Sum.elim (fun y : α => if hy : y ∈ X then x ⟨y, hy⟩ else dflt y) v) := by
  classical
  rw [iAllsOn]
  rw [Formula.realize_iAlls]
  constructor
  · intro hx x
    simp only [Formula.realize_relabel] at hx
    have hx' : ∀ i : X → M,
        Formula.Realize (φ.restrictFreeVar (fun a => match a with
          | ⟨Sum.inl x, hx⟩ => Sum.inl ⟨x, h (Sum.inl x) hx⟩
          | ⟨Sum.inr y, _⟩ => Sum.inr y)) (Sum.elim i v) := by
      intro i
      specialize hx i
      rw [show (fun a : β ⊕ X => Sum.elim v i a) ∘ Sum.swap = Sum.elim i v by
        funext a
        cases a <;> rfl] at hx
      exact hx
    specialize hx' x
    change BoundedFormula.Realize
      (φ.restrictFreeVar (fun a => match a with
        | ⟨Sum.inl x, hx⟩ => Sum.inl ⟨x, h (Sum.inl x) hx⟩
        | ⟨Sum.inr y, _⟩ => Sum.inr y)) (Sum.elim x v) default at hx'
    rw [BoundedFormula.realize_restrictFreeVar
      (v := Sum.elim x v)
      (v' := Sum.elim (fun y : α => if hy : y ∈ X then x ⟨y, hy⟩ else dflt y) v)] at hx'
    · exact hx'
    · intro a
      cases a with
      | mk val prop =>
        cases val with
        | inl y => simp [h (Sum.inl y) prop]
        | inr z => rfl
  · intro hx x
    simp only [Formula.realize_relabel]
    rw [show (fun a : β ⊕ X => Sum.elim v x a) ∘ Sum.swap = Sum.elim x v by
      funext a; cases a <;> rfl]
    change BoundedFormula.Realize (φ.restrictFreeVar (fun a => match a with
      | ⟨Sum.inl x, hx⟩ => Sum.inl ⟨x, h (Sum.inl x) hx⟩
      | ⟨Sum.inr y, _⟩ => Sum.inr y)) (Sum.elim x v) default
    rw [BoundedFormula.realize_restrictFreeVar
      (v := Sum.elim x v)
      (v' := Sum.elim (fun y : α => if hy : y ∈ X then x ⟨y, hy⟩ else dflt y) v)]
    · exact hx x
    · intro a
      cases a with
      | mk val prop =>
        cases val with
        | inl y => simp [h (Sum.inl y) prop]
        | inr z => rfl

/-- The language inclusion `L[[A]] →ᴸ L[[B]]` induced by `A ⊆ B`. -/
@[reducible]
noncomputable def lhomInclusion {M : Type w} {A B : Set M} (hAB : A ⊆ B) : L[[A]] →ᴸ L[[B]] :=
  L.lhomWithConstantsMap (Set.inclusion hAB)

/-- The formula over `L[[B]]` obtained from an `L[[A]]`-formula in variables `α ⊕ Fin n` by
substituting the `B`-constants `b` for the `Fin n`-variables. -/
noncomputable def evalTupleB {M : Type w} {A B : Set M} (hAB : A ⊆ B)
    {α : Type w'} {n : ℕ} (χ : (L[[A]]).Formula (α ⊕ Fin n)) (b : Fin n → B) :
    (L[[B]]).Formula α :=
  ((lhomInclusion (L := L) hAB).onFormula χ).subst (fun v : α ⊕ Fin n => match v with
    | Sum.inl x => Term.var x
    | Sum.inr i => (L.con (b i)).term)

/-- Realizing `evalTupleB hAB χ b` at `x` is the same as realizing `χ` at `(x, b)`. -/
theorem realize_evalTupleB {M : Type w} [L.Structure M] {A B : Set M} (hAB : A ⊆ B)
    {α : Type w'} {n : ℕ} (χ : (L[[A]]).Formula (α ⊕ Fin n)) (b : Fin n → B) (x : α → M) :
    (evalTupleB (L := L) hAB χ b).Realize x ↔
      χ.Realize (Sum.elim x (fun i => ((b i : B) : M))) := by
  classical
  rw [evalTupleB]
  change BoundedFormula.Realize
    (((lhomInclusion (L := L) hAB).onFormula χ).subst (fun v : α ⊕ Fin n => match v with
      | Sum.inl x => Term.var x
      | Sum.inr i => (L.con (b i)).term)) x default ↔
    BoundedFormula.Realize χ (Sum.elim x (fun i => ((b i : B) : M))) default
  rw [BoundedFormula.realize_subst]
  have h : (fun a : α ⊕ Fin n => Term.realize x (match a with
      | Sum.inl y => (var y : (L[[B]]).Term α)
      | Sum.inr i => (L.con (b i)).term)) = Sum.elim x (fun i => ((b i : B) : M)) := by
    funext a
    cases a with
    | inl y => rfl
    | inr i => simp
  rw [h]
  simpa [Formula.Realize] using (LHom.realize_onFormula (lhomInclusion (L := L) hAB) χ)

/-- Realizing a formula only depends on the values of the assignment on its free variables. -/
theorem realize_iff_of_agree_freeVarFinset {M : Type w} [L.Structure M] [DecidableEq α]
    (φ : L.Formula α) {v v' : α → M}
    (h : ∀ a ∈ φ.freeVarFinset, v a = v' a) : φ.Realize v ↔ φ.Realize v' := by
  have h1 : Formula.Realize (φ.restrictFreeVar (fun a : φ.freeVarFinset => (a : α))) v ↔
      φ.Realize v := by
    simpa [Formula.Realize] using
      (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := fun a : φ.freeVarFinset => (a : α))
        (v := v) (v' := v) (xs := default) (by intro a; rfl))
  have h2 : Formula.Realize (φ.restrictFreeVar (fun a : φ.freeVarFinset => (a : α))) v ↔
      φ.Realize v' := by
    simpa [Formula.Realize] using
      (BoundedFormula.realize_restrictFreeVar (φ := φ) (f := fun a : φ.freeVarFinset => (a : α))
        (v := v) (v' := v') (xs := default) (by intro a; exact h a.1 a.2))
  exact h1.symm.trans h2

end Formula

namespace Theory

/-- Formula-level semantic entailment is preserved under renaming free variables. -/
theorem relabel_models_imp_formula {L : Language.{u, v}} (T : L.Theory) {β : Type w} {γ : Type w'}
    (g : β → γ) (φ ψ : L.Formula β)
    (h : T ⊨ᵇ φ.imp ψ) : T ⊨ᵇ (φ.relabel g).imp (ψ.relabel g) := by
  rw [models_formula_iff]
  intro M v
  rw [Formula.realize_imp]
  intro hφ
  rw [Formula.realize_relabel] at hφ
  have h' : (φ.imp ψ).Realize (v ∘ g) := h.realize_formula M
  rw [Formula.realize_imp] at h'
  rw [Formula.realize_relabel]
  exact h' hφ

/-- Semantic entailment between formulas is preserved under renaming free variables. -/
theorem relabel_models_imp {L : Language.{u, v}} (T : L.Theory) {β : Type w} {γ : Type w'}
    (g : β → γ) (φ ψ : L.Formula β)
    (h : (L.lhomWithConstants β).onTheory T ⊨ᵇ
      (Formula.equivSentence φ).imp (Formula.equivSentence ψ)) :
    (L.lhomWithConstants γ).onTheory T ⊨ᵇ
      (Formula.equivSentence (φ.relabel g)).imp (Formula.equivSentence (ψ.relabel g)) := by
  classical
  change (L.lhomWithConstants γ).onTheory T ⊨ᵇ
    Formula.equivSentence ((φ.relabel g).imp (ψ.relabel g))
  rw [← models_formula_iff_onTheory_models_equivSentence]
  change (L.lhomWithConstants β).onTheory T ⊨ᵇ
    Formula.equivSentence (φ.imp ψ) at h
  rw [← models_formula_iff_onTheory_models_equivSentence] at h
  exact relabel_models_imp_formula T g φ ψ h

/-- Universal instantiation and modus ponens: from `∀x ∈ X, (η₁ → χ)` (as a sentence over the
joint variables) together with `η₁` one obtains `χ`. -/
theorem instantiation_entailment (K : Language.{u, v}) (T : K.Theory) {α : Type w} {β : Type w'}
    [DecidableEq α] [DecidableEq β] (η₁ χ : K.Formula (α ⊕ β)) (X : Finset α)
    (h : ∀ a ∈ (η₁.imp χ).freeVarFinset,
      match a with | Sum.inl x => x ∈ X | Sum.inr _ => True) :
    (K.lhomWithConstants (α ⊕ β)).onTheory T ⊨ᵇ
      ((Formula.equivSentence ((Formula.iAllsOn (η₁.imp χ) X h).relabel Sum.inr)) ⊓
       (Formula.equivSentence η₁)).imp (Formula.equivSentence χ) := by
  classical
  rw [models_sentence_iff]
  intro N
  haveI : (K.lhomWithConstants (α ⊕ β)).IsExpansionOn ↑N :=
    LHom.isExpansionOn_reduct (K.lhomWithConstants (α ⊕ β)) ↑N
  rw [Sentence.realize_imp]
  intro hinf
  rw [Sentence.realize_inf] at hinf
  rcases hinf with ⟨hσ, hη₁⟩
  rw [Formula.realize_equivSentence] at hη₁
  rw [Formula.realize_equivSentence] at hσ
  rw [Formula.realize_relabel] at hσ
  let con : α ⊕ β → N := fun i => (K.con i : N)
  let con_y : β → N := fun i => (K.con (Sum.inr i : α ⊕ β) : N)
  have hcon_y : ((fun i : α ⊕ β => (K.con i : N)) ∘ Sum.inr) = con_y := by
    funext i
    rfl
  rw [hcon_y] at hσ
  let dflt : α → N := fun _ => Classical.choice inferInstance
  have hσ' : ∀ x : X → N,
      (η₁.imp χ).Realize (Sum.elim (fun y : α => if hy : y ∈ X then x ⟨y, hy⟩ else dflt y) con_y) :=
    (Formula.realize_iAllsOn (η₁.imp χ) X h con_y dflt).1 hσ
  let x₀ : X → N := fun ⟨y, hy⟩ => (K.con (Sum.inl y : α ⊕ β) : N)
  have hx₀ := hσ' x₀
  have hagree : ∀ a ∈ (η₁.imp χ).freeVarFinset,
      (Sum.elim (fun y : α => if hy : y ∈ X then x₀ ⟨y, hy⟩ else dflt y) con_y) a =
        (fun i : α ⊕ β => (K.con i : N)) a := by
    intro a ha
    cases a with
    | inl y =>
      simp [x₀, h (Sum.inl y) ha]
    | inr i =>
      rfl
  have hχ : (η₁.imp χ).Realize (fun i : α ⊕ β => (K.con i : N)) :=
    (Formula.realize_iff_of_agree_freeVarFinset (η₁.imp χ)
      (v := Sum.elim (fun y : α => if hy : y ∈ X then x₀ ⟨y, hy⟩ else dflt y) con_y)
      (v' := fun i : α ⊕ β => (K.con i : N)) hagree).1 hx₀
  rw [Formula.realize_imp] at hχ
  rw [Formula.realize_equivSentence]
  exact hχ hη₁

end Theory

end Language

end FirstOrder

namespace Scratch

end Scratch
