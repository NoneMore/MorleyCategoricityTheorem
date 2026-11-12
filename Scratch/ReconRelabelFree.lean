/-
Recon scratch — NOT part of the library.

Experiment: can `Formula.relabel` be decoupled from the general binder-shifting
`BoundedFormula.relabel` and re-implemented as a genuinely arity-preserving
free-variable relabel, so that formula-level naturality lands inside the existing
`mapTermRel` algebra (`mapTermRel_mapTermRel`) with no structural induction?

Round-1 primitives (`LHom.onTerm_relabel`, `LHom.onBoundedFormula_eq_mapTermRel`,
`BoundedFormula.mapTermRel_congr`, `BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap`)
live in `Scratch/ReconSyntaxKernel{,2}.lean` and are imported here.
-/
import Mathlib.ModelTheory.Syntax
import Scratch.ReconSyntaxKernel2

open FirstOrder

universe u v u' v' w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {α β γ : Type*}

namespace BoundedFormula

/-- Arity-preserving free-variable relabeling.  Unlike `BoundedFormula.relabel` (whose
arity index is shifted by the number `n` of extra bound variables it introduces), this
keeps the bound-variable arity exactly fixed, so it is an instance of `mapTermRel` with
`g = id` and `h = id`. -/
def relabelFree (f : α → β) {n : ℕ} : L.BoundedFormula α n → L.BoundedFormula β n :=
  mapTermRel (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)

@[simp]
theorem relabelFree_falsum (f : α → β) {n : ℕ} :
    relabelFree f (falsum : L.BoundedFormula α n) = falsum := rfl

@[simp]
theorem relabelFree_imp (f : α → β) {n : ℕ} (φ ψ : L.BoundedFormula α n) :
    relabelFree f (φ.imp ψ) = (relabelFree f φ).imp (relabelFree f ψ) := rfl

@[simp]
theorem relabelFree_all (f : α → β) {n : ℕ} (φ : L.BoundedFormula α (n + 1)) :
    relabelFree f φ.all = (relabelFree f φ).all := rfl

/-! ## Algebraic laws, all [0 inductions] -/

/-- `relabelFree` is functorial.  [0 inductions] -/
theorem relabelFree_comp (g : α → β) (g' : β → γ) {n : ℕ} (ψ : L.BoundedFormula α n) :
    relabelFree g' (relabelFree g ψ) = relabelFree (g' ∘ g) ψ := by
  simp only [relabelFree]
  rw [mapTermRel_mapTermRel]
  apply BoundedFormula.mapTermRel_congr
  · intro n t
    simp only [Function.comp_apply, Term.relabel_relabel]
    congr 1
    funext x
    rcases x with a | i <;> rfl
  · intro n R
    rfl

/-- `relabelFree` preserves identities.  [0 inductions] -/
theorem relabelFree_id {n : ℕ} (ψ : L.BoundedFormula α n) :
    relabelFree (id : α → α) ψ = ψ := by
  have h : relabelFree (id : α → α) ψ =
      ψ.mapTermRel (fun _ => id) (fun _ => id) (fun _ => id) := by
    apply BoundedFormula.mapTermRel_congr
    · intro n t
      rw [show Sum.map (id : α → α) (id : Fin n → Fin n) = id from by
            funext x; rcases x with a | i <;> rfl, Term.relabel_id]
      rfl
    · intro n R
      rfl
  rw [h, mapTermRel_id_id_id]

/-- `BoundedFormula.relabelEquiv` is the arity-preserving `relabelFree` (the binder index
is a genuine `≃`, so no `castLE` appears).  [0 inductions] -/
theorem relabelEquiv_eq_relabelFree (e : α ≃ β) {k : ℕ} (ψ : L.BoundedFormula α k) :
    BoundedFormula.relabelEquiv e ψ = BoundedFormula.relabelFree e ψ := by
  apply BoundedFormula.mapTermRel_congr (φ := ψ)
  · intro n t
    congr 1
  · intro n R
    rfl

/-- The inverse of `relabelEquiv` is relabeling along the inverse.  [0 inductions] -/
theorem relabelEquiv_symm_eq_relabelFree (e : α ≃ β) {k : ℕ} (ψ : L.BoundedFormula β k) :
    (BoundedFormula.relabelEquiv e).symm ψ = BoundedFormula.relabelFree e.symm ψ := by
  simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv,
    BoundedFormula.relabelFree]
  apply BoundedFormula.mapTermRel_congr (φ := ψ)
  · intro n t
    congr 1
  · intro n R
    rfl

/-! ## Bridge to the Mathlib `BoundedFormula.relabel` -/

/-- The `relabelAux` of `BoundedFormula.relabel` at the special map `Sum.inl ∘ f` is an
arity-preserving `Sum.map`.  [0 inductions] -/
theorem relabelAux_sumInl_comp (f : α → β) (n : ℕ) :
    relabelAux (Sum.inl ∘ f) n = Sum.map f (Fin.castLE (Nat.le_add_left n 0)) := by
  funext x
  rcases x with a | i
  · rfl
  · rw [relabelAux]
    simp only [Function.comp_apply, Sum.map_inr, Equiv.sumAssoc_apply_inr,
      finSumFinEquiv_apply_right]
    congr 1
    ext
    simp [Fin.natAdd]

/-- Term-level form of the arity cast.  [0 inductions] -/
theorem term_relabel_castLE (f : α → β) {n : ℕ} (h : n ≤ 0 + n)
    (t : L.Term (α ⊕ Fin n)) :
    t.relabel (Sum.map f (Fin.castLE h)) =
      (t.relabel (Sum.map f id)).relabel (Sum.map id (Fin.castLE h)) := by
  rw [Term.relabel_relabel]
  congr 1
  funext x
  rcases x with a | i <;> rfl

/-- Bridge: `BoundedFormula.relabel` along `Sum.inl ∘ f` is `relabelFree f` followed by
the arity cast `n → 0 + n`.

This is the *only* `BoundedFormula` induction in the whole development: every later
naturality statement is derived from it algebraically. -/
theorem relabel_sumInl_comp_eq_relabelFree_castLE (f : α → β) {n : ℕ}
    (φ : L.BoundedFormula α n) :
    φ.relabel (Sum.inl ∘ f) = (relabelFree f φ).castLE (Nat.le_add_left n 0) := by
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp only [relabel, mapTermRel, relabelFree, castLE, relabelAux_sumInl_comp]
    congr 1 <;> exact term_relabel_castLE f _ _
  | rel R ts =>
    simp only [relabel, mapTermRel, relabelFree, castLE, relabelAux_sumInl_comp]
    congr 1
    funext i
    simpa only [Function.comp_apply] using term_relabel_castLE f _ (ts i)
  | imp f₁ f₂ ih1 ih2 =>
    simp only [relabel, mapTermRel, relabelFree, castLE] at ih1 ih2 ⊢
    rw [ih1, ih2]
  | all f ih =>
    simp only [relabel, mapTermRel, relabelFree] at ih ⊢
    rw [ih]
    simp only [castLE, castLE_castLE]
    congr 1

end BoundedFormula

namespace LHom

/-- Symbol renaming commutes with arity-preserving free-variable relabeling of bounded
formulas.  [0 `BoundedFormula` inductions: both maps are identity-arity `mapTermRel`s and
`onTerm` commutes with `Term.relabel`, so `mapTermRel_mapTermRel` + `mapTermRel_congr` do
all the work.] -/
theorem onBoundedFormula_relabelFree (Φ : L →ᴸ L') (f : α → β) {n : ℕ}
    (ψ : L.BoundedFormula α n) :
    Φ.onBoundedFormula (BoundedFormula.relabelFree f ψ) =
      BoundedFormula.relabelFree f (Φ.onBoundedFormula ψ) := by
  simp only [BoundedFormula.relabelFree, LHom.onBoundedFormula_eq_mapTermRel]
  simp only [BoundedFormula.mapTermRel_mapTermRel]
  apply BoundedFormula.mapTermRel_congr
  · intro n t
    simpa only [Function.comp_apply] using LHom.onTerm_relabel Φ (Sum.map f id) t
  · intro n R
    rfl

end LHom

/-- Naturality of `BoundedFormula.constantsVarsEquiv` against the constant-renaming
language map, restated with `relabelFree`.  [0 inductions] -/
theorem BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap_relabelFree
    {κ κ' : Type*} (f : κ → κ') {γ : Type*} {n : ℕ}
    (ψ : (L[[κ]]).BoundedFormula γ n) :
    BoundedFormula.constantsVarsEquiv ((L.lhomWithConstantsMap f).onBoundedFormula ψ) =
      BoundedFormula.relabelFree (Sum.map f (id : γ → γ))
        (BoundedFormula.constantsVarsEquiv ψ) := by
  rw [BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap]
  rfl

namespace Formula

/-- Experiment-version `Formula.relabel`, arity-preserving by construction. -/
def relabel' (f : α → β) : L.Formula α → L.Formula β :=
  BoundedFormula.relabelFree f

@[simp]
theorem relabel'_apply (f : α → β) (θ : L.Formula α) :
    relabel' f θ = BoundedFormula.relabelFree f θ := rfl

/-- The bridge: the arity-preserving `relabel'` agrees with the Mathlib `relabel`.
[derived from the single `BoundedFormula` induction above; 0 inductions here] -/
theorem relabel'_eq_relabel (f : α → β) (φ : L.Formula α) :
    relabel' f φ = φ.relabel f := by
  show BoundedFormula.relabelFree f φ = BoundedFormula.relabel (Sum.inl ∘ f) φ
  rw [BoundedFormula.relabel_sumInl_comp_eq_relabelFree_castLE, BoundedFormula.castLE_rfl]

/-- `relabel'` is functorial.  [0 inductions] -/
theorem relabel'_comp (g : α → β) (g' : β → γ) (θ : L.Formula α) :
    relabel' g' (relabel' g θ) = relabel' (g' ∘ g) θ :=
  BoundedFormula.relabelFree_comp g g' θ

end Formula

namespace LHom

/-- `LHom.onFormula` commutes with the arity-preserving `Formula.relabel'`.  [0
`BoundedFormula` inductions] -/
theorem onFormula_relabel' (Φ : L →ᴸ L') (f : α → β) (θ : L.Formula α) :
    Φ.onFormula (Formula.relabel' f θ) = Formula.relabel' f (Φ.onFormula θ) :=
  LHom.onBoundedFormula_relabelFree Φ f θ

end LHom

namespace Formula

/-- `constantsVarsEquiv` turns `equivSentence` into the inverse of `relabelEquiv` along
`Equiv.sumEmpty`.  [0 inductions] -/
theorem constantsVarsEquiv_equivSentence (θ : L.Formula α) :
    BoundedFormula.constantsVarsEquiv (Formula.equivSentence θ) =
      (BoundedFormula.relabelEquiv (Equiv.sumEmpty α Empty)).symm θ := by
  rw [Formula.equivSentence, Equiv.symm_trans_apply]
  exact _root_.Equiv.apply_symm_apply (BoundedFormula.constantsVarsEquiv (L := L) (γ := α)
    (α := Empty) (n := 0)) _

/-- **Main naturality**: renaming constants after `Formula.equivSentence` is
`Formula.equivSentence` after relabeling the free variables.

[0 `BoundedFormula` inductions: the proof is `constantsVarsEquiv` injectivity plus the
`mapTermRel` algebra of `relabelFree`.] -/
theorem onSentence_equivSentence_relabel' (f : α → β) (θ : L.Formula α) :
    (L.lhomWithConstantsMap f).onSentence (Formula.equivSentence θ) =
      Formula.equivSentence (Formula.relabel' f θ) := by
  refine (BoundedFormula.constantsVarsEquiv (L := L) (γ := β)).injective ?_
  rw [LHom.onSentence, LHom.onFormula,
    BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap_relabelFree]
  rw [Formula.constantsVarsEquiv_equivSentence,
    Formula.constantsVarsEquiv_equivSentence]
  rw [Formula.relabel'_apply]
  rw [BoundedFormula.relabelEquiv_symm_eq_relabelFree,
    BoundedFormula.relabelEquiv_symm_eq_relabelFree]
  rw [BoundedFormula.relabelFree_comp, BoundedFormula.relabelFree_comp]
  congr 1

end Formula

end Language

end FirstOrder
