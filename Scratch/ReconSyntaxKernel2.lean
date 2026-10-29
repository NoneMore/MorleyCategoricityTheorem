/-
Recon scratch (round 2) — NOT part of the library.

Goal of this round: test whether a *small* set of term/syntax-level lemmas lets us
derive several high-level naturality theorems for `equivSentence` **without any new
`induction` on `BoundedFormula`/`Formula`**.

Builds on round 1 (`Scratch/ReconSyntaxKernel.lean`):
`Term.relabel_eq_subst`, `LHom.onTerm_eq_substFunc`, `LHom.onBoundedFormula_eq_mapTermRel`.

This file imports only syntax-level Mathlib.
-/
import Mathlib.ModelTheory.Syntax
import Scratch.ReconSyntaxKernel

open FirstOrder

universe u v u' v' w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {α β : Type*}

/-! ## Part 1: term-level naturality lemmas -/

namespace LHom

/-- Symbol renaming commutes with variable relabeling of terms.  [1 `Term` induction] -/
theorem onTerm_relabel (Φ : L →ᴸ L') (g : α → β) (t : L.Term α) :
    Φ.onTerm (t.relabel g) = (Φ.onTerm t).relabel g := by
  induction t with
  | var a => rfl
  | func f ts ih => simp only [Term.relabel, onTerm, ih]

end LHom

/-! ### Computation rules for the constants-renaming language map -/

@[simp]
theorem lhomWithConstantsMap_onFunction_inl (f : α → β) {n : ℕ} (g : L.Functions n) :
    (L.lhomWithConstantsMap f).onFunction (Sum.inl g) = Sum.inl g := by
  simp only [lhomWithConstantsMap, LHom.sumMap_onFunction, LHom.id_onFunction, Sum.map_inl]
  rfl

@[simp]
theorem lhomWithConstantsMap_onFunction_inr (f : α → β) (c : (constantsOn α).Functions 0) :
    (L.lhomWithConstantsMap f).onFunction (Sum.inr c) = Sum.inr (f c) := by
  simp only [lhomWithConstantsMap, LHom.sumMap_onFunction, LHom.id_onFunction, Sum.map_inr,
    LHom.constantsOnMap]
  rfl

/-- `constantsOn` has no relations, so the relation part of the constants-renaming map is
invisible after `Equiv.sumEmpty`. -/
theorem sumEmpty_lhomWithConstantsMap_onRelation (f : α → β) {n : ℕ}
    (R : (L[[α]]).Relations n) :
    Equiv.sumEmpty (L.Relations n) Empty ((L.lhomWithConstantsMap f).onRelation R) =
      Equiv.sumEmpty (L.Relations n) Empty R := by
  rcases R with R | e
  · rfl
  · exact isEmptyElim e

/-! ### Term-level computation rules for `constantsToVars` -/

@[simp]
theorem Term.constantsToVars_inl {κ : Type*} {n : ℕ} (f : L.Functions n)
    (ts : Fin n → (L[[κ]]).Term α) :
    Term.constantsToVars (Term.func (Sum.inl f) ts) =
      Term.func f fun i => Term.constantsToVars (ts i) := by
  cases n <;> rfl

@[simp]
theorem Term.constantsToVars_inr_zero {κ : Type*} (c : κ)
    (ts : Fin 0 → (L[[κ]]).Term α) :
    Term.constantsToVars (Term.func (l := 0) (Sum.inr c) ts) = Term.var (Sum.inl c) := rfl

@[simp]
theorem Term.constantsToVars_inr_succ {κ : Type*} {n : ℕ}
    (c : (constantsOn κ).Functions (n + 1)) (ts : Fin (n + 1) → (L[[κ]]).Term α) :
    Term.constantsToVars (Term.func (l := n + 1) (Sum.inr c) ts) = isEmptyElim c := by
  obtain ⟨⟩ := c

/-- **The main term-level naturality lemma.**  `constantsToVars` commutes with
`lhomWithConstantsMap`; this is what lets the constant-renaming be pushed through the
"constants to free variables" translation.  [1 `Term` induction] -/
theorem Term.constantsToVars_lhomWithConstantsMap {κ κ' : Type*} (f : κ → κ') {γ : Type*}
    (t : (L[[κ]]).Term γ) :
    Term.constantsToVars ((L.lhomWithConstantsMap f).onTerm t) =
      (Term.constantsToVars t).relabel (Sum.map f (id : γ → γ)) := by
  induction t with
  | var x => rfl
  | @func n fn ts ih =>
    rcases fn with fl | fc
    · cases n with
      | zero =>
        simp only [LHom.onTerm, Term.constantsVarsEquiv_apply, Term.constantsToVars_inl,
          lhomWithConstantsMap_onFunction_inl]
        congr 1
        funext i
        simpa only [Term.constantsVarsEquiv_apply] using ih i
      | succ m =>
        simp only [LHom.onTerm, Term.constantsVarsEquiv_apply, Term.constantsToVars_inl,
          lhomWithConstantsMap_onFunction_inl]
        congr 1
        funext i
        simpa only [Term.constantsVarsEquiv_apply] using ih i
    · cases n with
      | zero =>
        simp only [LHom.onTerm, Term.constantsVarsEquiv_apply, Term.constantsToVars,
          lhomWithConstantsMap_onFunction_inr, Term.relabel, Sum.map_inl, id]
        rfl
      | succ m => obtain ⟨⟩ := fc

/-- `Equiv.sumAssoc` bookkeeping for the naturality of `constantsVarsEquivLeft`. -/
theorem sumAssoc_symm_comp_sumMap {κ κ' γ δ : Type*} (f : κ → κ') :
    (Equiv.sumAssoc κ' γ δ).symm ∘ Sum.map f (id : γ ⊕ δ → γ ⊕ δ) =
      (Sum.map (Sum.map f (id : γ → γ)) (id : δ → δ)) ∘
        (Equiv.sumAssoc κ γ δ).symm := by
  funext x
  rcases x with c | (g | d) <;> rfl

/-- Naturality of `constantsVarsEquivLeft`, the term map used by
`BoundedFormula.constantsVarsEquiv`.  [0 inductions; derives from the `constantsToVars`
lemma above via `Term.relabel_relabel`.] -/
theorem Term.constantsVarsEquivLeft_lhomWithConstantsMap {κ κ' : Type*} (f : κ → κ')
    {γ δ : Type*} (t : (L[[κ]]).Term (γ ⊕ δ)) :
    Term.constantsVarsEquivLeft ((L.lhomWithConstantsMap f).onTerm t) =
      (Term.constantsVarsEquivLeft t).relabel (Sum.map (Sum.map f (id : γ → γ)) (id : δ → δ)) := by
  simp only [Term.constantsVarsEquivLeft_apply, Term.constantsToVars_lhomWithConstantsMap f t,
    Term.relabel_relabel, Function.comp_apply]
  rw [sumAssoc_symm_comp_sumMap]

/-! ## Part 2: formula-level naturality theorems (no `BoundedFormula` induction) -/

/-- The `castLE` in the `all`-slot of `BoundedFormula.relabel` is a *fake* cast
(`0 + n` versus `n + 1` are definitionally equal), so the `h`-slot can be replaced by `id`
pointwise via `castLE_rfl`.  This turns `relabel` into a plain identity-arity `mapTermRel`
and makes it composable with `mapTermRel_mapTermRel`.  [0 inductions] -/
theorem BoundedFormula.relabel_eq_mapTermRel {n : ℕ} (g : α → β ⊕ Fin n) {k : ℕ}
    (φ : L.BoundedFormula α k) :
    φ.relabel g =
      φ.mapTermRel (fun _ t => t.relabel (BoundedFormula.relabelAux g _))
        (fun _ => id) (fun _ => id) := by
  unfold BoundedFormula.relabel
  refine congrArg (fun h => φ.mapTermRel
    (fun _ t => t.relabel (BoundedFormula.relabelAux g _)) (fun _ => id) h) ?_
  funext j X
  exact BoundedFormula.castLE_rfl _ X

/-- Congruence for `BoundedFormula.mapTermRel` in its term/relation maps, for the
identity arity case.  [0 inductions] -/
theorem BoundedFormula.mapTermRel_congr {n : ℕ} {φ : L.BoundedFormula α n}
    {ft ft' : ∀ n, L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin n)}
    {fr fr' : ∀ n, L.Relations n → L'.Relations n}
    (hft : ∀ n t, ft n t = ft' n t) (hfr : ∀ n R, fr n R = fr' n R) :
    φ.mapTermRel ft fr (fun _ => id) = φ.mapTermRel ft' fr' (fun _ => id) := by
  have h1 : ft = ft' := funext fun n => funext (hft n)
  have h2 : fr = fr' := funext fun n => funext (hfr n)
  rw [h1, h2]

namespace LHom

/-- Symbol renaming commutes with arity-preserving variable relabeling of bounded
formulas.  [0 `BoundedFormula` inductions] -/
theorem onBoundedFormula_relabelEquiv (Φ : L →ᴸ L') (e : α ≃ β) {n : ℕ}
    (ψ : L.BoundedFormula α n) :
    Φ.onBoundedFormula (BoundedFormula.relabelEquiv e ψ) =
      BoundedFormula.relabelEquiv e (Φ.onBoundedFormula ψ) := by
  simp only [BoundedFormula.relabelEquiv, BoundedFormula.mapTermRelEquiv, Equiv.coe_fn_mk]
  simp only [LHom.onBoundedFormula_eq_mapTermRel]
  simp only [BoundedFormula.mapTermRel_mapTermRel]
  apply BoundedFormula.mapTermRel_congr (φ := ψ)
  · intro n t
    simp only [Function.comp_apply, Term.relabelEquiv_apply]
    exact LHom.onTerm_relabel Φ (e.sumCongr (_root_.Equiv.refl (Fin n))) t
  · intro n R
    rfl

end LHom

/-- Naturality of `BoundedFormula.constantsVarsEquiv` with respect to the
constants-renaming language map.  [0 `BoundedFormula` inductions] -/
theorem BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap {κ κ' : Type*} (f : κ → κ')
    {γ : Type*} {n : ℕ} (ψ : (L[[κ]]).BoundedFormula γ n) :
    BoundedFormula.constantsVarsEquiv ((L.lhomWithConstantsMap f).onBoundedFormula ψ) =
      (BoundedFormula.constantsVarsEquiv ψ).mapTermRel
        (fun _ t => t.relabel (Sum.map (Sum.map f (id : γ → γ)) id))
        (fun _ => id) (fun _ => id) := by
  simp only [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv, Equiv.coe_fn_mk]
  simp only [LHom.onBoundedFormula_eq_mapTermRel]
  simp only [BoundedFormula.mapTermRel_mapTermRel]
  apply BoundedFormula.mapTermRel_congr (φ := ψ)
  · intro n t
    exact Term.constantsVarsEquivLeft_lhomWithConstantsMap f t
  · intro n R
    exact sumEmpty_lhomWithConstantsMap_onRelation f R

end Language

end FirstOrder
