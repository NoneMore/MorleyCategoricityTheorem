/-
Recon scratch: the bottom-layer primitives that make "syntactic computation +
transport" close.  NOT part of the library; investigation artifact only.
-/
import Mathlib.ModelTheory.Semantics

open FirstOrder FirstOrder.Language FirstOrder.Language.Formula

universe u v

namespace Recon

variable {L : Language.{u, v}} {L' : Language.{u, v}} {L'' : Language.{u, v}}
  {α β γ δ : Type*}

/-! ### Primitive 1: the `LHom` mechanism is a `mapTermRel` instance -/

theorem LHom.onBoundedFormula_eq_mapTermRel (φ : L →ᴸ L') {n : ℕ}
    (f : L.BoundedFormula α n) :
    φ.onBoundedFormula f =
      f.mapTermRel (fun _ => φ.onTerm) (fun _ R => φ.onRelation R) (fun _ => id) := by
  induction f with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp f₁ f₂ ih1 ih2 =>
    simp only [LHom.onBoundedFormula, BoundedFormula.mapTermRel, ih1, ih2]
  | all f ih => simp only [LHom.onBoundedFormula, BoundedFormula.mapTermRel, ih, id]

/-! ### Primitive 2: term reindexing commutes with symbol renaming -/

theorem LHom.onTerm_relabel (φ : L →ᴸ L') (g : γ → δ) (t : L.Term γ) :
    φ.onTerm (t.relabel g) = (φ.onTerm t).relabel g := by
  induction t with
  | var x => rfl
  | func fn ts ih => simp only [Term.relabel, LHom.onTerm, ih]

/-! ### Primitive 3: arity bookkeeping commutes with an arity-preserving `mapTermRel` -/

theorem mapTermRel_id_castLE {L₀ : Language.{u, v}} {L₀' : Language.{u, v}}
    {γ₀ δ₀ : Type*} {m : ℕ} (φ : L₀.BoundedFormula γ₀ m)
    (ft : ∀ n, L₀.Term (γ₀ ⊕ Fin n) → L₀'.Term (δ₀ ⊕ Fin n))
    (fr : ∀ n, L₀.Relations n → L₀'.Relations n)
    (hft : ∀ (k l : ℕ) (hkl : k ≤ l) (t : L₀.Term (γ₀ ⊕ Fin k)),
      ft l (t.relabel (Sum.map id (Fin.castLE hkl))) =
        (ft k t).relabel (Sum.map id (Fin.castLE hkl))) :
    ∀ (n : ℕ) (e : m ≤ n),
      (φ.castLE e).mapTermRel ft fr (fun _ => id) =
        (φ.mapTermRel ft fr (fun _ => id)).castLE e := by
  induction φ with
  | falsum => intro n e; rfl
  | equal t₁ t₂ =>
    intro n e
    simp only [BoundedFormula.castLE, BoundedFormula.mapTermRel]
    rw [hft, hft]
  | rel R ts =>
    intro n e
    simp only [BoundedFormula.castLE, BoundedFormula.mapTermRel]
    congr 1
    funext i
    exact hft _ _ _ _
  | imp f₁ f₂ ih1 ih2 =>
    intro n e
    simp only [BoundedFormula.castLE, BoundedFormula.mapTermRel, ih1, ih2]
  | all f ih =>
    intro n e
    simp only [BoundedFormula.castLE, BoundedFormula.mapTermRel]
    rw [ih (n + 1) (by omega)]
    rfl

/-! ### Primitive 4 (root fix): composition with an arity shift -/

theorem mapTermRel_comp_shift {k : ℕ}
    (ft : ∀ n, L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (k + n)))
    (fr : ∀ n, L.Relations n → L'.Relations n)
    (ft' : ∀ n, L'.Term (β ⊕ Fin n) → L''.Term (γ ⊕ Fin n))
    (fr' : ∀ n, L'.Relations n → L''.Relations n)
    (hft' : ∀ (p q : ℕ) (hpq : p ≤ q) (t : L'.Term (β ⊕ Fin p)),
      ft' q (t.relabel (Sum.map id (Fin.castLE hpq))) =
        (ft' p t).relabel (Sum.map id (Fin.castLE hpq))) :
    ∀ {m : ℕ} (φ : L.BoundedFormula α m),
      (φ.mapTermRel ft fr (fun n => BoundedFormula.castLE (ge_of_eq (add_assoc k n 1)))).mapTermRel
          ft' fr' (fun _ => id)
        = φ.mapTermRel (fun n => ft' (k + n) ∘ ft n) (fun n => fr' n ∘ fr n)
            (fun n => BoundedFormula.castLE (ge_of_eq (add_assoc k n 1))) := by
  intro m φ
  induction φ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp f₁ f₂ ih1 ih2 => simp only [BoundedFormula.mapTermRel, ih1, ih2]
  | all f ih =>
    simp only [BoundedFormula.mapTermRel]
    rw [mapTermRel_id_castLE _ ft' fr' hft']
    rw [ih]
    rfl

/-! ### Primitive 5: term-level naturality of `constantsVarsEquiv` -/

@[simp]
theorem Term.constantsToVars_inl {n : ℕ} (f : L.Functions n)
    (ts : Fin n → L[[γ]].Term α) :
    Term.constantsToVars (Term.func (Sum.inl f) ts) =
      Term.func f fun i => Term.constantsToVars (ts i) := by
  cases n <;> rfl

@[simp]
theorem Term.constantsToVars_inr_zero (c : γ) (ts : Fin 0 → L[[γ]].Term α) :
    Term.constantsToVars (Term.func (l := 0) (Sum.inr c) ts) = Term.var (Sum.inl c) := rfl

@[simp]
theorem Term.constantsToVars_inr_succ {n : ℕ}
    (c : (constantsOn γ).Functions (n + 1)) (ts : Fin (n + 1) → L[[γ]].Term α) :
    Term.constantsToVars (Term.func (l := n + 1) (Sum.inr c) ts) = isEmptyElim c := by
  obtain ⟨⟩ := c

@[simp]
theorem lhomWithConstantsMap_onFunction_inl (f : α → β) {n : ℕ} (g : L.Functions n) :
    (L.lhomWithConstantsMap f).onFunction (n := n) (Sum.inl g) = Sum.inl g := by
  simp only [lhomWithConstantsMap, LHom.sumMap_onFunction, LHom.id_onFunction,
    Sum.map_inl, id]
  rfl

@[simp]
theorem lhomWithConstantsMap_onFunction_inr (f : α → β) (c : (constantsOn α).Functions 0) :
    (L.lhomWithConstantsMap f).onFunction (n := 0) (Sum.inr c) = Sum.inr (f c) := by
  simp only [lhomWithConstantsMap, LHom.sumMap_onFunction, LHom.id_onFunction,
    Sum.map_inr, LHom.constantsOnMap, id]
  rfl

theorem Term.constantsVarsEquiv_onTerm (f : α → β) (t : L[[α]].Term γ) :
    Term.constantsVarsEquiv ((L.lhomWithConstantsMap f).onTerm t) =
      (Term.constantsVarsEquiv t).relabel (Sum.map f (id : γ → γ)) := by
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

end Recon
