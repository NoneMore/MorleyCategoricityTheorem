/-
Recon scratch — NOT part of the library.  Investigation artifact for the
"syntax-first kernel" experiment.

Hypothesis under test: a handful of purely syntactic *representation* equalities
lets the semantic layer replace several separate structural inductions (on
`Term` / `BoundedFormula`) by one generic semantic induction kernel,
`BoundedFormula.realize_mapTermRel_id`.

This file deliberately imports ONLY `Mathlib.ModelTheory.Syntax`: every lemma
below is pure syntax and must not mention structures or realization.
-/
import Mathlib.ModelTheory.Syntax

open FirstOrder

universe u v u' v'

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {α β : Type*}

namespace Term

/-- Relabeling a term is substitution of its variables by variables.  This is the
"term-level representation" that turns `realize_relabel` into an instance of
`realize_subst`. -/
theorem relabel_eq_subst (g : α → β) (t : L.Term α) :
    t.relabel g = t.subst (fun a => var (g a)) := by
  induction t with
  | var a => rfl
  | func f ts ih => simp only [relabel, subst, ih]

end Term

namespace LHom

/-- `LHom.onTerm` is `Term.substFunc` along the function symbols themselves.  This is
the "symbol-renaming representation" that turns `realize_onTerm` into an instance of
`realize_substFunc`. -/
theorem onTerm_eq_substFunc (φ : L →ᴸ L') (t : L.Term α) :
    φ.onTerm t = t.substFunc (fun {_} f => (φ.onFunction f).term) := by
  induction t with
  | var a => rfl
  | @func n f ts ih =>
    simp only [onTerm, Term.substFunc, Functions.term, Term.subst, ih]

/-- `LHom.onBoundedFormula` is the identity-arity instance of `BoundedFormula.mapTermRel`.
This is the "formula-level representation" that turns `realize_onBoundedFormula` into an
instance of `realize_mapTermRel_id`.

Note the arity bookkeeping `(fun _ => id)` in the `all` slot: no `castLE`/`liftAt`
coherence appears, because `onBoundedFormula` preserves arities exactly. -/
theorem onBoundedFormula_eq_mapTermRel (φ : L →ᴸ L') {n : ℕ} (ψ : L.BoundedFormula α n) :
    φ.onBoundedFormula ψ =
      ψ.mapTermRel (fun _ => φ.onTerm) (fun _ R => φ.onRelation R) (fun _ => id) := by
  induction ψ with
  | falsum => rfl
  | equal t₁ t₂ => rfl
  | rel R ts => rfl
  | imp _ _ ih1 ih2 => simp only [onBoundedFormula, BoundedFormula.mapTermRel, ih1, ih2]
  | all _ ih => simp only [onBoundedFormula, BoundedFormula.mapTermRel, ih, id]

end LHom

end Language

end FirstOrder
