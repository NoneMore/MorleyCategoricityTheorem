/-
Recon scratch — NOT part of the library.  Investigation artifact for the
"syntax-first kernel" experiment.

Part 2: re-derive the three semantic commutation theorems **without any
`induction`/`cases` on `Term` or `BoundedFormula`**, using only
* the syntax-only representation lemmas from `Scratch/ReconSyntaxKernel.lean`,
* the existing generic semantic kernels `Term.realize_subst`,
  `Term.realize_substFunc`, `BoundedFormula.realize_mapTermRel_id`,
* `IsExpansionOn.map_onFunction` / `IsExpansionOn.map_onRelation`.

The kernel lemmas below are deliberately name-suffixed: Mathlib already owns
`Term.realize_relabel`, `LHom.realize_onTerm`, `LHom.realize_onBoundedFormula`,
and this scratch file does not attempt to restate them in place.

`Scratch/` is not a Lake library, so the cross-file import needs an explicit
root.  From the repository root:

```
lake env lean -R . -o Scratch/ReconSyntaxKernel.olean \
  -i Scratch/ReconSyntaxKernel.ilean Scratch/ReconSyntaxKernel.lean
lake env sh -c 'export LEAN_PATH="$LEAN_PATH:."; \
  lean -R . -o Scratch/ReconSemanticsKernel.olean \
  -i Scratch/ReconSemanticsKernel.ilean Scratch/ReconSemanticsKernel.lean'
```
-/

import Mathlib.ModelTheory.Semantics
import Scratch.ReconSyntaxKernel

open FirstOrder FirstOrder.Language

universe u v u' v' w

namespace FirstOrder

namespace Language

variable {L : Language.{u, v}} {L' : Language.{u', v'}} {M : Type w}
variable [L.Structure M] [L'.Structure M]

namespace Term

/-- `Term.realize_relabel`, re-derived from the syntax lemma `relabel_eq_subst` and the
generic kernel `Term.realize_subst`. -/
theorem realize_relabel_kernel {α β : Type*} (t : L.Term α) (g : α → β) (v : β → M) :
    (t.relabel g).realize v = t.realize (v ∘ g) := by
  rw [Term.relabel_eq_subst, Term.realize_subst]
  rfl

end Term

namespace LHom

/-- `LHom.realize_onTerm`, re-derived from the syntax lemma `onTerm_eq_substFunc` and the
generic kernel `Term.realize_substFunc`. -/
theorem realize_onTerm_kernel {α : Type*} (φ : L →ᴸ L') [φ.IsExpansionOn M] (t : L.Term α)
    (v : α → M) : (φ.onTerm t).realize v = t.realize v := by
  rw [LHom.onTerm_eq_substFunc]
  refine Term.realize_substFunc (fun {_} f y => ?_) v t
  simp only [Functions.term, Term.realize_func, Term.realize_var]
  exact (IsExpansionOn.map_onFunction (ϕ := φ) f y).symm

/-- `LHom.realize_onBoundedFormula`, re-derived from the syntax lemma
`onBoundedFormula_eq_mapTermRel` and the generic kernel
`BoundedFormula.realize_mapTermRel_id`. -/
theorem realize_onBoundedFormula_kernel {α : Type*} (φ : L →ᴸ L') [φ.IsExpansionOn M] {n : ℕ}
    (ψ : L.BoundedFormula α n) (v : α → M) (xs : Fin n → M) :
    (φ.onBoundedFormula ψ).Realize v xs ↔ ψ.Realize v xs := by
  rw [LHom.onBoundedFormula_eq_mapTermRel]
  exact BoundedFormula.realize_mapTermRel_id
    (fun m t ys => LHom.realize_onTerm_kernel φ t (Sum.elim v ys))
    (fun m R x => IsExpansionOn.map_onRelation (ϕ := φ) R x)

end LHom

end Language

end FirstOrder
