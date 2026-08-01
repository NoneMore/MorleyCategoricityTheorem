import Mathlib.ModelTheory.Topology.Types
import MorleyCategoricityTheorem.ModelTheory.Types

open FirstOrder Language Theory CompleteType

universe u v w w' x

namespace FirstOrder

namespace Language

namespace BoundedFormula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {α : Type w'}

/-- Every bounded formula over a parameter set is, up to realization, a substitution instance of a
constant-free bounded formula in finitely many extra variables. -/
lemma exists_fin_params {B : Set M} (k : ℕ) (φ : (L[[B]]).BoundedFormula α k) :
    ∃ n : ℕ, ∃ b : Fin n → B, ∃ φ' : L.BoundedFormula (α ⊕ Fin n) k,
      ∀ v : α → M, ∀ xs : Fin k → M,
        φ.Realize v xs ↔ φ'.Realize (Sum.elim v (fun i => (b i : M))) xs := by
  classical
  let φ₀ : L.BoundedFormula (B ⊕ α) k := BoundedFormula.constantsVarsEquiv φ
  let S : Finset B := φ₀.freeVarFinset.toLeft
  let n : ℕ := S.card
  let e : S ≃ Fin n := Finset.equivFin S
  let b : Fin n → B := fun i => (e.symm i : B)
  let f : φ₀.freeVarFinset → (α ⊕ Fin n) := fun z =>
    match h : z.1 with
    | Sum.inl x => Sum.inr (e ⟨x, (Finset.mem_toLeft).mpr (h ▸ z.2)⟩)
    | Sum.inr w => Sum.inl w
  refine ⟨n, b, BoundedFormula.restrictFreeVar φ₀ f, fun v xs => ?_⟩
  simp_rw [φ₀]
  rw [BoundedFormula.realize_restrictFreeVar (Sum.elim (fun x : B => (L.con x : M)) v) (by
    rintro ⟨z, hz⟩
    cases z <;> simp [f, b]), BoundedFormula.realize_constantsVarsEquiv]

end BoundedFormula

namespace LHom

open BoundedFormula

variable {L L' : Language}

/-- Applying a language homomorphism to a term commutes with relabeling its variables. -/
lemma onTerm_relabel {α β : Type*} (g : L →ᴸ L') (t : L.Term α) (h : α → β) :
    g.onTerm (t.relabel h) = (g.onTerm t).relabel h := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

/-- Applying a language homomorphism to a term commutes with substituting its variables by
terms. -/
lemma onTerm_subst {α β : Type*} (g : L →ᴸ L') (t : L.Term α) (f : α → L.Term β) :
    g.onTerm (t.subst f) = (g.onTerm t).subst (g.onTerm ∘ f) := by
  induction t with
  | var => rfl
  | func _ _ ih => simp [ih]

/-- `onBoundedFormula` is the `mapTermRel` whose term map is `onTerm` and relation map is
`onRelation`. -/
lemma onBoundedFormula_eq_mapTermRel {α : Type*} {n : ℕ} (g : L →ᴸ L')
    (φ : L.BoundedFormula α n) :
    g.onBoundedFormula φ =
      φ.mapTermRel (fun _ t => g.onTerm t) (fun _ R => g.onRelation R) (fun _ => id) := by
  induction φ with
  | falsum => rfl
  | equal => rfl
  | rel => rfl
  | imp _ _ ih1 ih2 => simp [mapTermRel, ih1, ih2]
  | all _ ih => simp [mapTermRel, ih]

/-- Applying a language homomorphism to a bounded formula commutes with substituting variables
by terms. -/
lemma onBoundedFormula_subst {α β : Type*} {n : ℕ} (g : L →ᴸ L')
    (φ : L.BoundedFormula α n) (f : α → L.Term β) :
    (g.onBoundedFormula φ).subst (g.onTerm ∘ f) = g.onBoundedFormula (φ.subst f) := by
  have hft : ∀ (n : ℕ) (t : L.Term (α ⊕ Fin n)),
      (g.onTerm t).subst (Sum.elim (Term.relabel Sum.inl ∘ g.onTerm ∘ f) (var ∘ Sum.inr)) =
      g.onTerm (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr))) := by
    intro n t
    rw [onTerm_subst]
    congr 1
    funext z
    cases z with
    | inl x => simp [onTerm_relabel]
    | inr i => simp
  calc
    (g.onBoundedFormula φ).subst (g.onTerm ∘ f)
        = φ.mapTermRel
            (fun n t => g.onTerm (t.subst (Sum.elim (Term.relabel Sum.inl ∘ f) (var ∘ Sum.inr))))
            (fun _ R => g.onRelation R) (fun _ => id) := by
          rw [BoundedFormula.subst, onBoundedFormula_eq_mapTermRel]
          rw [mapTermRel_mapTermRel]
          congr
          · funext n t
            simpa using hft n t
    _ = g.onBoundedFormula (φ.subst f) := by
          rw [BoundedFormula.subst, onBoundedFormula_eq_mapTermRel]
          rw [mapTermRel_mapTermRel]
          congr

/-- Applying a language homomorphism to a formula commutes with substituting variables by
terms. -/
lemma onFormula_subst {α β : Type*} (g : L →ᴸ L')
    (φ : L.Formula α) (f : α → L.Term β) :
    (g.onFormula φ).subst (g.onTerm ∘ f) = g.onFormula (φ.subst f) := by
  simpa [onFormula] using onBoundedFormula_subst (L := L) (L' := L') g φ f

end LHom

namespace Theory

namespace CompleteType

variable {L : Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]
variable {α : Type w'}

omit [Nonempty M] in
/-- Every formula over a parameter set is, up to realization, a substitution instance of a
constant-free formula in finitely many extra variables. -/
lemma formula_exists_fin_params {B : Set M} (φ : (L[[B]]).Formula α) :
    ∃ n : ℕ, ∃ b : Fin n → B, ∃ φ' : L.Formula (α ⊕ Fin n),
      ∀ v : α → M, φ.Realize v ↔ φ'.Realize (Sum.elim v (fun i => (b i : M))) := by
  classical
  rcases BoundedFormula.exists_fin_params (L := L) (M := M) (B := B) (α := α) 0 φ with
    ⟨n, b, φ', h⟩
  exact ⟨n, b, φ', fun v => h v default⟩

/-- Realization of a formula is invariant under having the same complete type, possibly in
different models. -/
lemma realize_iff_of_typeOf_eq {L : Language.{u, v}} {T : L.Theory}
    {M : Type w} [L.Structure M] [Nonempty M] [M ⊨ T]
    {N : Type x} [L.Structure N] [Nonempty N] [N ⊨ T]
    {β : Type w'} {v : β → M} {w : β → N} (h : T.typeOf v = T.typeOf w) (φ : L.Formula β) :
    φ.Realize v ↔ φ.Realize w := by
  rw [← CompleteType.formula_mem_typeOf (M := M) (T := T)]
  rw [h]
  rw [CompleteType.formula_mem_typeOf (M := N) (T := T)]

/-- A formula isolating a type is satisfied by exactly the tuples whose type is that type. -/
lemma typeOf_eq_of_isolating_witness {L : Language.{u, v}} {T : L.Theory} {β : Type w'}
    (ψ : L.Formula β) {p : T.CompleteType β} (hisol : p.IsolatedBy ψ)
    {N : Type x} [L.Structure N] [Nonempty N] [N ⊨ T] {v : β → N}
    (hv : ψ.Realize v) : T.typeOf v = p := by
  exact hisol.2 (T.typeOf v) ((CompleteType.formula_mem_typeOf).mpr hv)

/-- Realizing a formula over `A` after substituting a tuple of parameters from `B` agrees with
realizing the corresponding formula over `B`, provided the map `f : A → B` is compatible with
parameter realization (which is automatic for the inclusion of `A` into `B`). -/
lemma realize_subst_params {L : Language.{u, v}} {M : Type w} [L.Structure M]
    {A B : Set M} (f : A → B) (hf : ∀ a : A, (f a : M) = (a : M))
    {α : Type w'} {β : Type*} (φ : (L[[A]]).Formula (α ⊕ β)) (b : β → B) (v : α → M) :
    Formula.Realize
      ((LHom.onFormula (L.lhomWithConstantsMap f) φ).subst
        (Sum.elim (Term.var : α → (L[[B]]).Term α) (fun i => (L.con (b i)).term))) v ↔
      φ.Realize (Sum.elim v (fun i => (b i : M))) := by
  classical
  haveI : (L.lhomWithConstantsMap f).IsExpansionOn M := by
    haveI : (LHom.constantsOnMap f).IsExpansionOn M := by
      exact constantsOnMap_isExpansionOn (by funext a; exact hf a)
    exact LHom.sumMap_isExpansionOn (LHom.id L) (LHom.constantsOnMap f) M
  unfold Formula.Realize
  rw [BoundedFormula.realize_subst]
  have hsum : (fun z : α ⊕ β =>
      Term.realize v (Sum.elim (Term.var : α → (L[[B]]).Term α)
        (fun i => (L.con (b i)).term) z)) =
      Sum.elim v (fun i => (b i : M)) := by
    funext z; cases z with
    | inl x => simp [Term.realize_var]
    | inr i => simp
  rw [hsum]
  simpa [Formula.Realize] using
    (LHom.realize_onFormula (M := M) (v := Sum.elim v (fun i => (b i : M)))
      (L.lhomWithConstantsMap f) φ)

namespace Formula

/-- Relabel the free variables of a formula: the left variables occurring in `used` become right
variables indexed by `used`, while the right variables are kept on the left. -/
def freeVarLeftRelabel {L : Language.{u, v}} {α β : Type*} [DecidableEq (α ⊕ β)]
    (φ : L.Formula (α ⊕ β)) (used : Finset α)
    (hcover : φ.freeVarFinset.toLeft ⊆ used) :
    φ.freeVarFinset → (β ⊕ used) :=
  fun a => match h : a.1 with
    | Sum.inl x => Sum.inr ⟨x, by
        exact hcover ((Finset.mem_toLeft).mpr (by simpa [h] using a.2))⟩
    | Sum.inr i => Sum.inl i

/-- Existentially close the free `α`-variables of a formula in `α ⊕ β`, yielding a formula in
the remaining `β` variables. -/
noncomputable def existsLeft {L : Language.{u, v}} {α β : Type*} [DecidableEq (α ⊕ β)]
    (φ : L.Formula (α ⊕ β)) : L.Formula β :=
  Formula.iExs φ.freeVarFinset.toLeft
    (φ.restrictFreeVar (freeVarLeftRelabel (L := L) φ φ.freeVarFinset.toLeft (by
      intro x hx
      exact hx)))

/-- Existential closure over the free `α`-variables commutes with realization: `existsLeft φ`
holds at `v` exactly when some assignment to the free `α`-variables makes `φ` hold, with the
remaining `α`-variables interpreted by `ext`. -/
lemma realize_existsLeft {L : Language.{u, v}} {M : Type w} [L.Structure M]
    {α β : Type*} [DecidableEq α] [DecidableEq (α ⊕ β)] (φ : L.Formula (α ⊕ β))
    (v : β → M) (ext : α → M) :
    (Formula.existsLeft φ).Realize v ↔
      ∃ g : φ.freeVarFinset.toLeft → M, φ.Realize
        (Sum.elim (fun x => if hx : x ∈ φ.freeVarFinset.toLeft then g ⟨x, hx⟩ else ext x) v) := by
  classical
  simp only [Formula.existsLeft]
  rw [Formula.realize_iExs]
  have hcv : ∀ (g : φ.freeVarFinset.toLeft → M) (a : φ.freeVarFinset),
      (Sum.elim v g) (freeVarLeftRelabel (L := L) φ φ.freeVarFinset.toLeft (Finset.toLeft_subset_toLeft fun ⦃x⦄ a ↦ a) a) =
        (Sum.elim (fun x => if hx : x ∈ φ.freeVarFinset.toLeft then g ⟨x, hx⟩ else ext x) v) a.1 := by
    intro g a
    rcases a with ⟨z, hz⟩
    cases z with
    | inl x =>
      simp [freeVarLeftRelabel, hz]
    | inr i =>
      simp [freeVarLeftRelabel]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, (BoundedFormula.realize_restrictFreeVar (φ := φ)
      (f := freeVarLeftRelabel (L := L) φ φ.freeVarFinset.toLeft (by
        intro x hx; exact hx))
      (v := Sum.elim v g)
      (v' := Sum.elim (fun x => if hx : x ∈ φ.freeVarFinset.toLeft then g ⟨x, hx⟩ else ext x) v)
      (xs := default) (hcv g)).1 hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, (BoundedFormula.realize_restrictFreeVar (φ := φ)
      (f := freeVarLeftRelabel (L := L) φ φ.freeVarFinset.toLeft (by
        intro x hx; exact hx))
      (v := Sum.elim v g)
      (v' := Sum.elim (fun x => if hx : x ∈ φ.freeVarFinset.toLeft then g ⟨x, hx⟩ else ext x) v)
      (xs := default) (hcv g)).2 hg⟩

end Formula

/-- The joint type `tp^A (a ⊕ b)` is isolated when `tp^B a` is isolated by a formula which is a
substitution instance of `φ'` and `tp^A b` is isolated by `ψ`. -/
lemma joint_isolated
    {A B : Set M} (hAB : A ⊆ B) (a : α → M)
    (φ : (L[[B]]).Formula α)
    (hφisol : ((L[[B]].completeTheory M).typeOf a).IsolatedBy φ)
    {n : ℕ} (b : Fin n → B) (φ' : L.Formula (α ⊕ Fin n))
    (hφ' : ∀ v : α → M, φ.Realize v ↔ φ'.Realize (Sum.elim v (fun i => (b i : M))))
    (ψ : (L[[A]]).Formula (Fin n))
    (hψisol : ((L[[A]].completeTheory M).typeOf (fun i => (b i : M))).IsolatedBy ψ) :
    ((L[[A]].completeTheory M).typeOf (Sum.elim a (fun i => (b i : M)))).IsIsolated := by
  -- Refactoring plan: once `joint_isolated_iff_of_realizedBy` is proved, separate this argument
  -- into conditional isolation and the general joint-isolation theorem. Set
  -- `d := fun i ↦ (b i : M)`. The hypothesis `hψisol` immediately isolates the marginal type
  -- `tp^A(d)`. To isolate the conditional type of `a` over `d`, map `φ'` into `L[[A]]`, swap
  -- the `α` and `Fin n` variables, and turn the `Fin n` variables into named constants. The
  -- essential part of the proof below then shows that this formula isolates
  -- `typeOfOverType (T := L[[A]].completeTheory M) d a`: a distinguishing formula produces,
  -- after existentially closing the `α`-variables and transferring along `tp^A(d)`, a tuple
  -- `a''` in `M`; `hφ'` and `hφisol` give `tp^B(a'') = tp^B(a)`, contradicting the
  -- distinction because `A ⊆ B` and every entry of `d` lies in `B`. Finally, a right-handed
  -- corollary of `joint_isolated_iff_of_realizedBy`, obtained using invariance under `Sum.swap`,
  -- combines the isolated marginal and conditional types. This would replace the direct
  -- construction of `Θ` and its joint-type bookkeeping, while retaining the hard conditional
  -- isolation argument as a reusable helper lemma.
  classical
  let T : (L[[A]]).Theory := L[[A]].completeTheory M
  let c : α ⊕ Fin n → M := Sum.elim a (fun i => (b i : M))
  let φ'' : (L[[A]]).Formula (α ⊕ Fin n) := LHom.onFormula (L.lhomWithConstants A) φ'
  let Θ : (L[[A]]).Formula (α ⊕ Fin n) := ψ.relabel Sum.inr ⊓ φ''
  rw [isIsolated_iff_typesWith_eq_singleton]
  refine ⟨Θ, ?_⟩
  rw [singleton_eq_typesWith_iff]
  constructor
  · rw [CompleteType.mem_typeOf]
    have hΘc : Θ.Realize c := by
      rw [show Θ = ψ.relabel Sum.inr ⊓ φ'' from rfl]
      rw [Formula.realize_inf]
      constructor
      · rw [Formula.realize_relabel]
        change ψ.Realize (fun i : Fin n => (b i : M))
        exact (CompleteType.formula_mem_typeOf).mp hψisol.1
      · rw [show φ'' = LHom.onFormula (L.lhomWithConstants A) φ' from rfl]
        rw [LHom.realize_onFormula]
        exact (hφ' a).mp ((CompleteType.formula_mem_typeOf).mp hφisol.1)
    simpa using hΘc
  · intro χ hχ
    let χf : (L[[A]]).Formula (α ⊕ Fin n) := Formula.equivSentence.symm χ
    rw [models_sentence_iff]
    intro N
    rw [Sentence.realize_imp]
    intro hΘN
    letI : (L[[A]]).Structure ↑N := (L[[A]].lhomWithConstants (α ⊕ Fin n)).reduct ↑N
    letI : L.Structure ↑N := (L.lhomWithConstants A).reduct ↑N
    haveI : (L[[A]].lhomWithConstants (α ⊕ Fin n)).IsExpansionOn ↑N :=
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    haveI : (L.lhomWithConstants A).IsExpansionOn ↑N :=
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩
    haveI : ↑N ⊨ T :=
      (LHom.onTheory_model (L[[A]].lhomWithConstants (α ⊕ Fin n)) T).1 inferInstance
    let v : α ⊕ Fin n → ↑N := fun x => ((L[[A]]).con x : ↑N)
    have hΘv : Θ.Realize v := by
      simpa [v] using (Formula.realize_equivSentence ↑N Θ).1 hΘN
    let u : α → ↑N := v ∘ Sum.inl
    let w : Fin n → ↑N := v ∘ Sum.inr
    have hΘred : (ψ.relabel Sum.inr ⊓ φ'').Realize v := by simpa [Θ] using hΘv
    have hφ''v : φ''.Realize v := ((Formula.realize_inf).1 hΘred).2
    have hψw : ψ.Realize w := by
      have h1 : (ψ.relabel Sum.inr).Realize v := ((Formula.realize_inf).1 hΘred).1
      rw [Formula.realize_relabel] at h1
      simpa [w] using h1
    have htype_w : T.typeOf w = T.typeOf (fun i : Fin n => (b i : M)) := by
      exact typeOf_eq_of_isolating_witness (T := T) ψ hψisol hψw
    by_contra hnot
    have hχnot_v : (χf.not).Realize v := by
      rw [Formula.realize_not]
      intro hχv
      exact hnot ((FirstOrder.Language.Formula.realize_equivSentence_symm_con
        (L := L[[A]]) (α := α ⊕ Fin n) (M := ↑N) χ).1 hχv)
    let φχ : (L[[A]]).Formula (α ⊕ Fin n) := φ'' ⊓ χf.not
    let ξ : (L[[A]]).Formula (Fin n) := Formula.existsLeft φχ
    have hφχv : φχ.Realize v := by
      rw [show φχ = φ'' ⊓ χf.not from rfl]
      rw [Formula.realize_inf]
      exact ⟨hφ''v, hχnot_v⟩
    have hξw : ξ.Realize w := by
      change (Formula.existsLeft φχ).Realize w
      rw [Formula.realize_existsLeft (L := L[[A]]) (φ := φχ) (v := w) (ext := u)]
      refine ⟨fun sx => u sx.1, ?_⟩
      have hv : Sum.elim (fun x : α =>
          if hx : x ∈ φχ.freeVarFinset.toLeft then u (⟨x, hx⟩ : φχ.freeVarFinset.toLeft) else u x) w = v := by
        funext z
        cases z with
        | inl x => simp [u]
        | inr i => rfl
      rw [hv]
      exact hφχv
    have hξb : ξ.Realize (fun i : Fin n => (b i : M)) :=
      (realize_iff_of_typeOf_eq (T := T) htype_w.symm ξ).2 hξw
    change (Formula.existsLeft φχ).Realize (fun i : Fin n => (b i : M)) at hξb
    rw [Formula.realize_existsLeft (L := L[[A]]) (φ := φχ)
      (v := fun i : Fin n => (b i : M))
      (ext := fun _ : α => Classical.choice inferInstance)] at hξb
    rcases hξb with ⟨g, hξb'⟩
    let a'' : α → M := fun x =>
      if hx : x ∈ φχ.freeVarFinset.toLeft then g ⟨x, hx⟩ else Classical.choice inferInstance
    have hξb'' : (φ'' ⊓ χf.not).Realize (Sum.elim a'' (fun i : Fin n => (b i : M))) := by
      simpa [a'', φχ] using hξb'
    rw [Formula.realize_inf] at hξb''
    rcases hξb'' with ⟨hφ''b, hχnotb⟩
    have hφa'' : φ.Realize a'' := by
      have h1 : φ'.Realize (Sum.elim a'' (fun i : Fin n => (b i : M))) :=
        (LHom.realize_onFormula (L.lhomWithConstants A) φ').1 hφ''b
      exact (hφ' a'').mpr h1
    have htp : (L[[B]].completeTheory M).typeOf a'' = (L[[B]].completeTheory M).typeOf a :=
      typeOf_eq_of_isolating_witness (T := L[[B]].completeTheory M) φ hφisol hφa''
    let χnotB : (L[[B]]).Formula α :=
      (LHom.onFormula (L.lhomWithConstantsMap (Set.inclusion hAB)) (χf.not)).subst
        (Sum.elim (Term.var : α → (L[[B]]).Term α) (fun i : Fin n => (L.con (b i)).term))
    have hχnotB_a'' : χnotB.Realize a'' :=
      (realize_subst_params (L := L) (M := M) (Set.inclusion hAB)
        (by intro x; rfl) (φ := χf.not) b a'').2 hχnotb
    have hχnotB_a : χnotB.Realize a :=
      (realize_iff_of_typeOf_eq (T := L[[B]].completeTheory M) htp χnotB).1 hχnotB_a''
    have hχnotc : (χf.not).Realize (Sum.elim a (fun i : Fin n => (b i : M))) :=
      (realize_subst_params (L := L) (M := M) (Set.inclusion hAB)
        (by intro x; rfl) (φ := χf.not) b a).1 hχnotB_a
    have hχc : χf.Realize (Sum.elim a (fun i : Fin n => (b i : M))) :=
      (CompleteType.mem_typeOf).mp hχ
    exact (Formula.realize_not).1 hχnotc hχc

/-- Isolation is transitive from a larger parameter set to a smaller one when finite tuples from
the larger set have isolated types over the smaller set. -/
theorem isIsolated_typeOf_trans'
    {L : Language.{u, v}} {M : Type w} [L.Structure M] [Nonempty M]
    {A B : Set M} (hAB : A ⊆ B) {α : Type w'} (a : α → M)
    (hB : ∀ (n : ℕ) (b : Fin n → B),
      ((L[[A]].completeTheory M).typeOf (fun i ↦ (b i : M))).IsIsolated)
    (ha : ((L[[B]].completeTheory M).typeOf a).IsIsolated) :
    ((L[[A]].completeTheory M).typeOf a).IsIsolated := by
  classical
  rcases ha with ⟨φ, hφisol⟩
  rcases formula_exists_fin_params (L := L) (M := M) φ with ⟨n, b, φ', hφ'⟩
  rcases hB n b with ⟨ψ, hψisol⟩
  have hj : ((L[[A]].completeTheory M).typeOf (Sum.elim a (fun i => (b i : M)))).IsIsolated :=
    joint_isolated (L := L) (M := M) hAB a φ hφisol b φ' hφ' ψ hψisol
  exact isIsolated_typeOf_left (T := L[[A]].completeTheory M) a (fun i => (b i : M)) hj

end CompleteType

end Theory

end Language

end FirstOrder
