import Mathlib.ModelTheory.Definability
import Mathlib.ModelTheory.Satisfiability
import MorleyCategoricityTheorem.ModelTheory.LanguageMap
import MorleyCategoricityTheorem.ModelTheory.ElementaryChain
import MorleyCategoricityTheorem.ModelTheory.ElementaryMaps

/-!
# Large models without small infinite definable sets

This file states the existence of large models in which every parameter-definable
unary set is either finite or of full cardinality.

## Main results

- `Theory.exists_elementaryExtension_card_eq_with_full_unary_realizations`:
  one-step elementary extension of cardinality `κ` that fully realizes every
  infinite unary formula with parameters from the base model.
- `Theory.exists_large_model_no_small_infinite_definable_sets`: for a countable
  language and an infinite theory, every uncountable cardinal admits a model with
  no intermediate infinite definable sets.
-/

universe u v w z

namespace FirstOrder

namespace Language

open scoped Cardinal

def UnaryDefinablyFull
    (L : Language.{u, v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ (A X : Set M), A.Definable₁ L X → X.Infinite → #X = #M

def DefinablyFull (L : Language.{u,v}) (M : Type w) [L.Structure M] : Prop :=
  ∀ (A : Set M) {n : ℕ} (S : Set (Fin n → M)), A.Definable L S →
    S.Infinite → #S = #M

theorem definablyFull_of_unary
    {L : Language.{u, v}} {M : Type w}
    [L.Structure M] [Infinite M]
    (h : UnaryDefinablyFull L M) :
    DefinablyFull L M := by
  simp [UnaryDefinablyFull, DefinablyFull] at ⊢ h
  intro A n S hSD hSI
  let P (i : Fin n) := (fun x : Fin n → M ↦ x i) '' S
  have hP : ∃ (i : Fin n), (P i).Infinite := by
    contrapose! hSI
    exact Set.forall_finite_image_eval_iff.mp hSI
  rcases hP with ⟨i,hPiI⟩
  have hPiD : A.Definable₁ L (P i) := by
    simp only [P, Set.Definable₁]
    convert hSD.image_comp fun (_ : Fin 1) ↦ i
    ext x; simp [funext_iff]
  specialize h A (P i) hPiD hPiI
  apply le_antisymm
  · trans #(Fin n → M)
    · exact Cardinal.mk_set_le S
    · rw [Cardinal.mk_pi, Cardinal.prod_const]
      simpa using Cardinal.power_nat_le (Cardinal.aleph0_le_mk M)
  · simpa [← h] using Cardinal.mk_image_le

namespace Formula

variable {L : Language.{u, v}} {M : Type*} [L.Structure M]

def finOneRealizationsEquiv (φ : L.Formula (Fin 1)) :
      {x : Fin 1 → M | φ.Realize x} ≃
        {x : M | φ.Realize fun _ ↦ x} := by
  refine (Equiv.funUnique (Fin 1) M).subtypeEquiv ?_
  intro v
  simp
  congr!

end Formula

namespace Theory

open Cardinal Set

variable {L : Language.{u, v}} (T : L.Theory)

/-- One-step growth: given a model `M` of cardinality `κ`, there is an elementary
extension `N` of the same cardinality such that every infinite unary formula with
parameters in `M` has `κ` many realizations in `N`. -/
theorem exists_elementaryExtension_card_eq_with_full_unary_realizations
    {κ : Cardinal.{w}} (M : ModelType.{u, v, w} T) (hM : #M = κ)
    (hκ : ℵ₀ ≤ κ)
    (hL : Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ) :
    ∃ (N : ModelType.{u, v, w} T) (e : M ↪ₑ[L] N),
      #N = κ ∧
        ∀ {β : Type z} (ψ : L.Formula (β ⊕ Fin 1)) (b : β → M),
          Set.Infinite {x : Fin 1 → M | ψ.Realize (Sum.elim b x)} →
            #({x : Fin 1 → N | ψ.Realize (Sum.elim (e ∘ b) x)}) = κ := by
  classical
  let F := { φ : L[[M]].Formula (Fin 1) // Set.Infinite {x : M | φ.Realize fun _ ↦ x}}
  have hFcard : #F ≤ Cardinal.lift.{max u v} κ := by
    calc
      #F ≤ #(L[[M]].Formula (Fin 1)) := Cardinal.mk_subtype_le _
      _ ≤ #(Σ n, L[[M]].BoundedFormula (Fin 1) n) :=
        Cardinal.mk_le_of_injective
          (f := fun φ ↦ (⟨0, φ⟩ : Σ n, L[[M]].BoundedFormula (Fin 1) n))
          (@sigma_mk_injective ℕ (fun n ↦ L[[M]].BoundedFormula (Fin 1) n) 0)
      _ ≤ max ℵ₀
          (Cardinal.lift.{max (max u w) v} #(Fin 1) +
            Cardinal.lift.{0} L[[M]].card) :=
        BoundedFormula.card_le
      _ ≤ _ := by
        simpa [hM] using
          ⟨hκ, add_le_of_le (aleph0_le_lift.mpr hκ)
            (one_le_lift_iff.mpr (one_le_aleph0.trans hκ))
            (add_le_of_le (aleph0_le_lift.mpr hκ) hL le_rfl)⟩
  let I := κ.out
  let fL := L[[M]].lhomWithConstants (F × I)
  let L' := L[[M]][[F × I]]
  have hL'card : Cardinal.lift.{w} L'.card ≤ Cardinal.lift.{max u v w} κ := by
    simp [L']
    rw [Cardinal.lift_id'.{w, max u v}, Cardinal.lift_umax.{w, max u v}]
    refine add_le_of_le (aleph0_le_lift.mpr hκ) ?_ ?_
    · exact add_le_of_le (aleph0_le_lift.mpr hκ) hL (le_of_eq (congrArg _ hM))
    · refine mul_le_of_le (aleph0_le_lift.mpr hκ) hFcard ?_
      simp [I]
  let subst : F → I → L[[M]][[F × I]].Sentence :=
    fun φ i => (fL.onFormula φ.1).subst (fun _ => (L[[M]].con (φ,i)).term)
  let T₁ := fL.onTheory (L.elementaryDiagram M)
  let T₂ (S : Set (F × I)) := (fun p : F × I => subst p.1 p.2) '' S
  let T₃ (S : Set (F × I)) := ⋃ φ : F,
    L[[M]].distinctConstantsTheory (S ∩ { p : F × I | p.1 = φ })
  let Γ (s : Finset (F × I)) : L'.Theory :=
    T₁ ∪ T₂ s ∪ T₃ s
  have hΓ (s : Finset (F × I)): (Γ s).IsSatisfiable := by
    let sφ : Finset F := s.image Prod.fst
    let sφi (φ : F) : Finset I := ({v : F × I | v ∈ s ∧ v.1 = φ}.image Prod.snd).toFinset
    have hsφ : ∀ v ∈ s, v.1 ∈ sφ := by
      simp [sφ]
      intro φ i h
      exists i
    have hsφi : ∀ v ∈ s, v.2 ∈ sφi v.1 := by simp [sφi]
    let rs : F → Set M := fun φ => {x | (φ.1).Realize fun _ ↦ x}
    have hrs : ∀ φ ∈ sφ, (rs φ).Infinite := fun φ _ => φ.2
    let valOn : s → M := fun v => by
      let f := (hrs (v.1).1 (hsφ v v.2)).natEmbedding
      let n := (((sφi (v.1).1).equivFin ⟨(v.1).2,hsφi v v.2⟩).toNat)
      exact (f n).1
    have hrealize : ∀ (v : s), v.1.1.1.Realize fun _ ↦ valOn v := by
      intro v
      change valOn v ∈ rs v.1.1
      simp [valOn, rs]
    have hdistinct (φ : F) (i j : I)
        (hi : (φ,i) ∈ s) (hj : (φ,j) ∈ s)
        (hval : valOn ⟨(φ,i),hi⟩ = valOn ⟨(φ,j),hj⟩) : i = j := by
      simp [valOn] at hval
      apply Subtype.ext at hval
      apply (hrs φ (hsφ (φ, i) hi)).natEmbedding.injective  at hval
      apply Fin.ext at hval
      apply (sφi φ).equivFin.injective at hval
      simpa using hval
    letI : Inhabited M := Classical.inhabited_of_nonempty inferInstance
    let val : F × I → M := Function.extend ((↑) : s → F × I) valOn default
    have hval (v : s) : val v = valOn v := by simp [val]
    letI : (constantsOn (F × I)).Structure M := constantsOn.structure val
    have hcon (p : F × I) : (L[[M]].con p : M) = val p := rfl
    have hT₁ : M ⊨ T₁ := (LHom.onTheory_model fL (L.elementaryDiagram ↑M)).mpr model_completeTheory
    have hT₂ : M ⊨ T₂ s := by
      rw [model_iff]
      rintro ψ ⟨v,hv,rfl⟩
      specialize hrealize ⟨v,hv⟩
      simp only [subst, Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst, Term.realize_constants, hcon, LHom.onFormula]
      simp only [Formula.Realize] at hrealize
      rw [LHom.realize_onBoundedFormula fL]
      convert hrealize
      simpa using hval ⟨v,hv⟩
    have hT₃ : M ⊨ T₃ s := by
      simp [T₃, distinctConstantsTheory]
      intro ψ φ i j hi hj hij rfl
      simp [Sentence.Realize, hcon]
      contrapose! hij
      apply hdistinct φ i j hi hj
      simpa [← hval]
    haveI : M ⊨ Γ s := (hT₁.union hT₂).union hT₃
    exact Model.isSatisfiable M
  have hΓ' : Directed (· ⊆ ·) Γ :=
    Monotone.directed_le fun s t hst ↦ by
      simp only [Γ, T₂, T₃]
      exact union_subset_union (union_subset_union subset_rfl (image_mono hst))
        (iUnion_mono fun _ ↦ distinctConstantsTheory_mono (inter_subset_inter hst subset_rfl))
  let Sigma := T₁ ∪ T₂ univ ∪ T₃ univ
  have Sigma_eq_iUnion : Sigma = ⋃ s, Γ s := by
    simp [Sigma, Γ]
    have : ⋃ (s : Finset (F × I)), T₁ ∪ T₂ ↑s ∪ T₃ ↑s = T₁ ∪ (⋃ (s : Finset (F × I)), T₂ s) ∪ (⋃ (s : Finset (F × I)), T₃ s) := by
      ext x
      simp
      constructor
      · rintro ⟨s,(hs | hs) | hs⟩
        · left; left; assumption
        · left; right; exists s
        · right; exists s
      · rintro ((hs | ⟨s,hs⟩) | ⟨s,hs⟩)
        · exists ∅; left; left; assumption
        · exists s; left; right; assumption
        · exists s; right; assumption
    rw [this]
    have hT₂ : T₂ Set.univ = ⋃ (s : Finset (F × I)), T₂ s := by
      simp [T₂, ← image_iUnion]
      suffices h : ⋃ (s : Finset (F × I)), s = (univ : Set (F × I)) by
        simp only [image_univ,h]
      apply Set.eq_univ_of_forall
      intro x; exists {x}; simp
    have hT₃ : T₃ Set.univ = ⋃ (s : Finset (F × I)), T₃ s := by
      simp [T₃]
      apply subset_antisymm
      · apply iUnion_subset
        intro φ
        rw [distinctConstantsTheory_eq_iUnion]
        apply iUnion_subset
        intro s
        refine subset_iUnion₂_of_subset (s.map (Function.Embedding.subtype fun p : F × I => p.1 = φ)) φ ?_
        have : ↑(s.map (Function.Embedding.subtype fun p : F × I => p.1 = φ)) ∩ {p : F × I | p.1 = φ} =
          ↑(s.map (Function.Embedding.subtype fun p : F × I => p.1 = φ)) := by
          refine inter_eq_left.mpr ?_
          simp
          intro x hx
          refine mem_setOf.mpr x.2
        rw [this]
        simp
      · exact iUnion_subset fun s ↦
          iUnion_mono fun φ ↦ distinctConstantsTheory_mono inter_subset_right
    simp [hT₂,hT₃]
  have hSigma : Sigma.IsSatisfiable := by
    rw [Sigma_eq_iUnion]
    exact (isSatisfiable_directed_union_iff hΓ').mpr hΓ
  obtain ⟨P⟩ := hSigma
  haveI hPT₁ : P ⊨ T₁ :=
    Theory.Model.mono (P.is_model) (fun _ hψ => (Or.inl (Or.inl hψ)))
  letI : L[[M]].Structure P := fL.reduct P
  letI : L.Structure P := (L.lhomWithConstants M).reduct P
  haveI hPdiag : P ⊨ L.elementaryDiagram M := by
    change P ⊨ fL.onTheory (L.elementaryDiagram M) at hPT₁
    exact (LHom.onTheory_model fL _).mp hPT₁
  let eP : M ↪ₑ[L] P :=
    ElementaryEmbedding.ofModelsElementaryDiagram L M P
  have hPcard :
      Cardinal.lift.{max u v w} κ ≤ Cardinal.lift.{w} #P := by
    rw [← hM]
    refine lift_mk_le'.mpr ⟨eP,eP.injective⟩
  obtain ⟨N,⟨e'⟩,hNcard⟩ := L'.exists_elementaryEmbedding_card_eq_of_le
    P κ hκ hL'card hPcard
  letI : L[[M]].Structure N := fL.reduct N
  letI : L.Structure N := (L.lhomWithConstants M).reduct N
  haveI hNSigma : N ⊨ Sigma := (e'.theory_model_iff Sigma).mpr (P.is_model)
  haveI hNT₁ : N ⊨ T₁ := Theory.Model.mono (hNSigma) (fun _ hψ => (Or.inl (Or.inl hψ)))
  haveI hNT₂ : N ⊨ T₂ univ := Theory.Model.mono (hNSigma) (fun _ hψ => (Or.inl (Or.inr hψ)))
  haveI hNT₃ : N ⊨ T₃ univ := Theory.Model.mono (hNSigma) (fun _ hψ => (Or.inr hψ))
  haveI hNdiag : N ⊨ L.elementaryDiagram M := by
    change N ⊨ fL.onTheory (L.elementaryDiagram M) at hNT₁
    exact (LHom.onTheory_model fL _).mp hNT₁
  let eN : M ↪ₑ[L] N :=
    ElementaryEmbedding.ofModelsElementaryDiagram L M N
  haveI hNT : N ⊨ T :=
    (eN.theory_model_iff T).mp (ModelType.is_model M)
  haveI hNne : Nonempty N := by
    simpa [← Cardinal.mk_ne_zero_iff, hNcard, ← Cardinal.one_le_iff_ne_zero] using one_le_aleph0.trans hκ
  haveI : (L.lhomWithConstantsMap ⇑eN).IsExpansionOn ↑N:= by
    apply LHom.lhomWithConstantsMap_isExpansionOn_of_eq
    intro x
    simp [eN, Language.con]
  exists (ModelType.of T N), eN
  refine ⟨by simpa,?_⟩
  intro β ψ b hψb
  let φ : L[[M]].Formula (Fin 1) :=
    BoundedFormula.constantsVarsEquiv.symm (ψ.relabel (Sum.map b id))
  have hφI : {x : M | φ.Realize fun x_1 ↦ x}.Infinite := by
    rw [← infinite_coe_iff, ← (φ.finOneRealizationsEquiv).infinite_iff,
      infinite_coe_iff]
    convert hψb with v
    simp [φ, Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, Formula.relabel]
    congr!
    funext w
    cases w <;> rfl
  have hφN :
      #({x : N | ((L.lhomWithConstantsMap ⇑eN).onFormula φ).Realize fun _ ↦ x}) = κ := by
    apply le_antisymm
    · calc
        #{x // ((L.lhomWithConstantsMap ⇑eN).onFormula φ).Realize fun _ ↦ x} ≤ #N :=
          mk_subtype_le _
        _ = _ := hNcard
    · let rsN : Set N :=
        {x | ((L.lhomWithConstantsMap ⇑eN).onFormula φ).Realize fun _ ↦ x}
      let φ' : F := ⟨φ, hφI⟩
      rw [← mk_out κ, le_def]
      change Nonempty (I ↪ rsN)
      have hφI' : ∀ (i : I), (L[[M]].con (φ', i) : N) ∈ rsN := by
        intro i
        simp [rsN]
        simp [T₂] at hNT₂
        specialize hNT₂ (subst φ' i) φ' i rfl
        simp only [subst, Sentence.Realize, Formula.Realize, BoundedFormula.realize_subst,
          Term.realize_constants, LHom.onFormula] at hNT₂ ⊢
        simpa [LHom.realize_onBoundedFormula] using hNT₂
      let f : I → rsN := fun i =>
        ⟨(L[[M]].con (φ', i) : N), mem_setOf.mpr (hφI' i)⟩
      have hf : f.Injective := by
        intro i j hij
        simp only [T₃] at hNT₃
        have hNT₃' :
            N ⊨ L[[↑M]].distinctConstantsTheory
              (Set.univ ∩ {p : F × I | p.1 = φ'}) :=
          Theory.Model.mono hNT₃
            (subset_iUnion_of_subset ⟨φ, hφI⟩ fun ⦃a⦄ a_1 ↦ a_1)
        simp [model_distinctConstantsTheory] at hNT₃'
        specialize @hNT₃' (φ', i) (by simp) (φ', j) (by simp)
        simp [f] at hNT₃' hij
        exact (hNT₃' ∘ fun a ↦ hij) L
      exists Function.Embedding.mk f hf
  rw [← ((L.lhomWithConstantsMap ⇑eN).onFormula φ).finOneRealizationsEquiv.cardinal_eq]
    at hφN
  change #({x : Fin 1 → N | ψ.Realize (Sum.elim (eN ∘ b) x)}) = κ
  convert hφN with v
  letI := constantsOn.structure eN
  haveI : (L.lhomWithConstantsMap ⇑eN).IsExpansionOn ↑N := by
    apply LHom.lhomWithConstantsMap_isExpansionOn_of_eq
    intro a
    rfl
  simp [(L.lhomWithConstantsMap ⇑eN).realize_onFormula, φ]
  simp [Formula.Realize, Formula.relabel, ← BoundedFormula.realize_constantsVarsEquiv]
  congr!
  funext w
  cases w <;> rfl

theorem exists_model_of_card_definably_full
    {κ : Cardinal.{w}}
    (hL : L.card ≤ ℵ₀)
    (hT : ∃ M : ModelType.{u, v, max u v} T, Infinite M)
    (hκ : ℵ₀ ≤ κ) :
    ∃ M : ModelType.{u, v, w} T, #M = κ ∧ L.DefinablyFull M:= by
  obtain ⟨M₀,hM₀card⟩ :=
    Theory.exists_model_card_eq hT κ hκ
      ((lift_le_aleph0.mpr hL).trans (aleph0_le_lift.mpr hκ))
  let Stage := {M : ModelType.{u,v,w} T | #M = κ}
  have hLκ :
        Cardinal.lift.{w} L.card ≤ Cardinal.lift.{max u v} κ :=
      (lift_le_aleph0.mpr hL).trans (aleph0_le_lift.mpr hκ)
  have hsucc : ∀ s : Stage, ∃ t : Stage, ∃ e : s.1 ↪ₑ[L] t.1,
        ∀ {β : Type w} (ψ : L.Formula (β ⊕ Fin 1)) (b : β → s.1),
          Set.Infinite {x : Fin 1 → s.1 | ψ.Realize (Sum.elim b x)} →
            #({x : Fin 1 → t.1 | ψ.Realize (Sum.elim (e ∘ b) x)}) = κ := by
    intro s
    obtain ⟨N,e,hNcard,hfull⟩ :=
      exists_elementaryExtension_card_eq_with_full_unary_realizations.{u,v,w,w}
        T s.1 s.2 hκ hLκ
    exists ⟨N,hNcard⟩, e
  choose next nextEmb nextFull using hsucc
  let stage : ℕ → Stage := fun n ↦
    Nat.rec ⟨M₀,hM₀card⟩ (fun _ s ↦ next s) n
  let M : ℕ → Type w := fun n ↦ (stage n).1
  letI chainStruct : ∀ n, L.Structure (M n) := fun n ↦
    (stage n).1.struc
  let f : ∀ n, M n ↪ₑ[L] M (n + 1) := fun n ↦ by
    simpa [M, stage, chainStruct] using nextEmb (stage n)
  let C := ElementaryChain.ofNatSucc M f
  haveI : Nonempty (C.Limit) := Nonempty.map (C.toLimit 0) M₀.instNonempty
  let M' : T.ModelType := (C.limit_models T ⟨0,M₀.is_model⟩).bundled
  have hM'κ : #M' = κ := by
    apply C.mk_limit_eq_of_forall_lift_mk_eq
    · exact le_of_eq_of_le rfl hκ
    · intro i
      cases i with
      | zero => simpa [C, M, f, ElementaryChain.ofNatSucc, stage]
      | succ n =>
        simp [C, M, f, ElementaryChain.ofNatSucc, stage]
        exact (next (Nat.rec ⟨M₀, hM₀card⟩ (fun x s ↦ next s) n)).2
  refine ⟨M',hM'κ,?_⟩
  have hM'I : Infinite M' := infinite_iff.mpr <|
    le_of_le_of_eq hκ (id (Eq.symm hM'κ))
  apply definablyFull_of_unary
  unfold UnaryDefinablyFull
  intro A X hAX hXI
  rw [Definable₁, definable_iff_finitely_definable] at hAX
  rcases hAX with ⟨A₀,hA₀,φ,hφ⟩
  obtain ⟨i,v,hiv⟩ := C.exists_finite_common_stage fun (a : A₀) ↦ a.1
  let ψ : L.Formula (A₀ ⊕ Fin 1) := BoundedFormula.constantsVarsEquiv φ
  have hψI : {x : Fin 1 → (stage i).1 | ψ.Realize (Sum.elim v x)}.Infinite := by
    erw [← (C.toLimitElementary i).infinite_realizations_iff ψ v]
    change {x : Fin 1 → M' | ψ.Realize (Sum.elim (C.toLimit i ∘ v) x)}.Infinite
    convert_to {x : Fin 1 → M' | x 0 ∈ X}.Infinite using 1
    · rw [hφ]
      ext x
      change ψ.Realize (Sum.elim (C.toLimit i ∘ v) x) ↔ _
      simpa only [ψ, hiv] using
        BoundedFormula.realize_constantsVarsEquiv (φ := φ) (v := x)
    · refine hXI.preimage (f := fun x : Fin 1 → M' ↦ x 0) ?_
      simp only [Fin.isValue, range_eval, subset_univ]
  specialize nextFull (stage i) ψ v hψI
  apply le_antisymm
  · exact mk_set_le X
  · let b : A₀ → M' :=
      (C.toLimitElementary (i + 1)) ∘ (f i) ∘ v
    calc
    #↑M' = κ := hM'κ
    _ = _ := nextFull.symm
    _ ≤ #↑{x : Fin 1 → M' | ψ.Realize (Sum.elim b x)} := by
      simpa [lift_id, b] using (C.toLimitElementary (i + 1)).mk_realizations_le ψ (f i ∘ v)
    _ = #{x : Fin 1 → M' | x 0 ∈ X} := by
      rw [hφ]
      congr! with x
      simp [ψ, Formula.Realize, ← BoundedFormula.realize_constantsVarsEquiv, b]
      congr! with a
      change C.toLimit (i + 1) (f i (v a)) = (a : M')
      simpa [← congrFun hiv a, C] using C.toLimit_map (Nat.le_succ i) (v a)
    _ = _ :=
      Cardinal.mk_congr ((Equiv.funUnique (Fin 1) M').subtypeEquiv (by intro x; rfl))

end Theory

end Language

end FirstOrder
