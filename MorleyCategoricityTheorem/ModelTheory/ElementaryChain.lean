import Mathlib.ModelTheory.Bundled
import Mathlib.ModelTheory.DirectLimit
import Mathlib.ModelTheory.ElementaryMaps

/-!
# Elementary Chains

This file defines an elementary chain without choosing a common ambient structure.  Its union is
the direct limit of the underlying directed system of first-order embeddings.

The main remaining mathematical argument is that the canonical maps into the direct limit are
elementary.  The relevant statements are included below with proof placeholders.
-/

universe u v w w'

open Cardinal Function

/- These are copied from `Mathlib.SetTheory.Cardinal.DirectLimit` in the newer Mathlib checkout.
They stay private until this project updates to a Mathlib version containing that module. -/

private def directLimitEquivOfForallLE {ι : Type w} [Preorder ι] {F : ι → Type w'}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort u} (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)] [IsDirectedOrder ι] (m : ι) (hm : ∀ i, i ≤ m) :
    _root_.DirectLimit F (f · · ·) ≃ F m where
  toFun := _root_.DirectLimit.lift f (fun i x ↦ f i m (hm i) x) (by simp [DirectedSystem.map_map'])
  invFun := fun x ↦ ⟦⟨m, x⟩⟧
  left_inv := by
    intro z
    induction z using _root_.DirectLimit.induction with
    | _ i x => simp only [_root_.DirectLimit.lift_def, _root_.DirectLimit.mk_apply]
  right_inv := fun _ ↦ by simp only [_root_.DirectLimit.lift_def, DirectedSystem.map_self']

private theorem directLimitMkLeSum {ι : Type w} [Preorder ι] {F : ι → Type w'}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort u} (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)] [IsDirectedOrder ι] :
    #(_root_.DirectLimit F (f · · ·)) ≤ Cardinal.sum fun i ↦ #(F i) :=
  mk_quotient_le.trans_eq (mk_sigma F)

private theorem directLimitMkLeOfAleph0Le {ι : Type w} [Preorder ι] {F : ι → Type w'}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort u} (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)] [IsDirectedOrder ι] (c : Cardinal.{max w w'})
    (hc : ℵ₀ ≤ c) (hι : Cardinal.lift.{w'} #ι ≤ c)
    (hF : ∀ i, Cardinal.lift.{w} #(F i) ≤ c) :
    #(_root_.DirectLimit F (f · · ·)) ≤ c :=
  (directLimitMkLeSum f).trans <| (sum_le_lift_mk_mul_iSup_lift _).trans <|
    Cardinal.mul_le_of_le hc hι (ciSup_le' hF)

private theorem directLimitISupLiftMkLeMk {ι : Type w} [Preorder ι] {F : ι → Type w'}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort u} (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)] [IsDirectedOrder ι]
    (h : ∀ i, Injective fun x ↦ (⟦⟨i, x⟩⟧ : _root_.DirectLimit F (f · · ·))) :
    (⨆ i, Cardinal.lift.{w} #(F i)) ≤ #(_root_.DirectLimit F (f · · ·)) := by
  refine ciSup_le' fun i ↦ ?_
  have := lift_mk_le_lift_mk_of_injective (h i)
  simp [_root_.DirectLimit]
  rwa [Cardinal.lift_umax, Cardinal.lift_id'.{w', w}] at this

private theorem directLimitMkEqISupLiftMk {ι : Type w} [Preorder ι] {F : ι → Type w'}
    {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort u} (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)] [IsDirectedOrder ι]
    (hι : Cardinal.lift.{w'} #ι ≤ ⨆ i, Cardinal.lift.{w} #(F i))
    (h : ∀ i, Injective fun x ↦ (⟦⟨i, x⟩⟧ : _root_.DirectLimit F (f · · ·))) :
    #(_root_.DirectLimit F (f · · ·)) = ⨆ i, Cardinal.lift.{w} #(F i) := by
  refine le_antisymm ?_ (directLimitISupLiftMkLeMk f h)
  by_cases! hc : ℵ₀ ≤ ⨆ i, lift.{w, w'} #(F i)
  · exact directLimitMkLeOfAleph0Le f _ hc hι fun i ↦
      le_ciSup Cardinal.bddAbove_of_small i
  · haveI : Finite ι := mk_lt_aleph0_iff.mp (lift_lt_aleph0.mp (hι.trans_lt hc))
    cases isEmpty_or_nonempty ι with
    | inl hle =>
      simp
    | inr hlne =>
      obtain ⟨m, hm⟩ := Finite.exists_le (id : ι → ι)
      have he := (directLimitEquivOfForallLE f m hm).lift_cardinal_eq
      rw [Cardinal.lift_id'.{w', w}, Cardinal.lift_umax.{w', w}] at he
      rw [he]
      exact le_ciSup Cardinal.bddAbove_of_small m

private theorem directLimitMkEqOfForallLiftMkEq {ι : Type w} [Preorder ι]
    {F : ι → Type w'} {T : ∀ ⦃i j : ι⦄, i ≤ j → Sort u}
    (f : ∀ i j (h : i ≤ j), T h)
    [∀ ⦃i j⦄ (h : i ≤ j), FunLike (T h) (F i) (F j)]
    [DirectedSystem F (f · · ·)] [IsDirectedOrder ι] [Nonempty ι]
    (c : Cardinal.{max w w'}) (hι : Cardinal.lift.{w'} #ι ≤ c)
    (hF : ∀ i, Cardinal.lift.{w} #(F i) = c)
    (h : ∀ i, Injective fun x ↦ (⟦⟨i, x⟩⟧ : _root_.DirectLimit F (f · · ·))) :
    #(_root_.DirectLimit F (f · · ·)) = c := by
  simpa only [hF, ciSup_const] using
    directLimitMkEqISupLiftMk f (by simpa only [hF, ciSup_const]) h

namespace FirstOrder

namespace Language

open scoped Cardinal

/-- A directed system of `L`-structures whose transition maps are elementary embeddings.

Despite the name, the index type is only required to be a preorder here.  Directedness is imposed
when forming the limit, so the same definition also covers elementary chains indexed by a linear
or well-order.
-/
structure ElementaryChain (L : Language.{u, v}) (ι : Type w) [Preorder ι] where
  /-- The structure at each stage of the chain. -/
  carrier : ι → Type w'
  /-- The `L`-structure on each stage. -/
  [struc : ∀ i, L.Structure (carrier i)]
  /-- The elementary transition map between comparable stages. -/
  map : ∀ i j, i ≤ j → carrier i ↪ₑ[L] carrier j
  /-- Transition along a reflexive comparison is the identity, pointwise. -/
  map_self : ∀ i x, map i i le_rfl x = x
  /-- Transition maps compose coherently, pointwise. -/
  map_map : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k) (x : carrier i),
    map j k hjk (map i j hij x) = map i k (hij.trans hjk) x

attribute [instance] ElementaryChain.struc

namespace ElementaryEmbedding

variable {L : Language.{u, v}} {M : ℕ → Type w'} [∀ n, L.Structure (M n)]

/-- Compose a sequence of elementary embeddings along an interval of natural numbers. -/
noncomputable def natLERec (f : ∀ n, M n ↪ₑ[L] M (n + 1))
    (m n : ℕ) (h : m ≤ n) : M m ↪ₑ[L] M n :=
  Nat.leRecOn h (@fun k g ↦ (f k).comp g) (refl L _)

/-- Iterated composition over a reflexive natural-number interval is the identity. -/
@[simp]
theorem natLERec_self (f : ∀ n, M n ↪ₑ[L] M (n + 1)) (n : ℕ) (x : M n) :
    natLERec f n n le_rfl x = x := by
  simp [natLERec, Nat.leRecOn]

/-- Iterated composition over one successor step is the supplied elementary embedding. -/
@[simp]
theorem natLERec_succ (f : ∀ n, M n ↪ₑ[L] M (n + 1)) (n : ℕ) (x : M n) :
    natLERec f n (n + 1) (Nat.le_succ n) x = f n x := by
  simp [natLERec, Nat.leRecOn]

/-- Iterated elementary embeddings compose coherently across adjacent intervals. -/
theorem natLERec_trans {f : ∀ n, M n ↪ₑ[L] M (n + 1)}
    {i j k : ℕ} (hij : i ≤ j) (hjk : j ≤ k) (x : M i) :
    natLERec f j k hjk (natLERec f i j hij x) = natLERec f i k (hij.trans hjk) x := by
  induction k, hjk using Nat.le_induction with
  | base =>
    simp only [natLERec_self]
  | succ k hjk ih =>
    simp [natLERec, Nat.leRecOn_succ hjk, Nat.leRecOn_succ (hij.trans hjk)]
    convert ih

end ElementaryEmbedding

namespace ElementaryChain

variable {L : Language.{u, v}} {ι : Type w} [Preorder ι]

/-- Construct a countable elementary chain by composing elementary embeddings between
successive stages. -/
noncomputable def ofNatSucc (M : ℕ → Type w') [∀ n, L.Structure (M n)]
    (f : ∀ n, M n ↪ₑ[L] M (n + 1)) : ElementaryChain L ℕ where
  carrier := M
  map := ElementaryEmbedding.natLERec f
  map_self := ElementaryEmbedding.natLERec_self f
  map_map := fun _ _ _ hij hjk x => ElementaryEmbedding.natLERec_trans hij hjk x

/-- The transition map of `ofNatSucc` between successive stages is the supplied elementary
embedding. -/
@[simp]
theorem ofNatSucc_map_succ (M : ℕ → Type w') [∀ n, L.Structure (M n)]
    (f : ∀ n, M n ↪ₑ[L] M (n + 1)) (n : ℕ) :
    (ofNatSucc M f).map n (n + 1) (Nat.le_succ n) = f n := by
  ext x
  simp [ofNatSucc]
  exact ElementaryEmbedding.natLERec_succ f n x

/-- The underlying first-order embeddings form a directed system. -/
instance toEmbeddingDirectedSystem (C : ElementaryChain L ι) :
    DirectedSystem C.carrier (fun i j h => (C.map i j h).toEmbedding) where
  map_self i x := C.map_self i x
  map_map k j i hij hjk x := C.map_map i j k hij hjk x

variable [IsDirectedOrder ι]

/-- The abstract union of an elementary chain, constructed without an ambient structure. -/
abbrev Limit (C : ElementaryChain L ι) :=
  L.DirectLimit C.carrier (fun i j h => (C.map i j h).toEmbedding)

variable [Nonempty ι]

/-- The canonical first-order embedding of a stage into the direct limit. -/
noncomputable def toLimit (C : ElementaryChain L ι) (i : ι) : C.carrier i ↪[L] C.Limit :=
  DirectLimit.of L ι C.carrier (fun i j h => (C.map i j h).toEmbedding) i

/-- The canonical maps commute with the transition maps. -/
@[simp]
theorem toLimit_map (C : ElementaryChain L ι) {i j : ι} (hij : i ≤ j) (x : C.carrier i) :
    C.toLimit j (C.map i j hij x) = C.toLimit i x := by
  unfold toLimit; exact DirectLimit.of_f

/-- Every element of the direct limit is represented by an element of some stage. -/
theorem exists_toLimit (C : ElementaryChain L ι) (z : C.Limit) :
    ∃ (i : ι) (x : C.carrier i), C.toLimit i x = z := by
  simpa [toLimit] using DirectLimit.exists_of z

private def limitEquiv (C : ElementaryChain L ι) :
    C.Limit ≃
      _root_.DirectLimit C.carrier (fun i j h ↦ (C.map i j h).toEmbedding) :=
  Quotient.congrRight fun _ _ ↦ Iff.rfl

omit [Nonempty ι] in
/-- An infinite cardinal bounding the index type and every stage also bounds the limit. -/
theorem mk_limit_le_of_lift_mk_le (C : ElementaryChain L ι) {κ : Cardinal.{max w w'}}
    (hκ : ℵ₀ ≤ κ) (hι : Cardinal.lift.{w'} #ι ≤ κ)
    (hC : ∀ i, Cardinal.lift.{w} #(C.carrier i) ≤ κ) :
    #(C.Limit) ≤ κ := by
  rw [(limitEquiv C).cardinal_eq]
  exact directLimitMkLeOfAleph0Le
    (fun i j h ↦ (C.map i j h).toEmbedding) κ hκ hι hC

/-- If every stage has cardinality `κ` and the index type has cardinality at most `κ`, then the
limit also has cardinality `κ`. -/
theorem mk_limit_eq_of_forall_lift_mk_eq (C : ElementaryChain L ι)
    (κ : Cardinal.{max w w'}) (hι : Cardinal.lift.{w'} #ι ≤ κ)
    (hC : ∀ i, Cardinal.lift.{w} #(C.carrier i) = κ) :
    #(C.Limit) = κ := by
  rw [(limitEquiv C).cardinal_eq]
  apply directLimitMkEqOfForallLiftMkEq
    (fun i j h ↦ (C.map i j h).toEmbedding) κ hι hC
  exact _root_.DirectLimit.mk_injective _ fun i j h ↦ (C.map i j h).injective

/-- Realization of bounded formulas is preserved and reflected by a canonical map into the
direct limit.
-/
theorem realize_toLimit (C : ElementaryChain L ι) {α : Type*} {n : ℕ}
    (φ : L.BoundedFormula α n) (i : ι) (v : α → C.carrier i)
    (xs : Fin n → C.carrier i) :
    φ.Realize (C.toLimit i ∘ v) (C.toLimit i ∘ xs) ↔ φ.Realize v xs := by
  induction φ generalizing i with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp [BoundedFormula.Realize, ← Sum.comp_elim]
  | rel R ts =>
    simp [BoundedFormula.Realize, ← Sum.comp_elim]
    exact StrongHomClass.map_rel (C.toLimit i) _ _
  | imp φ ψ ihφ ihψ =>
    simp [BoundedFormula.Realize, ihφ, ihψ]
  | @all n φ ih =>
    simp [BoundedFormula.Realize]
    constructor <;> intro h x
    · simpa [← Fin.comp_snoc, ih i v (Fin.snoc xs x)] using h (C.toLimit i x)
    · obtain ⟨j,xj,rfl⟩ := C.exists_toLimit x
      obtain ⟨k,hik,hjk⟩ := exists_ge_ge i j
      rw [← BoundedFormula.Realize,
        ← (C.map i k hik).map_boundedFormula φ.all v xs, BoundedFormula.Realize] at h
      specialize h (C.map j k hjk xj)
      specialize ih k (C.map i k hik ∘ v) (Fin.snoc (C.map i k hik ∘ xs) (C.map j k hjk xj))
      rw [← ih, Fin.comp_snoc] at h
      convert h using 1 <;> simp [Function.comp_def, C.toLimit_map]

/-- The canonical map from each stage to the direct limit is elementary. -/
noncomputable def toLimitElementary (C : ElementaryChain L ι) (i : ι) :
    C.carrier i ↪ₑ[L] C.Limit where
  toFun := C.toLimit i
  map_formula' := fun n φ v => by
    simp [Formula.Realize]
    convert C.realize_toLimit φ i v default

/-- A finite tuple indexed by `Fin n` from the direct limit can be lifted to a common stage. -/
private lemma exists_fin_common_stage (C : ElementaryChain L ι) {n : ℕ}
    (x : Fin n → C.Limit) : ∃ (i : ι) (z : Fin n → C.carrier i), C.toLimit i ∘ z = x := by
  induction n with
  | zero =>
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, Fin.elim0, by ext k; exact Fin.elim0 k⟩
  | succ n ih =>
    obtain ⟨i₁, z₁, hz₁⟩ := ih (x ∘ Fin.castSucc)
    obtain ⟨i₂, y, hy⟩ := C.exists_toLimit (x (Fin.last n))
    obtain ⟨i, hi₁, hi₂⟩ := exists_ge_ge i₁ i₂
    refine ⟨i, Fin.snoc (fun k => C.map i₁ i hi₁ (z₁ k)) (C.map i₂ i hi₂ y), ?_⟩
    ext k
    refine Fin.lastCases ?_ (fun k => ?_) k
    · simpa using hy
    · simpa [Function.comp_apply] using congrFun hz₁ k

/-- A finite family of elements of the direct limit can be lifted to a common stage of the chain. -/
theorem exists_finite_common_stage (C : ElementaryChain L ι) {α : Type*} [Finite α]
    (x : α → C.Limit) : ∃ (i : ι) (z : α → C.carrier i), C.toLimit i ∘ z = x := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  obtain ⟨i, z, hz⟩ := exists_fin_common_stage C (x ∘ e.symm)
  refine ⟨i, z ∘ e, ?_⟩
  ext a
  simpa [Function.comp_def, e.symm_apply_apply] using congrFun hz (e a)

/-- A compatible cocone of elementary embeddings induces an elementary embedding from the direct
limit.  This is the elementary version of `Language.DirectLimit.lift`. -/
noncomputable def liftElementary (C : ElementaryChain L ι) {P : Type*} [L.Structure P]
    (g : ∀ i, C.carrier i ↪ₑ[L] P)
    (comm : ∀ i j (hij : i ≤ j) (x : C.carrier i), g j (C.map i j hij x) = g i x) :
    C.Limit ↪ₑ[L] P :=
  let F : C.Limit ↪[L] P := Language.DirectLimit.lift L ι C.carrier
    (fun i j h => (C.map i j h).toEmbedding)
    (fun i => (g i).toEmbedding)
    (by intro i j hij x; simpa using comm i j hij x)
  { toFun := F
    map_formula' := by
      intro n φ x
      obtain ⟨i, z, hz⟩ := exists_fin_common_stage C x
      have hF_lift : ∀ a : C.carrier i, F (C.toLimit i a) = g i a := by
        intro a
        simp [F, toLimit]
      have h_eq : F ∘ x = (g i : C.carrier i → P) ∘ z := by
        ext k
        calc
          F (x k) = F (C.toLimit i (z k)) := by simp [← hz]
          _ = g i (z k) := hF_lift (z k)
      rw [h_eq]
      exact ((g i).map_formula' φ z).trans <| by
        rw [← hz]
        exact ((C.toLimitElementary i).map_formula' φ z).symm }

/-- If some stage is a model of `T`, then the direct limit is also a model of `T`. -/
theorem limit_models (C : ElementaryChain L ι) (T : L.Theory)
    (hT : ∃ i, C.carrier i ⊨ T) : C.Limit ⊨ T := by
  obtain ⟨i ,hi⟩ := hT
  exact ((C.toLimitElementary i).theory_model_iff T).1 hi

end ElementaryChain

end Language

end FirstOrder
