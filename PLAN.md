# Plan: The Realization Set of a Formula

## Target

Introduce a thin, unbundled semantic layer that names the set of tuples realizing a formula once
its parameter variables have been assigned values, and equip it with the membership, Boolean,
relabelling, elementary-embedding, and cardinality API needed by the two-cardinal part of the
blueprint.  The layer is a naming and reuse exercise, not a new theory of definable sets.

The public definition is intended to be:

```lean
def FirstOrder.Language.Formula.realizationSet
    (φ : L.Formula (α ⊕ β)) (a : α → M) : Set (β → M)
```

with a unary specialization `Formula.realizationSet₁ : Set M`.

## Motivation

Commit `e5b2d77` (`feat: define Vaughtian pairs`) had to hand-write the same set-builder four times
inside a 119-line file:

```lean
{x : M | φ.Realize (Sum.elim a (fun _ : Fin 1 => x))}
{y : N | φ.Realize (Sum.elim ((e : M → N) ∘ a) (fun _ : Fin 1 => y))}
```

`ElementaryEmbedding.image_realizations_subset` exists only to re-derive "an elementary embedding
sends the source realization set into the target realization set" for the unary shape
`Fin n ⊕ Fin 1`, because it cannot reuse `ElementaryMaps.realizations_embedding` stated for the
general shape `β ⊕ α`.

This is not an isolated incident.  The same set-builder is the working representation of
"parameter-definable subset" throughout the project:

| Location | Occurrences |
|---|---|
| `ModelTheory/Semantics.lean`, `realize_iExsAtLeast/AtMost/Exactly` | `{x : β → M \| φ.Realize (Sum.elim v x)}` |
| `ModelTheory/ElementaryMaps.lean` | `{x : α → M \| φ.Realize (Sum.elim b x)}` in all four statements |
| `ModelTheory/DefinablyFull.lean` | `{x : Fin 1 → M \| ψ.Realize (Sum.elim b x)}`, `{x : M \| φ.Realize fun _ ↦ x}` |
| `ModelTheory/VaughtianPair.lean` | unary `Fin n ⊕ Fin 1` shape, four times |

The project therefore already uses "the realization set of a formula" everywhere but has never
given it a name.  Consequently no `simp` or `rw` lemma can move between call sites, and every new
node of the form "this parameter-definable set is infinite / has cardinality λ / is unchanged in an
elementary extension" restates the object in a slightly different shape.

The blueprint nodes that will need the layer are:

- `def:kappa-lambda-model` ("some one-variable parameter-definable subset of `M`"),
- `lem:kappa-lambda-model-gives-vaughtian-pair` (`φ(M,ā) = φ(N,ā)`),
- `cor:no-small-infinite-definable-sets-without-vaughtian-pairs`,
- `lem:countable-vaughtian-pair` ("no realizations outside the `U`-part"),
- and the existing `lem:elementary-embedding-definable-set-cardinality`.

## Relationship to Mathlib

Mathlib already provides two related but insufficient notions.

```lean
def Set.Definable (s : Set (α → M)) : Prop :=
  ∃ φ : L[[A]].Formula α, s = setOf φ.Realize

def L.DefinableSet (A : Set M) (α : Type*) :=
  { s : Set (α → M) // A.Definable L s }
```

Neither replaces the proposed definition.

- `Set.Definable` is a proposition, so it cannot be used as a set.
- `L.DefinableSet` is a bundled subtype with a Boolean algebra structure.  Using it makes the image
  of a definable set under an elementary embedding no longer a definable set over the same
  parameter set, so the Vaughtian condition "unchanged in `N`" becomes an asymmetric coercion
  problem rather than an equality of sets.
- Both take parameters as constants of the expansion `L[[A]]`, while the two-cardinal part of the
  blueprint uses parameters as tuple variables `a : α → M`.  The translation between the two
  conventions should be one lemma, not repeated inline.

The proposed definition is exactly the unbundled companion of `Set.Definable`: with it,
Mathlib's `Set.definable_iff_exists_formula_sum` becomes

```lean
A.Definable L s ↔ ∃ φ : L.Formula (A ⊕ α), s = φ.realizationSet (Subtype.val)
```

so the witnessing formula of a definable set *is* the formula whose realization set it is, and the
bridge to `DefinableSet` is `⟨φ, rfl⟩`.  This is the main argument that the layer belongs upstream
rather than being a local invention.

## Relationship to Type Spaces

`T.typesWith σ` is a clopen subset of the Stone space of complete types; its elements are types, not
tuples.  `φ.realizationSet a` is a subset of the model `β → M` and is the model-side counterpart.
The dictionary between the two already exists in `ModelTheory/Types.lean` as
`CompleteType.typesWith_nonempty_iff_exists_realize`.  The new definition does not duplicate it; the
module documentation should state which side of the dictionary each object lives on.

## Design

### Definition and conventions

```lean
namespace FirstOrder.Language.Formula

variable {L : Language.{u, v}} {M : Type w} [L.Structure M]
variable {α : Type x} {β : Type y}

/-- `φ.realizationSet a` is the set of `β`-tuples realizing `φ` when the `α`-variables are
assigned the parameter tuple `a`. -/
def realizationSet (φ : L.Formula (α ⊕ β)) (a : α → M) : Set (β → M) :=
  {x | φ.Realize (Sum.elim a x)}

@[simp]
theorem mem_realizationSet {φ : L.Formula (α ⊕ β)} {a : α → M} {x : β → M} :
    x ∈ φ.realizationSet a ↔ φ.Realize (Sum.elim a x) :=
  Iff.rfl
```

Conventions, chosen to match the existing code rather than to introduce a third one:

- **Parameters first.**  The index type is `α ⊕ β`, the parameter tuple is `a : α → M`, and the
  realized tuples live in `β → M`.  This is the orientation already used by
  `Formula.realize_iExsAtLeast` (`φ : L.Formula (α ⊕ β)`, `v : α → M`,
  `{x : β → M | …}.encard`) and by `ElementaryMaps.realizations_embedding`.  It also lets the
  counting-formula lemmas be restated as
  `(φ.iExsAtLeast β n).Realize v ↔ (n : ℕ∞) ≤ (φ.realizationSet v).encard`.
- **`def`, not `abbrev`.**  An `abbrev` would unfold during every `simp`, risking defeq blow-ups and
  simp loops in the large cardinality proofs; a `def` together with a `@[simp]` membership lemma is
  the Mathlib convention and keeps the `Definable` bridge available.
- **Unbundled.**  The object is a plain `Set`, so images, preimages, and equality behave as in
  ordinary set theory and the `Cardinal.mk` / `Set.encard` API applies directly.
- **No notation.**  A custom notation would add blueprint-matching cost for little gain.

### Unary specialization

The two-cardinal story only uses unary sets, and `Set (Fin 1 → M)` is an awkward home for
`Set.Infinite`, `Set.encard`, and `Cardinal.mk`.  Provide

```lean
/-- The unary realization set. -/
def realizationSet₁ (φ : L.Formula (α ⊕ Fin 1)) (a : α → M) : Set M :=
  {x | φ.Realize (Sum.elim a fun _ => x)}

@[simp]
theorem mem_realizationSet₁ {φ : L.Formula (α ⊕ Fin 1)} {a : α → M} {x : M} :
    x ∈ φ.realizationSet₁ a ↔ φ.Realize (Sum.elim a fun _ => x) :=
  Iff.rfl
```

and relate the two shapes once:

```lean
theorem realizationSet_fin_one_image (φ : L.Formula (α ⊕ Fin 1)) (a : α → M) :
    φ.realizationSet a = (fun x : M => fun _ : Fin 1 => x) '' φ.realizationSet₁ a

theorem infinite_realizationSet_fin_one_iff (φ : L.Formula (α ⊕ Fin 1)) (a : α → M) :
    (φ.realizationSet a).Infinite ↔ (φ.realizationSet₁ a).Infinite
```

`DefinablyFull.Formula.finOneRealizationsEquiv` is the subtype-level version of the second lemma and
should move next to the new definitions or be generalized to `Equiv.funUnique (Fin 1) M`.

### Core API

1. **Membership and extensionality.**
   `mem_realizationSet`, `mem_realizationSet₁`,
   `realizationSet_congr : (∀ x, φ.Realize (Sum.elim a x) ↔ ψ.Realize (Sum.elim b x)) → φ.realizationSet a = ψ.realizationSet b`,
   and the `Set.ext` corollary.
2. **Boolean laws**, each one `ext x; simp`:
   `realizationSet_top`, `realizationSet_bot`, `realizationSet_inf`, `realizationSet_sup`,
   `realizationSet_compl`, `realizationSet_imp`.  These attach the existing
   `Formula.realize_inf`/`realize_sup`/`realize_not`/`realize_imp` lemmas to the new name.  The
   Boolean-algebra structure itself stays in Mathlib's `DefinableSet`; do not duplicate it.
3. **Variable relabelling.**
   ```lean
   theorem realizationSet_relabel (φ : L.Formula (α ⊕ β)) (a : α → M) (f : β' → β) :
       (φ.relabel (Sum.map id f)).realizationSet a =
         (fun x : β → M => x ∘ f) ⁻¹' φ.realizationSet a
   ```
   proved from `Formula.realize_relabel` and `Sum.elim_comp_map`.  This absorbs the `Sum.inl` /
   `Sum.inr` projections currently hand-rolled in `ModelTheory/Types.lean`.
4. **Elementary-embedding transport.**
   ```lean
   theorem ElementaryEmbedding.image_realizationSet_subset
       (e : M ↪ₑ[L] N) (φ : L.Formula (α ⊕ β)) (a : α → M) :
       (e : M → N) '' φ.realizationSet a ⊆ φ.realizationSet (e ∘ a)
   ```
   This generalizes `VaughtianPair.image_realizations_subset`, which should then be deleted.  Also
   restate `ElementaryMaps` as
   `realizations_embedding e φ b : φ.realizationSet b ↪ φ.realizationSet (e ∘ b)`.
5. **Cardinality.**  Restate `mk_realizations_le`, `encard_realizations_eq_coe_iff`, and
   `infinite_realizations_iff` with `realizationSet`.  Because `realizationSet` is a `def`, each
   restatement is definitionally equal to the current statement, so this is safe; see the risk
   note about declaration types below.  Keep the documented boundary: `Set.encard` only for
   comparison with a natural number, `Cardinal.mk` for monotonicity and arbitrary infinite lower
   bounds.

### Bridge to definable sets

```lean
theorem Set.definable_realizationSet {A : Set M} (φ : L.Formula (A ⊕ β)) :
    A.Definable L (φ.realizationSet (Subtype.val : A → M)) :=
  ⟨φ, rfl⟩
```

plus the reformulation of `Set.definable_iff_exists_formula_sum` in terms of `realizationSet`.
Optionally a bundled constructor for callers that want the Boolean algebra:

```lean
def Formula.toDefinableSet {A : Set M} (φ : L.Formula (A ⊕ β)) : L.DefinableSet A β :=
  ⟨φ.realizationSet Subtype.val, Set.definable_realizationSet φ⟩
```

Add `toDefinableSet` only if a caller needs `⊔`, `ᶜ`, or `Definable.mono` on the realization set;
do not add it preemptively.

### Rewriting the Vaughtian pair

```lean
def IsVaughtianPair (T : L.Theory) (e : M ↪ₑ[L] N) : Prop :=
  M ⊨ T ∧ N ⊨ T ∧ ¬ Function.Surjective e ∧
    ∃ (n : ℕ) (φ : L.Formula (Fin n ⊕ Fin 1)) (a : Fin n → M),
      (φ.realizationSet₁ a).Infinite ∧
      φ.realizationSet₁ (e ∘ a) = (e : M → N) '' φ.realizationSet₁ a
```

Because `realizationSet₁` unfolds to the current set-builder, this is a definitionally equal
restatement: `isVaughtianPair_iff` keeps its proof, and `image_realizations_subset` disappears.
After the rewrite `VaughtianPair.lean` should contain no `Sum.elim` at all.

## File plan

1. `MorleyCategoricityTheorem/ModelTheory/Semantics.lean`
   - `Formula.realizationSet`, `Formula.realizationSet₁`, membership, Boolean, and relabelling
     lemmas.  No new imports.
2. `MorleyCategoricityTheorem/ModelTheory/ElementaryMaps.lean`
   - elementary-embedding transport and cardinality restatements.  No new imports.
3. `MorleyCategoricityTheorem/ModelTheory/DefinablyFull.lean` (or a small new module)
   - the `Set.Definable` bridge, placed where `Mathlib.ModelTheory.Definability` is already
     imported.  Do not add that import to the foundational `Semantics.lean`.
4. `MorleyCategoricityTheorem/ModelTheory/VaughtianPair.lean`
   - restate `IsVaughtianPair` and delete the superseded lemma.
5. `MorleyCategoricityTheorem.lean`
   - only if a new module is added.

## Implementation order

1. Search the current Mathlib dependency again for an upstream realization-set definition; confirm
   that only `Set.Definable` and `L.DefinableSet` exist.
2. Define `Formula.realizationSet` and prove `mem_realizationSet`.
3. Add the unary specialization and the two shape-conversion lemmas; relocate or generalize
   `finOneRealizationsEquiv`.
4. Add the Boolean and relabelling laws.
5. Add `ElementaryEmbedding.image_realizationSet_subset` and restate
   `realizations_embedding`, `mk_realizations_le`, `encard_realizations_eq_coe_iff`,
   `infinite_realizations_iff`.
6. Optionally restate the counting-formula lemmas in `Semantics.lean` in terms of
   `realizationSet`.
7. Add the `Set.Definable` bridge and the `definable_iff_exists_formula_sum` reformulation.
8. Restate `IsVaughtianPair` and delete `image_realizations_subset`.
9. Recheck whether the blueprint proof text of the two-cardinal nodes should reference the new
   declaration names; update the blueprint only when explicitly authorized.

## Non-goals

- Do not introduce a bundled realization-set or definable-set type alongside `L.DefinableSet`.
- Do not change the two-cardinal encoding in which the Vaughtian formula is unary with `Fin n`
  parameters; keep the general layer at `α ⊕ β` and specialize.
- Do not decide between `Set.encard` and `Cardinal.mk` inside the definition layer.
- Do not add `Formula.toDefinableSet` or any notation without a concrete caller.
- Do not conflate the model-side realization set with the type-space basic open set `typesWith`.
- Do not modify `blueprint/` as part of this work unless the user explicitly requests blueprint
  changes.

## Risks and invariants

- **Declaration types of `\leanok` nodes.**  `lem:elementary-embedding-definable-set-cardinality`
  already names `realizations_embedding`, `mk_realizations_le`, `encard_realizations_eq_coe_iff`,
  and `infinite_realizations_iff` with `\leanok`.  Keep those names.  Restating their types in
  terms of `realizationSet` is definitionally neutral, but if it causes churn, add parallel
  `realizationSet`-stated lemmas instead and leave the original statements untouched.
- **Definitional transparency.**  `realizationSet` must remain a plain `def` whose body is the
  set-builder, so that `mem_realizationSet` is `Iff.rfl` and the Vaughtian restatement is
  definitionally equal to the committed one.
- **Orientation.**  Mixing `α ⊕ β` with `β ⊕ α` is the historical source of the duplication this
  plan removes.  Fix parameters-first everywhere and provide `Sum.comm`-based conversion lemmas
  only if a concrete caller needs them.
- **Import discipline.**  The `Definability` bridge must not force
  `Mathlib.ModelTheory.Definability` into the foundational `Semantics.lean`; place it under
  `DefinablyFull.lean` or a new module and keep imports acyclic.

## Estimated cost

Definition, unary specialization, membership, Boolean, relabelling, and embedding transport:
roughly 120–180 lines, dominated by `ext; simp`.  The only non-trivial proof is
`image_realizationSet_subset`, whose current unary proof transfers directly.  `VaughtianPair.lean`
should shrink.

## Validation

For Lean-only changes without new imports:

```bash
lake build MorleyCategoricityTheorem
```

If a module is added or imports change, additionally run:

```bash
lake exe mk_all --check
```

Blueprint validation is out of scope unless blueprint files are changed.

## Completion criteria

- `Formula.realizationSet` and `Formula.realizationSet₁` exist with `[simp]` membership lemmas.
- Boolean, relabelling, and elementary-embedding transport lemmas are available.
- No `sorry` is introduced.
- `VaughtianPair.lean` states its condition through `realizationSet₁` and no longer hand-writes the
  set-builder.
- Root imports reflect the current module set and remain acyclic.
- `blueprint/` is untouched unless explicitly requested.
