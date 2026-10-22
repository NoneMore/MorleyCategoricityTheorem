# Syntax-First Bridging Kernel

## Intent

Give the project a syntax-only kernel that owns the *representation* facts of first-order syntax, so
that every declaration above it is a kernel application rather than a structural induction or an
expansion-instance chain. The concrete products are

- a new module `MorleyCategoricityTheorem/ModelTheory/SyntaxKernel.lean` holding the
  arity-preserving relabel `BoundedFormula.relabelFree`, its algebra, a `mapTermRel` congruence
  lemma, the `constantsVarsEquiv` naturality family, and the currently missing law
  `Formula.onSentence_equivSentence_relabel`;
- a new module `MorleyCategoricityTheorem/ModelTheory/SemanticsKernel.lean` holding the one new
  realization lemma, `BoundedFormula.realize_relabelFree`, and its formula-level `[simp]` form;
- a rewritten proof of `LHom.realize_onSentence_equivSentence` in `ModelTheory/Semantics.lean` that
  is a syntactic rewrite and builds no expansion instance for a composite language map.

The motivating consumers are `PartialElementaryEmbedding.map_sentence`
(`ModelTheory/PartialEmbedding.lean`), which already routes through that bridge, and the ongoing
type-transport work on branch `feat/isomorphism-realized-type-counts` (commit `76d6776`, not part
of this branch), where a single proof binds a `constantsOn` structure for the source parameters, one
for the target parameters, one for the variable block, and two `IsExpansionOn` instances for
composite language maps before it can transfer one sentence.

The durable part of the plan is not the declaration list but the allocation rule it establishes:
syntax owns representation equalities and `Fin`/`castLE` arithmetic; semantics owns one lemma per
kernel; nothing above the kernel may case-split on `Term` or `BoundedFormula`. The rule is what
keeps later constructors (counting formulas, parameter binding, isomorphisms of type spaces) out of
the semantic layer.

Scope is repo-local. Mathlib is not edited, and its existing declarations keep their names,
statements, and proofs. `Formula.relabel` keeps its current definition; the kernel normal form sits
beside it and is bridged to it once.

## Facts / Observations

### The experiment and what it established

This branch archives five scratch files under `Scratch/`. All of them
compile against the pinned dependency (Mathlib `v4.34.1`, Lean `v4.34.1`); the copies used for the
checks below are byte-identical to the tracked files. `Scratch/` is not a Lake library, so none of
it participates in `lake build MorleyCategoricityTheorem`.

`Scratch/ReconSyntaxKernel.lean` (imports `Mathlib.ModelTheory.Syntax` only) proves three
representation identities:

```lean
t.relabel g = t.subst (fun a => var (g a))
φ.onTerm t = t.substFunc (fun {_} f => (φ.onFunction f).term)
φ.onBoundedFormula ψ =
  ψ.mapTermRel (fun _ => φ.onTerm) (fun _ R => φ.onRelation R) (fun _ => id)
```

`Scratch/ReconSemanticsKernel.lean` re-derives `Term.realize_relabel`, `LHom.realize_onTerm`, and
`LHom.realize_onBoundedFormula` from those identities, `Term.realize_subst`,
`Term.realize_substFunc`, `BoundedFormula.realize_mapTermRel_id`, and
`IsExpansionOn.map_onFunction`/`map_onRelation`, with no `induction` on `Term` or `BoundedFormula`.

`Scratch/ReconRelabelFree.lean` introduces the arity-preserving relabel

```lean
def relabelFree (f : α → β) {n : ℕ} : L.BoundedFormula α n → L.BoundedFormula β n :=
  mapTermRel (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)
```

and proves its functor laws, its agreement with `relabelEquiv`, and a single bridge to Mathlib's
`BoundedFormula.relabel`:

```lean
φ.relabel (Sum.inl ∘ f) = (relabelFree f φ).castLE (Nat.le_add_left n 0)
```

`Scratch/ReconSyntaxKernel2.lean` derives the `constantsVarsEquiv` naturality family and the
formula-level naturality law without any `BoundedFormula` induction.

Two further checks were run for this plan against the checked-out dependency; both compile with
`set_option autoImplicit false`, matching `lakefile.toml`:

1. The keystone holds for Mathlib's own `Formula.relabel`, not merely for the scratch stand-in:

   ```lean
   (L.lhomWithConstantsMap f).onSentence (Formula.equivSentence θ)
     = Formula.equivSentence (θ.relabel f)
   ```

2. The project bridge becomes

   ```lean
   theorem realize_onSentence_equivSentence {A : Set M} {B : Set N} (g : A → B)
       (θ : L.Formula A) :
       N ⊨ (L.lhomWithConstantsMap g).onSentence (Formula.equivSentence θ) ↔
         θ.Realize ((Subtype.val : B → N) ∘ g) := by
     rw [Formula.onSentence_equivSentence_relabel]
     let : (constantsOn B).Structure N := constantsOn.structure (Subtype.val : B → N)
     rw [Formula.realize_equivSentence, Formula.realize_relabel]
     rfl
   ```

   No hypothesis about the source structure is used by the proof: with the syntactic law in place,
   the calculation happens entirely in the target model, and the two `IsExpansionOn` instances plus
   the source `constantsOn` structure disappear.

### Where the complexity currently sits

The project's semantic layer is already induction-free: no module under
`MorleyCategoricityTheorem/ModelTheory/` except `Syntax.lean` and `ElementaryChain.lean` contains a
structural `induction`, and those are language-injectivity and direct-limit inductions, not formula
recursion. The complexity the kernel removes is therefore not project-local proof recursion; it is

- the expansion-instance chain in `realize_onSentence_equivSentence`: it builds `IsExpansionOn` for
  `constantsOnMap` and then for the composite `lhomWithConstantsMap`, even though the project
  already packages that as `LHom.lhomWithConstantsMap_isExpansionOn_of_eq`
  (`ModelTheory/LanguageMap.lean`) and the bridge does not use it;
- the absence of the naturality law, which is why any target expansion is needed at all;
- the absence of an arity-preserving relabel normal form, so formula reasoning reaches for
  `Formula.realize_relabel` plus `Sum.elim`/`Fin.castAdd_zero` side conditions.

For reference, the Mathlib bridge layer that a later upstream phase would reorganize has 21
`induction` occurrences in `Semantics.lean`, of which four are in the term/LHom/mapTermRel bridge,
and 20 `castLE` occurrences in `Syntax.lean`. The project has 16 relabel call sites across its
modules; none of them change.

### Why an arity-preserving relabel, and not a general `mapTermRel` algebra

`mapTermRel` is parameterized by an arity function `g : ℕ → ℕ`, but its composition law
`mapTermRel_mapTermRel` only holds for `g = id`. Lifting the law to a shift `g n = k + n` needs a
coherence hypothesis on the term map (`ft` must commute with `Fin.castLE`) and still costs a
`BoundedFormula` induction; `Scratch/ReconAll.lean` contains two attempts
(`mapTermRel_id_castLE`, `mapTermRel_comp_shift`) that demonstrate exactly this. The experiment
therefore takes the arity shift out of the composition algebra: `relabelFree` is `mapTermRel` at
`g = id`, its laws are induction-free, and the one unavoidable cast is confined to a single bridge
lemma. This is the design evidence behind the layer boundary, and it is why the kernel does not
attempt a general arity-shifting functor.

### What the local layer can and cannot delete

Because the target is repo-local, the kernel cannot remove Mathlib's own structural inductions
(`Term.realize_relabel`, `LHom.realize_onTerm`, `LHom.realize_onBoundedFormula`,
`realize_mapTermRel_add_castLe`). Those removals are upstream work and are recorded below as
out of scope. Locally the kernel buys three things: the missing naturality law, a cast-free normal
form for formula relabelling, and a written allocation rule that future proofs must follow.

`Mathlib/ModelTheory/Syntax.lean` on upstream `master` still defines
`Formula.relabel` as `@BoundedFormula.relabel _ _ _ 0 (Sum.inl ∘ g) 0` and has no `relabelFree`, so
the names proposed here are free today.

## Design

### Modules and import graph

```text
Mathlib.ModelTheory.Syntax
  └── SyntaxKernel                     (new; syntax only, no structures)
        ├── Syntax                     (existing; adds project constructors)
        └── SemanticsKernel            (new; needs Mathlib.ModelTheory.Semantics)
              └── Semantics            (existing; bridges and realization lemmas)
```

`SyntaxKernel` imports exactly `Mathlib.ModelTheory.Syntax`, which already provides `LHom`,
`lhomWithConstantsMap`, and `Formula.equivSentence`. Keeping it a separate module rather than
extending `Syntax.lean` makes the "syntax only" property structural: the file cannot acquire a
structure or a `Realize` reference without a visible import change, and the whole file remains a
single upstream-migration unit. `SemanticsKernel` is deliberately tiny; it exists so that the
realization kernel has one home and `Semantics.lean` stays a consumer rather than a mixed-purpose
module.

### Kernel declarations

Syntax module, in dependency order.

Representation of language maps:

```lean
theorem LHom.onBoundedFormula_eq_mapTermRel (φ : L →ᴸ L') {n : ℕ}
    (ψ : L.BoundedFormula α n) :
    φ.onBoundedFormula ψ =
      ψ.mapTermRel (fun _ => φ.onTerm) (fun _ R => φ.onRelation R) (fun _ => id)
```

The arity-preserving relabel and its algebra:

```lean
def BoundedFormula.relabelFree (f : α → β) {n : ℕ} :
    L.BoundedFormula α n → L.BoundedFormula β n :=
  mapTermRel (fun _ t => t.relabel (Sum.map f id)) (fun _ => id) (fun _ => id)

@[simp] theorem BoundedFormula.relabelFree_falsum ...
@[simp] theorem BoundedFormula.relabelFree_imp ...
@[simp] theorem BoundedFormula.relabelFree_all ...

theorem BoundedFormula.mapTermRel_congr {g : ℕ → ℕ} {φ : L.BoundedFormula α n}
    {ft ft' : ∀ n, L.Term (α ⊕ Fin n) → L'.Term (β ⊕ Fin (g n))}
    {fr fr' : ∀ n, L.Relations n → L'.Relations n}
    {h : ∀ n, L'.BoundedFormula β (g (n + 1)) → L'.BoundedFormula β (g n + 1)}
    (hft : ∀ n t, ft n t = ft' n t) (hfr : ∀ n R, fr n R = fr' n R) :
    φ.mapTermRel ft fr h = φ.mapTermRel ft' fr' h

theorem BoundedFormula.relabelFree_comp ...
theorem BoundedFormula.relabelFree_id ...
theorem BoundedFormula.relabelEquiv_eq_relabelFree ...
theorem BoundedFormula.relabelEquiv_symm_eq_relabelFree ...
```

`mapTermRel_congr` is stated for an arbitrary arity function, unlike the experiment's
identity-arity version; congruence does not need arity coherence, and the general form also serves
the shifted `relabel` if that is ever restated.

The bridge to Mathlib's relabel is the only `BoundedFormula` induction about relabelling. Together
with the `LHom.onBoundedFormula` representation lemma above and the term-level `constantsToVars`
naturality lemma further down, these are the layer's three structural inductions:

```lean
theorem BoundedFormula.relabelAux_sumInl_comp ...
theorem BoundedFormula.term_relabel_castLE ...
theorem BoundedFormula.relabel_sumInl_comp_eq_relabelFree_castLE (f : α → β)
    {n : ℕ} (φ : L.BoundedFormula α n) :
    φ.relabel (Sum.inl ∘ f) = (relabelFree f φ).castLE (Nat.le_add_left n 0)
```

Formula-fragment normal form and the constants naturality family:

```lean
theorem Formula.relabelFree_eq_relabel (f : α → β) (θ : L.Formula α) :
    BoundedFormula.relabelFree f θ = θ.relabel f

@[simp] theorem LHom.lhomWithConstantsMap_onFunction_inl ...
@[simp] theorem LHom.lhomWithConstantsMap_onFunction_inr ...
theorem LHom.lhomWithConstantsMap_onRelation_sumEmpty ...
@[simp] theorem Term.constantsToVars_inl ...
@[simp] theorem Term.constantsToVars_inr_zero ...
@[simp] theorem Term.constantsToVars_inr_succ ...
theorem Term.constantsToVars_lhomWithConstantsMap ...
theorem sumAssoc_symm_comp_sumMap ...
theorem Term.constantsVarsEquivLeft_lhomWithConstantsMap ...
theorem BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap ...
theorem Formula.constantsVarsEquiv_equivSentence ...
```

and the missing law, in kernel and Mathlib-facing forms:

```lean
theorem Formula.onSentence_equivSentence_relabelFree (f : α → β) (θ : L.Formula α) :
    (L.lhomWithConstantsMap f).onSentence (Formula.equivSentence θ) =
      Formula.equivSentence (BoundedFormula.relabelFree f θ)

theorem Formula.onSentence_equivSentence_relabel (f : α → β) (θ : L.Formula α) :
    (L.lhomWithConstantsMap f).onSentence (Formula.equivSentence θ) =
      Formula.equivSentence (θ.relabel f)
```

Semantics module:

```lean
theorem BoundedFormula.realize_relabelFree [L.Structure M] {n : ℕ}
    {φ : L.BoundedFormula α n} {g : α → β} {v : β → M} {xs : Fin n → M} :
    (BoundedFormula.relabelFree g φ).Realize v xs ↔ φ.Realize (v ∘ g) xs :=
  BoundedFormula.realize_mapTermRel_id
    (fun n t xs => by simp [Term.realize_relabel, Sum.elim_comp_map]) fun n R x => rfl

@[simp] theorem Formula.realize_relabelFree [L.Structure M] {φ : L.Formula α}
    {g : α → β} {v : β → M} :
    Formula.Realize (BoundedFormula.relabelFree g φ) v ↔ φ.Realize (v ∘ g) :=
  BoundedFormula.realize_relabelFree
```

Only the formula-level form is tagged `[simp]`; the bounded form is the `rw`/kernel entry point, and
tagging both would put two syntactically identical simp entries on the same goal shape.

### Simp and normal-form policy

- `relabelFree_falsum`, `relabelFree_imp`, `relabelFree_all` are the computation lemmas; they are
  `rfl` because `relabelFree` applies `mapTermRel` with the identity arity function.
- `relabelFree_comp`, `relabelFree_id`, and the two `relabelEquiv` comparisons stay off the simp
  set. They are normalization choices, not computational facts, and a global `relabelFree_comp`
  would rewrite every nested relabel in unrelated goals.
- `Formula.relabelFree_eq_relabel` stays off the simp set for the same reason: it would change the
  normal form of every `Formula.relabel` in the repository at once. It is used explicitly by the
  keystone and by code that has to cross the Mathlib boundary.
- `Formula.realize_relabelFree` is the one new `[simp]` lemma. It rewrites a `relabelFree` into the
  kernel form and cannot loop, since the right-hand side mentions no relabel.
- `relabelFree` is a `def`, not an `abbrev`. An `abbrev` would unfold during `simp` and reintroduce
  `mapTermRel`/`castLE` noise in exactly the goals the layer exists to keep clean.

### Consumer migration

`ModelTheory/Semantics.lean`, `LHom.realize_onSentence_equivSentence`: keep the statement, replace
the proof with the four-line rewrite verified above. The docstring should then say that the
identification is syntactic and that no temporary source structure is needed.

`ModelTheory/Syntax.lean`: the `## TODO` entry asking for the naturality law

```lean
(L.lhomWithConstantsMap f).onSentence (Formula.equivSentence θ)
  = Formula.equivSentence (θ.relabel f)
```

is replaced by a pointer to this plan, per the plan lifecycle.

`ModelTheory/PartialEmbedding.lean` and `ModelTheory/Types.lean`: no changes. Their statements and
proofs use the bridge and `Formula.realize_relabel` as before.

New project declarations about parameter renaming or formula relabelling state themselves through
`relabelFree` and prove themselves with `Formula.realize_relabelFree`; `Formula.relabel` appears
only where a Mathlib declaration requires that exact term. This is the boundary rule, and it is what
makes the next bridge a two-line proof instead of another instance chain.

### Rejected alternatives

- **Generalizing `mapTermRel_mapTermRel` to arity shifts.** Rejected: it needs a coherence
  hypothesis on the term map and two extra inductions (`Scratch/ReconAll.lean`), and it makes every
  later use carry a proof obligation that the `relabelFree` route discharges once.
- **Making `relabelFree` an `abbrev`, or defining it through `mapTermRelEquiv`.** Rejected:
  `g = id` needs neither an equivalence nor unfolding; both variants buy nothing and cost the
  `rfl` computation lemmas.
- **Shipping `Term.relabel_eq_subst` and `LHom.onTerm_eq_substFunc` now.** Deferred, not rejected:
  their only payoff is deleting Mathlib's `Term.realize_relabel` and `LHom.realize_onTerm` proofs,
  which a repo-local layer cannot do. They are the first additions of an upstream increment.
- **Changing `Formula.relabel` to `relabelFree`.** Deferred. The archived diff
  `Scratch/relabel_arity_preserving.diff` shows the change is small but not free: it rewrites the
  definition, adds `realize_relabelFree` as a simp lemma, and repairs two downstream simp scripts
  (`Mathlib/FieldTheory/AxGrothendieck.lean`, `Mathlib/ModelTheory/ElementarySubstructures.lean`).
  That change belongs to an upstream phase and is not made here.

### Deferred increments

Reserve, to be added with the first caller: `LHom.onTerm_relabel`,
`LHom.onBoundedFormula_relabelFree`, and the `Formula`-level naturality law for `LHom` against
`relabelFree`. The experiment proves all three; no current project declaration consumes them.

Upstream increment, out of scope here: the three representation identities, the three
induction removals (`Term.realize_relabel`, `LHom.realize_onTerm`, `LHom.realize_onBoundedFormula`),
`realize_relabel` restated through `relabelFree`, and the optional definitional switch.

## Specs / Constraints

### Non-goals

- Do not modify Mathlib, `.lake/packages/`, or `lake-manifest.json`.
- Do not change the statement of any existing project declaration, including
  `LHom.realize_onSentence_equivSentence`.
- Do not redefine `Formula.relabel`, and do not add a simp lemma that rewrites it.
- Do not restate Mathlib lemmas under new names. The kernel adds only declarations Mathlib does not
  have.
- Do not migrate existing `Formula.relabel` call sites; the boundary rule applies to new code.
- Do not modify `blueprint/`. No blueprint node references the declarations involved, so no
  declaration check is triggered.
- Do not add the reserve or upstream declarations without a caller or an explicitly authorized
  upstream phase.

### Invariants

- **Import discipline.** `SyntaxKernel` imports `Mathlib.ModelTheory.Syntax` and nothing else. It
  contains no `Structure`, `Realize`, or `Set.Definable` reference.
- **Allocation rule.** No module importing `Mathlib.ModelTheory.Semantics` may contain a structural
  `induction` on `Term` or `BoundedFormula`. A new constructor that needs one must express it as a
  syntax representation lemma in `SyntaxKernel` and realize it through a kernel.
- **No cast in statements above the kernel.** Project statements that mention `relabelFree` carry no
  `castLE`, `Nat.zero_add`, or `Fin.castAdd_zero`.
- **Name-collision policy.** `relabelFree` and `realize_relabelFree` are names a future Mathlib
  addition would plausibly take. If upstream lands them, delete the local declarations and the
  local import edge in the same commit; the build fails loudly on a duplicate, so this cannot be
  missed silently.
- **Elaboration note.** At arity `0`, `Formula α` and `BoundedFormula α 0` are definitionally equal,
  so dot notation `(… : L.Formula β).Realize v` still resolves to `BoundedFormula.Realize` and
  leaves a `Fin 0 → M` argument. Write `Formula.Realize …` explicitly in the formula-level lemma.

### Risks

- `mapTermRel_congr` is proved by `funext` plus rewriting, so it is cheap but brittle if Mathlib
  ever changes the binder order of `mapTermRel`. A rebuild failure would be local to the kernel.
- `Term.constantsToVars_lhomWithConstantsMap` is the one term-level induction, and it case-splits on
  the arity of the constant symbols (`0` versus `n + 1`, the latter eliminated by `isEmptyElim`).
  If the representation of `constantsOn` changes, this proof is the first to break.
- The keystone is an equality of sentences obtained through injectivity of
  `BoundedFormula.constantsVarsEquiv`. If that equivalence is ever restated with a different
  variable order, the last `congr 1` in its proof needs revisiting.
- Adding `Formula.realize_relabelFree` as `[simp]` widens the simp set for goals that mention
  `relabelFree`. Nothing else in the project produces that term yet, so the blast radius is the new
  code.

## Implementation / Verification

### File plan

1. `MorleyCategoricityTheorem/ModelTheory/SyntaxKernel.lean` (new)
   - the representation lemma for `LHom.onBoundedFormula`;
   - `relabelFree` and its computation, composition, identity, and equivalence laws;
   - `mapTermRel_congr`;
   - the cast bridge to `BoundedFormula.relabel` and `Formula.relabelFree_eq_relabel`;
   - the constants-renaming computation lemmas and the `constantsVarsEquiv` naturality family;
   - `Formula.onSentence_equivSentence_relabelFree` and `Formula.onSentence_equivSentence_relabel`.
2. `MorleyCategoricityTheorem/ModelTheory/SemanticsKernel.lean` (new)
   - `BoundedFormula.realize_relabelFree` and the `[simp]` formula form.
3. `MorleyCategoricityTheorem/ModelTheory/Semantics.lean`
   - import `SemanticsKernel`; replace the proof of `LHom.realize_onSentence_equivSentence`; update
     its docstring and the module summary.
4. `MorleyCategoricityTheorem/ModelTheory/Syntax.lean`
   - replace the `## TODO` entry for the naturality law with a pointer to this plan; list
     `relabelFree` in the module summary.
5. `MorleyCategoricityTheorem.lean`
   - add the two module imports in alphabetical position.

### Implementation order

1. `SyntaxKernel`: `relabelFree`, its three computation lemmas, `mapTermRel_congr`,
   `relabelFree_comp`, `relabelFree_id`, the two `relabelEquiv` comparisons.
2. `SyntaxKernel`: `relabelAux_sumInl_comp`, `term_relabel_castLE`, and the cast bridge; then
   `Formula.relabelFree_eq_relabel`.
3. `SemanticsKernel`: `realize_relabelFree` and its formula form; check that the proof is a kernel
   application with no case split.
4. `Semantics.lean`: replace the bridge proof and confirm the statement is untouched.
5. `SyntaxKernel`: the `LHom.onBoundedFormula` representation lemma and the constants-renaming
   computation lemmas.
6. `SyntaxKernel`: `Term.constantsToVars_lhomWithConstantsMap`, `sumAssoc_symm_comp_sumMap`,
   `Term.constantsVarsEquivLeft_lhomWithConstantsMap`,
   `BoundedFormula.constantsVarsEquiv_lhomWithConstantsMap`.
7. `SyntaxKernel`: `Formula.constantsVarsEquiv_equivSentence`, then the keystone in both forms.
8. Documentation: module headers, the `Syntax.lean` pointer, and the root imports.

### Estimated cost

Roughly 200–240 lines of new Lean, of which three declarations carry a structural induction and are
each under ten lines. `Semantics.lean` loses three bindings and one `let`. The bulk is the constants
naturality family; if it is deferred, the keystone is unavailable and the plan's main consumer
disappears, so it is not splittable below the keystone.

### Verification

```bash
lake build MorleyCategoricityTheorem
lake exe mk_all --check
```

`mk_all --check` is required because two modules are added. No blueprint declaration changes, so
`lake exe checkdecls blueprint/lean_decls` is not triggered; if a future increment renames a
blueprint-referenced declaration, add that check.

An additional review check enforces the allocation rule:

```bash
grep -rn "induction" MorleyCategoricityTheorem/ModelTheory/
```

Today this prints the four direct-limit inductions in `ElementaryChain.lean` and the two
language-injectivity inductions in `Syntax.lean`. After the change it may print the same six plus
the three kernel inductions in `SyntaxKernel.lean`; any other hit, in particular in `Semantics.lean`
or `SemanticsKernel.lean`, violates the rule. This is a review aid, not a CI gate.

### Completion criteria

- `BoundedFormula.relabelFree`, `Formula.relabelFree_eq_relabel`,
  `Formula.onSentence_equivSentence_relabel`, and `BoundedFormula.realize_relabelFree` exist with
  module documentation.
- `LHom.realize_onSentence_equivSentence` has an unchanged statement and a proof containing no
  `IsExpansionOn` binding and no `constantsOn A` structure.
- No `induction` on `Term` or `BoundedFormula` appears outside `SyntaxKernel`, except the two
  language-injectivity inductions already present in `Syntax.lean`.
- No `sorry` is introduced; no existing statement changes; `blueprint/` is untouched.
- Root imports reflect the module set, remain acyclic, and both validation commands pass.

### Rollback

The layer is additive. Reverting the three source edits and deleting the two new modules restores
the previous state; no Mathlib file, dependency, or declaration type is affected.
