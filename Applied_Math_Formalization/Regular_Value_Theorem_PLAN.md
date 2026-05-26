# Regular Value Theorem — proof plan & next steps

Working notes for completing `Regular_Value_Theorem.thy` and using it to discharge
the transversality keystone `regular_zero_set_projection_local_chart_2d` in
`Parametric_Transversality_Euclidean_Base.thy`.

**Architecture (per project decision):** standard/famous results (rank–nullity,
augmentation-to-bijection, the regular-value chart) live in the self-contained
`Regular_Value_Theorem.thy` (imports `HOL-Analysis.Derivative` only), so the module
is AFP-submittable on its own. `Parametric_*` imports it and specializes.

**Always pin existential witness types** (the lesson from `countable_chart_cover`):
an unannotated `∃U φ …` lets the chart-domain type generalize to a schematic
variable, making the statement claim a chart for *every* domain type — false by
invariance of domain, hence unprovable. The keystone's `shows` and `loc` are already
pinned to `real^'m`.

## Current state
- `Regular_Value_Theorem.thy`: two `sorry` lemmas — `dim_kernel_surj`,
  `linear_surj_augment_to_bij`.
- Keystone in `Parametric_*`: `shows` type-pinned, proof still `sorry`.
- A stray duplicate `exists_aug_proj_2d` was added to `Parametric_*` before the
  separate-theory decision — **DELETE it**; make `Parametric_*` import
  `Regular_Value_Theorem` and use `linear_surj_augment_to_bij`.

## STEP 0 (do first): restate with a product domain `'c × 'b`
`inverse_function_theorem` (`Derivative.thy:3031`) requires `f :: 'a ⇒ 'a` (same
type). State everything with domain `'c × 'b`, codomain `'b`. Then
`F z = (π z, G z) : ('c×'b) ⇒ ('c×'b)` is an **endomorphism** (same type), the
keystone's `real^'m × real^2` matches with `'c = real^'m`, `'b = real^2`, the
`DIM('c)+DIM('b)=DIM('a)` hypothesis becomes automatic, and `eucl.linear_inj_imp_surj`
applies directly (no cross-type inj⇒surj). Restate:
```isabelle
lemma linear_surj_augment_to_bij:
  fixes L :: "('c::euclidean_space × 'b::euclidean_space) ⇒ 'b"
  assumes "linear L" "surj L"
  shows "∃π::('c×'b) ⇒ 'c. linear π ∧ bij (λz. (π z, L z))"
```

## STEP 1 — `dim_kernel_surj` (Euclidean rank–nullity)  [hardest helper]
`linear f ⟹ surj f ⟹ dim {x. f x = 0} = DIM('a) - DIM('b)`. Not ready-made in
HOL-Analysis (only hyperplane cases; abstract `rank_nullity_theorem` is in
`HOL-Algebra`).
- Try `sledgehammer` first.
- `find_theorems` to try: `"dim (?f ` UNIV)"`; `name:linear "dim {x. _ = 0}"`;
  `"dim (?f ` ?S) = dim ?S"`; `name:dim_image`.
- Fallbacks: (a) extend a basis of `ker f` to a basis of the domain via
  `linear_independent_extend`; images of the extension are independent and span the
  range; count dimensions. (b) `orthogonal_subspace_decomp_exists`
  (`Linear_Algebra.thy:1467`): domain = `ker f ⊕ (ker f)^⊥`, and `f` restricted to
  `(ker f)^⊥` is an isomorphism onto the range.

## STEP 2 — `linear_surj_augment_to_bij` (given Step 1)
- `subspace {x. L x = 0}` (`find_theorems "subspace {x. ?f x = 0}"`; likely
  `subspace_kernel`, else `unfolding subspace_def` from linearity).
- `dim {x. L x = 0} = DIM('c)` from Step 1 + `DIM('c×'b)=DIM('c)+DIM('b)`.
- `thm subspace_isomorphism` (get exact statement via eval_at; referenced in
  `Affine.thy`, `Convex_Euclidean_Space.thy:1729`). It yields `π` with `linear π`,
  `π ` {x. L x = 0} = UNIV`, `inj_on π {x. L x = 0}`.
- `linear (λz. (π z, L z))` (`find_theorems "linear (λx. (?f x, ?g x))"`).
- injective: `(π z, L z) = 0 ⟹ z = 0` — `L z = 0 ⟹ z ∈ ker`; `π z = 0 = π 0`;
  `inj_on π ker` + `0 ∈ ker` ⟹ `z = 0`; lift to full injectivity by linearity.
- inj ⇒ bij: endomorphism (same type now) — `eucl.linear_inj_imp_surj`, then
  `bij = inj ∧ surj`.

## STEP 3 — `aug_local_diffeo`
From `regular_value_on G (V×Ω) 0` and `p ∈ M`, the derivative `DG p` is surjective
linear. Get `π` from Step 2 with `L = DG p`. Set `F z = (π z, G z)`; then
`DF p = (λv. (π v, DG p v))` is a bijection ⟹ invertible blinfun ⟹ apply
`inverse_function_theorem` (open set; `(F has_derivative …) (at z)`; `continuous_on`
of the derivative; `invf o⁠L f' x0 = id_blinfun`). Obtain local diffeo `F : U' → W`,
inverse `g`. For blinfun packaging use `linear_conv_bounded_linear` (finite dim) and
mirror how existing `inverse_function_theorem` callers construct `invf`.

## STEP 4 — `chart_from_diffeo` ⟹ the keystone
Chart `φ u = g (u, 0)`, `U = {u. (u,0) ∈ W}` (open: `W` open, `(λu.(u,0))`
continuous), `u0 = π p`. Discharge: `φ u0 = p` (since `F p = (π p, 0)` as `G p = 0`,
and `g∘F = id` on `U'`); `φ ` U ⊆ M` (the 2nd slot of `F(φ u)` is 0 ⟹ `G(φ u)=0`);
`differentiable_on`; `openin (top_of_set M) (φ ` U)`; `homeomorphism U (φ ` U) φ g'`
by restricting the `F`/`g` diffeomorphism.

## Verifying (heap cached)
From `Applied_Math_Formalization/`, using
`/home/dusty/Desktop/Isabelle/Isabelle2025-2/bin/isabelle`:
```
isabelle eval_at -d ../Imported_Munkres_Topology -d . -l Applied_Math_Base \
  Regular_Value_Theorem.thy <LINE> '<command>'
```
To `sledgehammer`/inspect a goal, the proof state must be OPEN at `<LINE>` ("No proof
state" = injected past the goal; temporarily replace `sorry` with the command).
Full build: temp-ROOT swap → session `Applied_Math_Nonemptiness` with the theory under
test, `quick_and_dirty=true` (other sorries allowed; real errors still surface);
restore ROOT after.
