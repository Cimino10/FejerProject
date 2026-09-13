# Fejér's Theorem on `AddCircle` in Lean 4

## Overview

This development formalizes Fejér's theorem for continuous complex-valued functions on `AddCircle T`. For a positive period `T`, it proves that the Cesàro means of the symmetric Fourier partial sums converge uniformly to the original function.

The proof follows the classical approximate-identity argument. It defines the Fejér means and Fejér kernel explicitly, proves that the kernel is real and nonnegative with normalized Haar integral equal to one, proves concentration of the kernel near the origin, rewrites the Fejér means as convolution with the kernel, and finally controls the approximation error by splitting the convolution integral into a neighborhood of the origin and its complement.

The final result is presented in three forms: an explicit uniform ε-N estimate, convergence in the sup-norm topology on bundled continuous maps, and mathlib's `TendstoUniformly` formulation.

## Mathematical setting

The main convergence results are stated for

```lean
{T : ℝ} [Fact (0 < T)]
f : C(AddCircle T, ℂ)
```

The positivity assumption supplies the compact positive-period circle structure needed by Fourier coefficients, normalized Haar integration, and the sup norm on continuous maps. Several purely algebraic or pointwise kernel lemmas are proved without this assumption; in particular, much of the kernel algebra is enclosed in `omit [Fact (0 < T)]`, and the pointwise lemmas `norm_fejerKernel_mul_diff_le_of_diff_le`, `norm_fejerKernel_mul_diff_le_on_neighborhood`, and `norm_fejerKernel_eq_re` are stated for arbitrary real `T`.

## Core definitions

`fourierIndices n` is the symmetric finite set of Fourier modes from `-n` through `n`. Using this set, `fourierPartialSum f n x` is the symmetric Fourier partial sum

\[
S_n f(x)=\sum_{|k|\le n}\widehat f(k)e_k(x).
\]

The Fejér mean `fejerMean f n x` is the Cesàro average of the first `n + 1` partial sums,

\[
\sigma_n f(x)=\frac{1}{n+1}\sum_{j=0}^{n}S_jf(x).
\]

The development also defines `fejerKernel n x` by its finite weighted Fourier expansion and `fourierPrefix n x` as the sum of the nonnegative Fourier modes from `0` through `n`. The auxiliary finite set `differencePairs n m` records pairs of indices whose difference is `m`; it is used to reorganize the square of the Fourier prefix into the weighted Fourier expansion of the Fejér kernel.

## Proof architecture

### Fourier partial sums and Fejér means

The first section establishes the finite-index bookkeeping needed for Cesàro averaging. It characterizes membership in `fourierIndices`, computes partial sums on a single Fourier mode, counts how often a mode appears among the partial sums, and derives `fejerMean_fourier_eq_weighted`. This identifies the familiar Fejér weight

\[
\frac{n+1-|m|}{n+1}
\]

for each mode with `|m| ≤ n`.

### Algebraic form and positivity of the Fejér kernel

The next section proves the algebraic identity behind positivity. The finite product `fourierPrefix * star fourierPrefix` is expanded as a double sum. The `differencePairs` lemmas count the number of pairs with a prescribed difference, allowing the double sum to be regrouped by Fourier mode.

This yields `fejerKernel_eq_prefix_mul_star` and then

\[
F_n(x)=\frac{1}{n+1}\,\lvert P_n(x)\rvert^2,
\]

formalized by `fejerKernel_eq_normSq`. From this representation the development proves `fejerKernel_im` and `fejerKernel_nonneg`: the Fejér kernel is real-valued and nonnegative.

### Normalization

The normalization section computes the Haar integral of each Fourier mode. The zero mode integrates to one and every nonzero mode integrates to zero. Applying this termwise to the weighted Fourier expansion gives

\[
\int F_n\,d\mu=1,
\]

formalized as `integral_fejerKernel`.

### Concentration away from the origin

The Fourier prefix is rewritten as a finite geometric sum. From

\[
P_n(x)(e_1(x)-1)=e_{n+1}(x)-1
\]

and the fact that every Fourier mode has norm one, the proof obtains a pointwise estimate for `x` away from the origin:

\[
F_n(x)\le
\frac{4}{(n+1)\,\lVert e_1(x)-1\rVert^2}.
\]

On a compact set not containing zero, continuity gives a positive lower bound for `‖fourier 1 x - 1‖`. The estimate therefore tends uniformly to zero there. This is packaged as `fejerKernel_tendsto_zero_uniformly_on_compact`, and then as `fejerKernel_tendsto_zero_uniformly_outside_neighborhood` for the complement of any open neighborhood of zero.

### Convolution representation

The next section connects the finite Fourier definition of the Fejér mean with Haar convolution. Translation identities for the Fourier modes and invariance of Haar measure give the key integral identity for a Fourier mode. After exchanging a finite sum and the integral, the weighted Fourier expansion is recovered.

The resulting theorem is

```lean
fejerMean_eq_integral_fejerKernel
```

which states

\[
\sigma_n f(x)=\int F_n(y)f(x-y)\,d\mu(y).
\]

### Error representation and local/far estimates

Using the normalization `∫ F_n = 1`, the convolution formula is rewritten as

\[
\sigma_n f(x)-f(x)
 =\int F_n(y)\bigl(f(x-y)-f(x)\bigr)\,d\mu(y),
\]

formalized by `fejerMean_sub_eq_integral`.

Uniform continuity of `f` supplies an open neighborhood `U` of zero on which `‖f (x-y) - f x‖` is uniformly small for every `x`. The error integral is then split over `U` and `Uᶜ`.

On `U`, positivity and total mass one of the kernel control the restricted integral directly; this is `norm_integral_fejerKernel_mul_diff_on_neighborhood_le`. On `Uᶜ`, the crude bound

\[
\lVert f(x-y)-f(x)\rVert\le 2\lVert f\rVert
\]

is combined with uniform decay of the kernel away from zero. This produces `norm_integral_fejerKernel_mul_diff_outside_neighborhood_le`.

### Fejér's theorem

The final theorem `fejerMean_uniform_error_lt` combines the near and far estimates. For a target `ε > 0`, the proof applies uniform continuity with `ε / 4` and sets

\[
\delta=\frac{\varepsilon}{8(\lVert f\rVert+1)}.
\]

The near integral is bounded by `ε / 4`, while the far integral is eventually bounded by `2 ‖f‖ δ ≤ ε / 4`. After splitting the error integral and applying the triangle inequality, the total error is strictly less than `ε`, uniformly in `x` for all sufficiently large `n`.

The explicit estimate is then packaged in two standard topological forms. `tendsto_fejerMeanContinuous` states convergence of the bundled continuous maps in the sup-norm topology, while `tendstoUniformly_fejerMean` states uniform convergence using mathlib's `TendstoUniformly` predicate.

## Main reusable interface

| Declaration | Role |
| --- | --- |
| `fourierPartialSum` | Symmetric Fourier partial sum |
| `fejerMean` | Cesàro mean of the first `n + 1` partial sums |
| `fejerKernel` | Finite weighted Fourier representation of the Fejér kernel |
| `fejerKernel_nonneg` | Nonnegativity of the real part of the kernel |
| `integral_fejerKernel` | Kernel normalization `∫ F_n = 1` |
| `fejerKernel_tendsto_zero_uniformly_on_compact` | Uniform decay on compact sets avoiding zero |
| `fejerMean_eq_integral_fejerKernel` | Convolution representation of the Fejér mean |
| `fejerMean_sub_eq_integral` | Integral representation of the approximation error |
| `fejerMean_uniform_error_lt` | Explicit uniform ε-N form of Fejér's theorem |
| `fejerMeanContinuous` | Fejér mean bundled as a continuous map |
| `tendsto_fejerMeanContinuous` | Sup-norm convergence of the bundled Fejér means |
| `tendstoUniformly_fejerMean` | Uniform convergence in mathlib's native formulation |

## Internal proof infrastructure

A substantial part of the file is supporting infrastructure rather than the public mathematical interface. The `differencePairs` cardinality lemmas and finite-sum rearrangements establish the algebraic kernel formula. Several integrability lemmas justify the Haar-integral manipulations, and the local/far pointwise inequalities feed into the restricted-integral estimates. These declarations are intentionally explicit: they expose the intermediate steps required by Lean while keeping the final convergence theorems close to the standard analytic proof.

## Result

For every continuous function `f : C(AddCircle T, ℂ)` with positive period `T`, the Fejér means of its Fourier series converge uniformly to `f`. The formalization proves this constructively through the classical Fejér-kernel argument rather than by invoking a more general approximation theorem.
