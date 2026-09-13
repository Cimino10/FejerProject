/-
Copyright (c) 2026 Nicholas Cimino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicholas Cimino
-/

import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Fejér's theorem on `AddCircle`

This file proves Fejér's theorem for continuous complex-valued functions on
`AddCircle T`: when `T > 0`, the Cesàro means of the symmetric Fourier partial
sums converge uniformly to the original function.

The proof follows the classical Fejér-kernel argument. We:

* define symmetric Fourier partial sums and their Cesàro means;
* define the Fejér kernel and prove its representation as a normalized squared
  Fourier prefix;
* deduce that the kernel is real and nonnegative;
* prove that its normalized Haar integral is one;
* establish uniform decay of the kernel on compact sets away from the origin;
* express the Fejér means as convolution with the Fejér kernel;
* rewrite the approximation error as an integral against
  `f (x - y) - f x`;
* split this integral into a neighborhood of the origin and its complement,
  controlling the two pieces by uniform continuity and kernel concentration.

The main convergence results are:

* `fejerMean_uniform_error_lt`: explicit uniform `ε`-`N` convergence;
* `tendsto_fejerMeanContinuous`: convergence in the sup-norm topology on
  continuous maps;
* `tendstoUniformly_fejerMean`: uniform convergence expressed using
  `TendstoUniformly`.

Important intermediate results include `integral_fejerKernel`,
`fejerKernel_tendsto_zero_uniformly_on_compact`,
`fejerMean_eq_integral_fejerKernel`, and `fejerMean_sub_eq_integral`.

Several algebraic and pointwise kernel lemmas are proved without the positivity
assumption on `T`; positivity is retained where the compact-circle, Fourier
coefficient, Haar-measure, or sup-norm infrastructure requires it.
-/

open scoped BigOperators
open MeasureTheory

namespace AddCircle

variable {T : ℝ} [Fact (0 < T)]
/-!
## Fourier partial sums and Fejér means

We begin with the symmetric Fourier index sets, partial Fourier sums, and the
Cesàro averages that define the Fejér means.
-/

/-- The symmetric set of Fourier modes from `-n` through `n`. -/
noncomputable def fourierIndices (n : ℕ) : Finset ℤ :=
Finset.Icc (-(n : ℤ)) n

lemma mem_fourierIndices {n : ℕ} {k : ℤ} :
    k ∈ fourierIndices n ↔ -(n : ℤ) ≤ k ∧ k ≤ n := by
  simp [fourierIndices]

lemma mem_fourierIndices_iff_natAbs_le
    (n : ℕ) (m : ℤ) :
    m ∈ fourierIndices n ↔ m.natAbs ≤ n := by
  rw [mem_fourierIndices]
  omega

/-- The `n`th symmetric partial Fourier sum of `f` on `AddCircle T`. -/
noncomputable def fourierPartialSum
    (f : AddCircle T → ℂ)
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ k ∈ fourierIndices n,
    fourierCoeff f k * fourier k x

private theorem fourierPartialSum_fourier_of_mem
    (n : ℕ) (m : ℤ)
    (hm : m ∈ fourierIndices n) :
    fourierPartialSum (T := T) ⇑(fourier m) n = ⇑(fourier m) := by
  funext x
  simp [fourierPartialSum, fourierCoeff_fourier, Pi.single_apply, hm]

private theorem fourierPartialSum_fourier_of_not_mem
    (n : ℕ) (m : ℤ)
    (hm : m ∉ fourierIndices n) :
    fourierPartialSum (T := T) ⇑(fourier m) n = 0 := by
  funext x
  simp [fourierPartialSum, fourierCoeff_fourier, Pi.single_apply, hm]

theorem fourierPartialSum_fourier
    (n : ℕ) (m : ℤ) :
    fourierPartialSum (T := T) ⇑(fourier m) n =
      if m ∈ fourierIndices n then ⇑(fourier m) else 0 := by
  by_cases hm : m ∈ fourierIndices n
  · simp [hm, fourierPartialSum_fourier_of_mem]
  · simp [hm, fourierPartialSum_fourier_of_not_mem]

/-- The `n`th Fejér mean, defined as the average of the first `n + 1`
    symmetric Fourier partial sums. -/
noncomputable def fejerMean
    (f : AddCircle T → ℂ)
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  (((n + 1 : ℕ) : ℂ)⁻¹) *
    ∑ j ∈ Finset.range (n + 1),
      fourierPartialSum (T := T) f j x

private theorem fejerMean_fourier
    (n : ℕ) (m : ℤ) :
    fejerMean (T := T) ⇑(fourier m) n =
      fun x =>
        (((n + 1 : ℕ) : ℂ)⁻¹) *
          ∑ j ∈ Finset.range (n + 1),
            if m ∈ fourierIndices j then fourier m x else 0 := by
  funext x
  unfold fejerMean
  apply congrArg
    (fun z : ℂ => (((n + 1 : ℕ) : ℂ)⁻¹) * z)
  apply Finset.sum_congr rfl
  intro j hj
  rw [fourierPartialSum_fourier (T := T) j m]
  by_cases h : m ∈ fourierIndices j
  · simp [h]
  · simp [h]

private lemma card_filter_natAbs_le
    (n : ℕ) (m : ℤ) :
    ((Finset.range (n + 1)).filter (fun j => m.natAbs ≤ j)).card =
      n + 1 - m.natAbs := by
  have hfilter :
      (Finset.range (n + 1)).filter (fun j => m.natAbs ≤ j) =
        Finset.Icc m.natAbs n := by
    ext j
    simp
    omega
  rw [hfilter]
  simp

private lemma sum_indicator
    (n : ℕ) (m : ℤ) (c : ℂ) :
    (∑ j ∈ Finset.range (n + 1),
        if m ∈ fourierIndices j then c else 0) =
      ((n + 1 - m.natAbs : ℕ) : ℂ) * c := by
  simp only [mem_fourierIndices_iff_natAbs_le]
  rw [← Finset.sum_filter]
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [card_filter_natAbs_le]

theorem fejerMean_fourier_eq_weighted
    (n : ℕ) (m : ℤ) :
    fejerMean (T := T) ⇑(fourier m) n =
      fun x =>
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourier m x) := by
  funext x
  rw [fejerMean_fourier (T := T) n m]
  change
    (((n + 1 : ℕ) : ℂ)⁻¹) *
        (∑ j ∈ Finset.range (n + 1),
          if m ∈ fourierIndices j then
            (fourier m : C(AddCircle T, ℂ)) x
          else 0) =
      (((n + 1 - m.natAbs : ℕ) : ℂ) /
        ((n + 1 : ℕ) : ℂ)) *
        (fourier m : C(AddCircle T, ℂ)) x
  rw [sum_indicator]
  rw [div_eq_mul_inv]
  ring

/-!
## Algebraic form of the Fejér kernel

This section introduces the Fejér kernel and rewrites it in terms of the square
of a finite Fourier prefix. The combinatorial lemmas below count pairs of
indices with a prescribed difference.
-/

/-- The Fejér kernel on `AddCircle T`, written as its finite weighted Fourier expansion. -/
noncomputable def fejerKernel
    {T : ℝ}
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ m ∈ fourierIndices n,
    ((((n + 1 - m.natAbs : ℕ) : ℂ) /
      ((n + 1 : ℕ) : ℂ)) *
      fourier m x)

/-- The finite sum of the nonnegative Fourier modes from `0` through `n`. -/
noncomputable def fourierPrefix
    (n : ℕ)
    (x : AddCircle T) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    fourier (k : ℤ) x

omit [Fact (0 < T)] in
lemma star_fourierPrefix
    (n : ℕ) (x : AddCircle T) :
    starRingEnd ℂ (fourierPrefix (T := T) n x) =
      ∑ k ∈ Finset.range (n + 1),
        fourier (-(k : ℤ)) x := by
  unfold fourierPrefix
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_neg]

omit [Fact (0 < T)] in
lemma fourierPrefix_mul_star
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x *
        starRingEnd ℂ (fourierPrefix (T := T) n x) =
      ∑ j ∈ Finset.range (n + 1),
        ∑ k ∈ Finset.range (n + 1),
          fourier ((j : ℤ) - (k : ℤ)) x := by
  rw [star_fourierPrefix]
  unfold fourierPrefix
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  rw [← fourier_add]
  ring_nf

/-- The pairs of indices in `0, ..., n` whose integer difference is `m`. -/
noncomputable def differencePairs
    (n : ℕ) (m : ℤ) : Finset (ℕ × ℕ) :=
  ((Finset.range (n + 1)).product (Finset.range (n + 1))).filter
    (fun p => (p.1 : ℤ) - (p.2 : ℤ) = m)

lemma card_differencePairs_of_nonneg
    (n r : ℕ) :
    (differencePairs n (r : ℤ)).card =
      n + 1 - r := by
  classical
  by_cases hr : r ≤ n
  · calc
      (differencePairs n (r : ℤ)).card =
          (Finset.range (n + 1 - r)).card := by
        apply Finset.card_bij (fun p _ => p.2)
        · intro p hp
          have hp' := hp
          simp [differencePairs] at hp'
          simp only [Finset.mem_range]
          omega
        · intro p₁ hp₁ p₂ hp₂ h
          have hp₁' := hp₁
          have hp₂' := hp₂
          simp [differencePairs] at hp₁' hp₂'
          apply Prod.ext
          · omega
          · exact h
        · intro k hk
          simp only [Finset.mem_range] at hk
          refine ⟨(k + r, k), ?_, ?_⟩
          · simp [differencePairs]
            omega
          · rfl
      _ = n + 1 - r := by
        simp
  · have hr' : n < r := Nat.lt_of_not_ge hr
    have hempty : differencePairs n (r : ℤ) = ∅ := by
      ext p
      simp [differencePairs]
      omega
    rw [hempty]
    simp
    omega

lemma card_differencePairs_of_neg
    (n r : ℕ) :
    (differencePairs n (-(r : ℤ))).card =
      n + 1 - r := by
  classical
  by_cases hr : r ≤ n
  · calc
      (differencePairs n (-(r : ℤ))).card =
          (Finset.range (n + 1 - r)).card := by
        apply Finset.card_bij (fun p _ => p.1)
        · intro p hp
          have hp' := hp
          simp [differencePairs] at hp'
          simp only [Finset.mem_range]
          omega
        · intro p₁ hp₁ p₂ hp₂ h
          have hp₁' := hp₁
          have hp₂' := hp₂
          simp [differencePairs] at hp₁' hp₂'
          apply Prod.ext
          · exact h
          · omega
        · intro j hj
          simp only [Finset.mem_range] at hj
          refine ⟨(j, j + r), ?_, ?_⟩
          · simp [differencePairs]
            omega
          · rfl
      _ = n + 1 - r := by
        simp
  · have hr' : n < r := Nat.lt_of_not_ge hr
    have hempty : differencePairs n (-(r : ℤ)) = ∅ := by
      ext p
      simp [differencePairs]
      omega
    rw [hempty]
    simp
    omega

lemma card_differencePairs
    (n : ℕ) (m : ℤ) :
    (differencePairs n m).card =
      n + 1 - m.natAbs := by
  rcases Int.natAbs_eq m with hm | hm
  · calc
      (differencePairs n m).card =
          (differencePairs n (m.natAbs : ℤ)).card := by
            exact congrArg
              (fun z : ℤ => (differencePairs n z).card)
              hm
      _ = n + 1 - m.natAbs :=
        card_differencePairs_of_nonneg n m.natAbs
  · calc
      (differencePairs n m).card =
          (differencePairs n (-(m.natAbs : ℤ))).card := by
            exact congrArg
              (fun z : ℤ => (differencePairs n z).card)
              hm
      _ = n + 1 - m.natAbs :=
        card_differencePairs_of_neg n m.natAbs

lemma sub_mem_fourierIndices
    (n j k : ℕ)
    (hj : j < n + 1)
    (hk : k < n + 1) :
    (j : ℤ) - (k : ℤ) ∈ fourierIndices n := by
  rw [mem_fourierIndices]
  omega

omit [Fact (0 < T)] in
lemma sum_by_difference
    (n : ℕ) (x : AddCircle T) :
    ∑ m ∈ fourierIndices n,
        ∑ _p ∈ differencePairs n m,
          fourier m x =
      ∑ p ∈
          (Finset.range (n + 1)).product (Finset.range (n + 1)),
        fourier ((p.1 : ℤ) - (p.2 : ℤ)) x := by
  classical
  refine Finset.sum_fiberwise_of_maps_to'
    (s := (Finset.range (n + 1)).product (Finset.range (n + 1)))
    (t := fourierIndices n)
    (g := fun p : ℕ × ℕ => (p.1 : ℤ) - (p.2 : ℤ))
    ?_
    (fun m : ℤ => fourier m x)
  intro p hp
  simp at hp
  apply sub_mem_fourierIndices n p.1 p.2
  · omega
  · omega

omit [Fact (0 < T)] in
lemma sum_differencePairs
    (n : ℕ) (m : ℤ) (x : AddCircle T) :
    ∑ _p ∈ differencePairs n m, fourier m x =
      ((n + 1 - m.natAbs : ℕ) : ℂ) * fourier m x := by
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  rw [card_differencePairs]

omit [Fact (0 < T)] in
lemma double_sum_eq_weighted_sum
    (n : ℕ) (x : AddCircle T) :
    ∑ p ∈
        (Finset.range (n + 1)).product (Finset.range (n + 1)),
      fourier ((p.1 : ℤ) - (p.2 : ℤ)) x =
    ∑ m ∈ fourierIndices n,
      ((n + 1 - m.natAbs : ℕ) : ℂ) * fourier m x := by
  rw [← sum_by_difference]
  apply Finset.sum_congr rfl
  intro m hm
  rw [sum_differencePairs]

omit [Fact (0 < T)] in
lemma product_sum_eq_nested_sum
    (n : ℕ) (x : AddCircle T) :
    ∑ p ∈
        (Finset.range (n + 1)).product (Finset.range (n + 1)),
      fourier ((p.1 : ℤ) - (p.2 : ℤ)) x =
    ∑ j ∈ Finset.range (n + 1),
      ∑ k ∈ Finset.range (n + 1),
        fourier ((j : ℤ) - (k : ℤ)) x := by
  exact
    Finset.sum_product
      (s := Finset.range (n + 1))
      (t := Finset.range (n + 1))
      (f := fun p : ℕ × ℕ =>
        (fourier ((p.1 : ℤ) - (p.2 : ℤ)) x : ℂ))

omit [Fact (0 < T)] in
lemma fourierPrefix_mul_star_eq_weighted_sum
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x *
        starRingEnd ℂ (fourierPrefix (T := T) n x) =
      ∑ m ∈ fourierIndices n,
        ((n + 1 - m.natAbs : ℕ) : ℂ) *
          fourier m x := by
  calc
    fourierPrefix (T := T) n x *
        starRingEnd ℂ (fourierPrefix (T := T) n x) =
        ∑ j ∈ Finset.range (n + 1),
          ∑ k ∈ Finset.range (n + 1),
            fourier ((j : ℤ) - (k : ℤ)) x := by
      exact fourierPrefix_mul_star (T := T) n x
    _ =
        ∑ p ∈
            (Finset.range (n + 1)).product (Finset.range (n + 1)),
          fourier ((p.1 : ℤ) - (p.2 : ℤ)) x := by
      exact (product_sum_eq_nested_sum (T := T) n x).symm
    _ =
        ∑ m ∈ fourierIndices n,
          ((n + 1 - m.natAbs : ℕ) : ℂ) *
            fourier m x := by
      exact double_sum_eq_weighted_sum (T := T) n x

omit [Fact (0 < T)] in
lemma fejerKernel_eq_inv_mul_weighted_sum
    (n : ℕ) (x : AddCircle T) :
    fejerKernel (T := T) n x =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        ∑ m ∈ fourierIndices n,
          ((n + 1 - m.natAbs : ℕ) : ℂ) *
            fourier m x := by
  unfold fejerKernel
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [div_eq_mul_inv]
  ring

omit [Fact (0 < T)] in
lemma fejerKernel_eq_prefix_mul_star
    (n : ℕ) (x : AddCircle T) :
    fejerKernel (T := T) n x =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        (fourierPrefix (T := T) n x *
          starRingEnd ℂ (fourierPrefix (T := T) n x)) := by
  rw [fejerKernel_eq_inv_mul_weighted_sum]
  rw [fourierPrefix_mul_star_eq_weighted_sum]

omit [Fact (0 < T)] in
lemma fejerKernel_eq_normSq
    (n : ℕ) (x : AddCircle T) :
    fejerKernel (T := T) n x =
      (((n + 1 : ℕ) : ℂ)⁻¹) *
        (Complex.normSq (fourierPrefix (T := T) n x) : ℂ) := by
  rw [fejerKernel_eq_prefix_mul_star]
  rw [Complex.mul_conj]

omit [Fact (0 < T)] in
lemma fejerKernel_re
    (n : ℕ) (x : AddCircle T) :
    (fejerKernel (T := T) n x).re =
      (((n + 1 : ℕ) : ℝ)⁻¹) *
        Complex.normSq (fourierPrefix (T := T) n x) := by
  rw [fejerKernel_eq_normSq]
  have h :
      (((n + 1 : ℕ) : ℂ)⁻¹) =
        (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    norm_num
  rw [h]
  change
    (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ) *
        ((Complex.normSq (fourierPrefix (T := T) n x) : ℝ) : ℂ)).re =
      (((n + 1 : ℕ) : ℝ)⁻¹) *
        Complex.normSq (fourierPrefix (T := T) n x)
  rw [Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [Fact (0 < T)] in
lemma fejerKernel_im
    (n : ℕ) (x : AddCircle T) :
    (fejerKernel (T := T) n x).im = 0 := by
  rw [fejerKernel_eq_normSq]
  have h :
      (((n + 1 : ℕ) : ℂ)⁻¹) =
        (((((n + 1 : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) := by
    norm_num
  rw [h]
  simp

omit [Fact (0 < T)] in
/-- The real part of the Fejér kernel is nonnegative. -/
lemma fejerKernel_nonneg
    (n : ℕ) (x : AddCircle T) :
    0 ≤ (fejerKernel (T := T) n x).re := by
  rw [fejerKernel_re]
  have h₁ : 0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have h₂ :
      0 ≤ Complex.normSq (fourierPrefix (T := T) n x) :=
    Complex.normSq_nonneg _
  exact mul_nonneg h₁ h₂

end AddCircle

namespace AddCircle

/-!
## Normalization of the Fejér kernel

We compute the Haar integral of the Fourier modes and deduce that every Fejér
kernel has total mass one.
-/

lemma integral_fourier
    {T : ℝ} [Fact (0 < T)]
    (m : ℤ) :
    (∫ x : AddCircle T,
        fourier m x ∂AddCircle.haarAddCircle) =
      if m = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) m) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

lemma integral_fourier_zero
    {T : ℝ} [Fact (0 < T)] :
    (∫ x : AddCircle T,
        fourier (0 : ℤ) x ∂AddCircle.haarAddCircle) = 1 := by
  rw [integral_fourier]
  simp

lemma integral_fourier_ne_zero
    {T : ℝ} [Fact (0 < T)]
    (m : ℤ) (hm : m ≠ 0) :
    (∫ x : AddCircle T,
        fourier m x ∂AddCircle.haarAddCircle) = 0 := by
  rw [integral_fourier]
  simp [hm]

lemma integrable_fourier
    {T : ℝ} [Fact (0 < T)]
    (m : ℤ) :
    MeasureTheory.Integrable
      (fun x : AddCircle T => fourier m x)
      AddCircle.haarAddCircle := by
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun x : AddCircle T => fourier m x)
        AddCircle.haarAddCircle :=
    (fourier m).continuous.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

lemma integrable_weighted_fourier
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) (m : ℤ) :
    MeasureTheory.Integrable
      (fun x : AddCircle T =>
        (((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourier m x)
      AddCircle.haarAddCircle := by
  exact
    (integrable_fourier m).const_mul
      ((((n + 1 - m.natAbs : ℕ) : ℂ) /
        ((n + 1 : ℕ) : ℂ)))

/-- The Fejér kernel has normalized Haar integral equal to one. -/
lemma integral_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    (∫ x : AddCircle T,
        fejerKernel (T := T) n x
          ∂AddCircle.haarAddCircle) = 1 := by
  unfold fejerKernel
  rw [MeasureTheory.integral_finsetSum (fourierIndices n)]
  · simp_rw [MeasureTheory.integral_const_mul]
    simp_rw [integral_fourier]
    have hn :
        (((n + 1 : ℕ) : ℂ)) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    rw [Finset.sum_eq_single 0]
    · simp only [Int.natAbs_zero, Nat.sub_zero, ite_true, mul_one]
      exact div_self hn
    · intro m hm hne
      simp [hne]
    · intro hzero
      exfalso
      apply hzero
      simp [fourierIndices]
  · intro m hm
    exact integrable_weighted_fourier n m

/-!
## Concentration away from the origin

Using the geometric-sum formula, we bound the Fejér kernel uniformly on compact
sets that avoid the origin. This yields uniform decay to zero away from zero.
-/

lemma fourier_nat_eq_pow
    (k : ℕ) (x : AddCircle T) :
    fourier (k : ℤ) x =
      (fourier (1 : ℤ) x) ^ k := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.cast_succ]
      rw [fourier_add]
      rw [ih]
      rw [pow_succ]

lemma fourierPrefix_eq_geom_sum
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x =
      ∑ k ∈ Finset.range (n + 1),
        (fourier (1 : ℤ) x) ^ k := by
  unfold fourierPrefix
  apply Finset.sum_congr rfl
  intro k hk
  rw [fourier_nat_eq_pow]

lemma fourierPrefix_mul_sub_one
    (n : ℕ) (x : AddCircle T) :
    fourierPrefix (T := T) n x *
        (fourier (1 : ℤ) x - 1) =
      fourier ((n + 1 : ℕ) : ℤ) x - 1 := by
  rw [fourierPrefix_eq_geom_sum]
  rw [fourier_nat_eq_pow]
  exact geom_sum_mul (fourier (1 : ℤ) x) (n + 1)

lemma norm_fourier
    {T : ℝ}
    (m : ℤ) (x : AddCircle T) :
    ‖fourier m x‖ = 1 := by
  rw [fourier_apply]
  exact Circle.norm_coe ((m • x).toCircle)

lemma norm_fourier_sub_one_le_two
    {T : ℝ}
    (m : ℤ) (x : AddCircle T) :
    ‖fourier m x - 1‖ ≤ 2 := by
  calc
    ‖fourier m x - 1‖
        ≤ ‖fourier m x‖ + ‖(1 : ℂ)‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le (fourier m x) (-1 : ℂ)
    _ = 2 := by
      rw [norm_fourier]
      norm_num

lemma norm_fourierPrefix_mul_norm_sub_one_le_two
    {T : ℝ}
    (n : ℕ) (x : AddCircle T) :
    ‖fourierPrefix (T := T) n x‖ *
        ‖fourier (1 : ℤ) x - 1‖ ≤ 2 := by
  have h :=
    congrArg norm
      (fourierPrefix_mul_sub_one (T := T) n x)
  rw [norm_mul] at h
  rw [h]
  exact norm_fourier_sub_one_le_two
    ((n + 1 : ℕ) : ℤ) x

lemma norm_fourierPrefix_le
    {T : ℝ}
    (n : ℕ) (x : AddCircle T)
    (hx : fourier (1 : ℤ) x ≠ 1) :
    ‖fourierPrefix (T := T) n x‖ ≤
      2 / ‖fourier (1 : ℤ) x - 1‖ := by
  have hpos :
      0 < ‖fourier (1 : ℤ) x - 1‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hx
  have h :=
    norm_fourierPrefix_mul_norm_sub_one_le_two
      (T := T) n x
  exact (le_div_iff₀ hpos).2 h

lemma normSq_fourierPrefix_le
    {T : ℝ}
    (n : ℕ) (x : AddCircle T)
    (hx : fourier (1 : ℤ) x ≠ 1) :
    Complex.normSq (fourierPrefix (T := T) n x) ≤
      4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2 := by
  have h :=
    norm_fourierPrefix_le (T := T) n x hx
  have hnonneg :
      0 ≤ ‖fourierPrefix (T := T) n x‖ := norm_nonneg _
  have hden :
      0 ≤ 2 / ‖fourier (1 : ℤ) x - 1‖ := by
    positivity
  have hsq :
      ‖fourierPrefix (T := T) n x‖ ^ 2 ≤
        (2 / ‖fourier (1 : ℤ) x - 1‖) ^ 2 := by
    exact pow_le_pow_left₀ hnonneg h 2
  rw [Complex.sq_norm] at hsq
  calc
    Complex.normSq (fourierPrefix (T := T) n x)
        ≤ (2 / ‖fourier (1 : ℤ) x - 1‖) ^ 2 := hsq
    _ = 4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2 := by
      ring

lemma fejerKernel_re_le
    {T : ℝ}
    (n : ℕ) (x : AddCircle T)
    (hx : fourier (1 : ℤ) x ≠ 1) :
    (fejerKernel (T := T) n x).re ≤
      4 /
        (((n + 1 : ℕ) : ℝ) *
          ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
  rw [fejerKernel_re]
  have hsq :=
    normSq_fourierPrefix_le (T := T) n x hx
  have hn :
      0 ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have hmul :
      (((n + 1 : ℕ) : ℝ)⁻¹) *
          Complex.normSq (fourierPrefix (T := T) n x)
        ≤
      (((n + 1 : ℕ) : ℝ)⁻¹) *
          (4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsq hn
  calc
    (((n + 1 : ℕ) : ℝ)⁻¹) *
        Complex.normSq (fourierPrefix (T := T) n x)
      ≤
        (((n + 1 : ℕ) : ℝ)⁻¹) *
          (4 / ‖fourier (1 : ℤ) x - 1‖ ^ 2) := hmul
    _ =
        4 /
          (((n + 1 : ℕ) : ℝ) *
            ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
      field_simp

lemma continuous_norm_fourier_one_sub_one
    {T : ℝ} :
    Continuous
      (fun x : AddCircle T =>
        ‖fourier (1 : ℤ) x - 1‖) := by
  fun_prop

lemma exists_pos_lower_bound_norm_fourier_one_sub_one
    {T : ℝ} [Fact (0 < T)]
    (K : Set (AddCircle T))
    (hK : IsCompact K)
    (h0 : (0 : AddCircle T) ∉ K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ K,
        c ≤ ‖fourier (1 : ℤ) x - 1‖ := by
  by_cases hKne : K.Nonempty
  · have hcont :
        ContinuousOn
          (fun x : AddCircle T =>
            ‖fourier (1 : ℤ) x - 1‖) K :=
      continuous_norm_fourier_one_sub_one.continuousOn
    obtain ⟨x₀, hx₀min⟩ :=
      hK.exists_isMinOn hKne hcont
    have hx₀K : x₀ ∈ K := by
      exact hx₀min.1
    refine ⟨‖fourier (1 : ℤ) x₀ - 1‖, ?_, ?_⟩
    · rw [norm_pos_iff]
      apply sub_ne_zero.mpr
      intro hfourier
      have hcircle :
          x₀.toCircle = (1 : Circle) := by
        apply Subtype.ext
        simpa [fourier_one] using hfourier
      have hT : T ≠ 0 := by
        exact ne_of_gt (Fact.out : 0 < T)
      have hx₀ : x₀ = 0 := by
        apply AddCircle.injective_toCircle hT
        simpa using hcircle
      exact h0 (hx₀ ▸ hx₀K)
    · intro x hxK
      exact hx₀min.2 hxK
  · refine ⟨1, by positivity, ?_⟩
    intro x hxK
    exfalso
    exact hKne ⟨x, hxK⟩

lemma fejerKernel_re_le_on_compact
    {T : ℝ} [Fact (0 < T)]
    (K : Set (AddCircle T))
    (hK : IsCompact K)
    (h0 : (0 : AddCircle T) ∉ K) :
    ∃ c : ℝ, 0 < c ∧
      ∀ n : ℕ, ∀ x ∈ K,
        (fejerKernel (T := T) n x).re ≤
          4 / ((((n + 1 : ℕ) : ℝ) * c ^ 2)) := by
  obtain ⟨c, hcpos, hc⟩ :=
    exists_pos_lower_bound_norm_fourier_one_sub_one
      (T := T) K hK h0
  refine ⟨c, hcpos, ?_⟩
  intro n x hxK
  have hc_le :
      c ≤ ‖fourier (1 : ℤ) x - 1‖ :=
    hc x hxK
  have hc_nonneg : 0 ≤ c := le_of_lt hcpos
  have hnorm_pos :
      0 < ‖fourier (1 : ℤ) x - 1‖ := by
    exact lt_of_lt_of_le hcpos hc_le
  have hx :
      fourier (1 : ℤ) x ≠ 1 := by
    intro h
    have :
        ‖fourier (1 : ℤ) x - 1‖ = 0 := by
      rw [h]
      simp
    linarith
  have hkernel :=
    fejerKernel_re_le (T := T) n x hx
  have hsq :
      c ^ 2 ≤ ‖fourier (1 : ℤ) x - 1‖ ^ 2 := by
    nlinarith [hc_le, hc_nonneg, norm_nonneg (fourier (1 : ℤ) x - 1)]
  have hnpos :
      0 < (((n + 1 : ℕ) : ℝ)) := by
    positivity
  have hden :
      (((n + 1 : ℕ) : ℝ) * c ^ 2) ≤
        (((n + 1 : ℕ) : ℝ) *
          ‖fourier (1 : ℤ) x - 1‖ ^ 2) := by
    exact mul_le_mul_of_nonneg_left hsq (le_of_lt hnpos)
  have hdenpos :
      0 < (((n + 1 : ℕ) : ℝ) * c ^ 2) := by
    positivity
  have hfrac :
      4 /
          (((n + 1 : ℕ) : ℝ) *
            ‖fourier (1 : ℤ) x - 1‖ ^ 2)
        ≤
      4 /
          (((n + 1 : ℕ) : ℝ) * c ^ 2) := by
    apply div_le_div_of_nonneg_left
    · norm_num
    · exact hdenpos
    · exact hden
  exact le_trans hkernel hfrac

/-- On every compact set avoiding the origin, the real parts of the Fejér
    kernels converge uniformly to zero. -/
lemma fejerKernel_tendsto_zero_uniformly_on_compact
    {T : ℝ} [Fact (0 < T)]
    (K : Set (AddCircle T))
    (hK : IsCompact K)
    (h0 : (0 : AddCircle T) ∉ K) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n →
          ∀ x ∈ K,
            (fejerKernel (T := T) n x).re < ε := by
  intro ε hε
  obtain ⟨c, hcpos, hbound⟩ :=
    fejerKernel_re_le_on_compact
      (T := T) K hK h0
  have hc2pos : 0 < c ^ 2 := by
    positivity
  have hεc2pos : 0 < ε * c ^ 2 := by
    positivity
  obtain ⟨N, hN⟩ :=
    exists_nat_gt (4 / (ε * c ^ 2))
  refine ⟨N, ?_⟩
  intro n hn x hxK
  have hkernel :
      (fejerKernel (T := T) n x).re ≤
        4 / ((((n + 1 : ℕ) : ℝ) * c ^ 2)) :=
    hbound n x hxK
  have hNcast :
      4 / (ε * c ^ 2) < (N : ℝ) := by
    exact hN
  have hncast :
      (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnlarge :
      4 / (ε * c ^ 2) < (n : ℝ) := by
    exact lt_of_lt_of_le hNcast hncast
  have hnlarge' :
      4 / (ε * c ^ 2) <
        ((n + 1 : ℕ) : ℝ) := by
    norm_num at *
    linarith
  have hfour :
      4 <
        ((n + 1 : ℕ) : ℝ) * (ε * c ^ 2) := by
    exact (div_lt_iff₀ hεc2pos).mp hnlarge'
  have hdenpos :
      0 < (((n + 1 : ℕ) : ℝ) * c ^ 2) := by
    positivity
  have hfrac :
      4 / ((((n + 1 : ℕ) : ℝ) * c ^ 2)) < ε := by
    apply (div_lt_iff₀ hdenpos).2
    nlinarith
  exact lt_of_le_of_lt hkernel hfrac

/-!
## Convolution representation of the Fejér means

We relate translation of Fourier modes to Haar integration and derive the
representation of a Fejér mean as convolution with the Fejér kernel.
-/

lemma fourier_apply_add
    {T : ℝ}
    (m : ℤ)
    (x y : AddCircle T) :
    fourier m (x + y) =
      fourier m x * fourier m y := by
  simp [fourier_apply, AddCircle.toCircle_add]

lemma fourier_apply_sub
    {T : ℝ}
    (m : ℤ)
    (x y : AddCircle T) :
    fourier m (x - y) =
      fourier m x * fourier (-m) y := by
  rw [sub_eq_add_neg]
  rw [fourier_apply_add]
  congr 1
  rw [fourier_apply]
  rw [fourier_apply]
  simp

lemma integral_neg_haarAddCircle
    {T : ℝ} [Fact (0 < T)]
    (g : AddCircle T → ℂ) :
    (∫ y : AddCircle T,
        g (-y) ∂AddCircle.haarAddCircle) =
      ∫ y : AddCircle T,
        g y ∂AddCircle.haarAddCircle := by
  exact
    MeasureTheory.integral_neg_eq_self
      g
      AddCircle.haarAddCircle

lemma integral_fourier_mul_translate
    {T : ℝ} [Fact (0 < T)]
    (f : AddCircle T → ℂ)
    (m : ℤ)
    (x : AddCircle T) :
    (∫ y : AddCircle T,
        fourier m y * f (x - y)
          ∂AddCircle.haarAddCircle) =
      fourier m x * fourierCoeff f m := by
  have hshift :=
    MeasureTheory.integral_add_right_eq_self
      (μ := AddCircle.haarAddCircle)
      (fun y : AddCircle T =>
        fourier m y * f (x - y))
      x
  calc
    (∫ y : AddCircle T,
        fourier m y * f (x - y)
          ∂AddCircle.haarAddCircle)
        =
      ∫ y : AddCircle T,
        fourier m (y + x) * f (x - (y + x))
          ∂AddCircle.haarAddCircle := hshift.symm
    _ =
      ∫ y : AddCircle T,
        fourier m x * (fourier m y * f (-y))
          ∂AddCircle.haarAddCircle := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      rw [fourier_apply_add]
      have hsub :
          x - (y + x) = -y := by
        abel
      rw [hsub]
      ring
    _ =
      fourier m x *
        (∫ y : AddCircle T,
          fourier m y * f (-y)
            ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_const_mul]
    _ =
      fourier m x *
        (∫ y : AddCircle T,
          fourier (-m) y * f y
            ∂AddCircle.haarAddCircle) := by
      congr 1
      have hneg :=
        integral_neg_haarAddCircle
          (T := T)
          (fun y : AddCircle T =>
            fourier (-m) y * f y)
      simpa [fourier_neg, mul_comm, mul_left_comm, mul_assoc]
        using hneg
    _ =
      fourier m x * fourierCoeff f m := by
      simp [fourierCoeff, smul_eq_mul]

lemma integrable_weighted_fourier_mul_translate
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (m : ℤ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourier m y) *
          f (x - y))
      AddCircle.haarAddCircle := by
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          ((((n + 1 - m.natAbs : ℕ) : ℂ) /
            ((n + 1 : ℕ) : ℂ)) *
            fourier m y) *
            f (x - y)) := by
    fun_prop
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          ((((n + 1 - m.natAbs : ℕ) : ℂ) /
            ((n + 1 : ℕ) : ℂ)) *
            fourier m y) *
            f (x - y))
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

lemma integral_fejerKernel_mul_translate_eq_sum
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          (fourier m x * fourierCoeff f m)) := by
  unfold fejerKernel
  simp_rw [Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum (fourierIndices n)]
  · apply Finset.sum_congr rfl
    intro m hm
    simp_rw [mul_assoc]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_fourier_mul_translate]
  · intro m hm
    exact
      integrable_weighted_fourier_mul_translate
        (T := T) f n m x

lemma integral_fejerKernel_mul_translate_eq_weighted_fourier
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x) := by
  rw [integral_fejerKernel_mul_translate_eq_sum
    (T := T) f n x]
  apply Finset.sum_congr rfl
  intro m hm
  ring

lemma fourierPartialSum_eq_sum_indicator
    {T : ℝ} [Fact (0 < T)]
    (f : AddCircle T → ℂ)
    (n j : ℕ)
    (hj : j ≤ n)
    (x : AddCircle T) :
    fourierPartialSum (T := T) f j x =
      ∑ m ∈ fourierIndices n,
        if m ∈ fourierIndices j then
          fourierCoeff f m * fourier m x
        else 0 := by
  unfold fourierPartialSum
  rw [← Finset.sum_filter]
  have hfilter :
      (fourierIndices n).filter
          (fun m => m ∈ fourierIndices j) =
        fourierIndices j := by
    ext m
    simp only [Finset.mem_filter]
    constructor
    · intro hm
      exact hm.2
    · intro hm
      constructor
      · rw [mem_fourierIndices] at hm ⊢
        omega
      · exact hm
  rw [hfilter]

lemma fejerMean_eq_weighted_fourier_sum
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMean (T := T) f n x =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x) := by
  unfold fejerMean
  calc
    (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ j ∈ Finset.range (n + 1),
          fourierPartialSum (T := T) f j x)
        =
      (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ j ∈ Finset.range (n + 1),
          ∑ m ∈ fourierIndices n,
            if m ∈ fourierIndices j then
              fourierCoeff f m * fourier m x
            else 0) := by
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      apply fourierPartialSum_eq_sum_indicator
        (T := T) f n j
      simp at hj
      omega
    _ =
      (((n + 1 : ℕ) : ℂ)⁻¹ *
        ∑ m ∈ fourierIndices n,
          ∑ j ∈ Finset.range (n + 1),
            if m ∈ fourierIndices j then
              fourierCoeff f m * fourier m x
            else 0) := by
      congr 1
      rw [Finset.sum_comm]
    _ =
      ∑ m ∈ fourierIndices n,
        (((n + 1 : ℕ) : ℂ)⁻¹ *
          ∑ j ∈ Finset.range (n + 1),
            if m ∈ fourierIndices j then
              fourierCoeff f m * fourier m x
            else 0) := by
      rw [Finset.mul_sum]
    _ =
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [sum_indicator
        n m (fourierCoeff f m * fourier m x)]
      rw [div_eq_mul_inv]
      ring

/-- A Fejér mean is the convolution of `f` with the Fejér kernel with respect
    to normalized Haar measure. -/
lemma fejerMean_eq_integral_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMean (T := T) f n x =
      ∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle := by
  rw [fejerMean_eq_weighted_fourier_sum]
  rw [integral_fejerKernel_mul_translate_eq_weighted_fourier]

/-!
## Error representation and local/far estimates

We rewrite the approximation error as an integral against the Fejér kernel,
then split that integral into a neighborhood of the origin and its complement.
The near part is controlled by uniform continuity, while the far part is
controlled by concentration of the kernel.
-/

lemma continuous_fejerKernel
    {T : ℝ}
    (n : ℕ) :
    Continuous
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y) := by
  unfold fejerKernel
  fun_prop

lemma integrable_fejerKernel_mul_translate
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y *
          f (x - y))
      AddCircle.haarAddCircle := by
  have htrans :
      Continuous
        (fun y : AddCircle T =>
          x - y) := by
    fun_prop
  have hftrans :
      Continuous
        (fun y : AddCircle T =>
          f (x - y)) := by
    exact f.continuous.comp htrans
  have hkernel :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y) :=
    continuous_fejerKernel (T := T) n
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            f (x - y)) :=
    hkernel.mul hftrans
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            f (x - y))
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

lemma integrable_fejerKernel_mul_const
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y * f x)
      AddCircle.haarAddCircle := by
  have hkernel :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y) :=
    continuous_fejerKernel (T := T) n
  have hconst :
      Continuous
        (fun _y : AddCircle T =>
          f x) := by
    fun_prop
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y * f x) :=
    hkernel.mul hconst
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y * f x)
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

/-- The error of a Fejér mean is the integral of the Fejér kernel against the
    translated difference `f (x - y) - f x`. -/
lemma fejerMean_sub_eq_integral
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMean (T := T) f n x - f x =
      ∫ y : AddCircle T,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle := by
  rw [fejerMean_eq_integral_fejerKernel]
  have hnorm :
      (∫ y : AddCircle T,
          fejerKernel (T := T) n y
            ∂AddCircle.haarAddCircle) = 1 :=
    integral_fejerKernel (T := T) n
  calc
    (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) - f x
        =
      (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f (x - y)
          ∂AddCircle.haarAddCircle) -
      (∫ y : AddCircle T,
        fejerKernel (T := T) n y * f x
          ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_mul_const]
      rw [hnorm]
      simp
    _ =
      ∫ y : AddCircle T,
        (fejerKernel (T := T) n y * f (x - y) -
          fejerKernel (T := T) n y * f x)
          ∂AddCircle.haarAddCircle := by
      rw [← MeasureTheory.integral_sub]
      · exact
          integrable_fejerKernel_mul_translate
            (T := T) f n x
      · exact
          integrable_fejerKernel_mul_const
            (T := T) f n x
    _ =
      ∫ y : AddCircle T,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with y
      ring

lemma exists_neighborhood_uniform_diff_lt
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ U : Set (AddCircle T),
      IsOpen U ∧
      (0 : AddCircle T) ∈ U ∧
      ∀ x : AddCircle T, ∀ y ∈ U,
        ‖f (x - y) - f x‖ < ε := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    f.uniform_continuity ε hε
  refine ⟨Metric.ball 0 δ, Metric.isOpen_ball, ?_, ?_⟩
  · simp [hδpos]
  · intro x y hy
    have hyδ :
        dist y 0 < δ := by
      simpa [Metric.mem_ball] using hy
    have hdist :
        dist (x - y) x < δ := by
      simpa [dist_eq_norm, sub_eq_add_neg,
        add_comm, add_left_comm, add_assoc] using hyδ
    have hf :
        dist (f (x - y)) (f x) < ε :=
      hδ hdist
    simpa [Complex.dist_eq] using hf

lemma fejerKernel_tendsto_zero_uniformly_outside_neighborhood
    {T : ℝ} [Fact (0 < T)]
    (U : Set (AddCircle T))
    (hU : IsOpen U)
    (h0 : (0 : AddCircle T) ∈ U) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ,
        ∀ n : ℕ, N ≤ n →
          ∀ x : AddCircle T, x ∉ U →
            (fejerKernel (T := T) n x).re < ε := by
  have hK :
      IsCompact (Uᶜ : Set (AddCircle T)) :=
    hU.isClosed_compl.isCompact
  have h0K :
      (0 : AddCircle T) ∉ Uᶜ := by
    simpa using h0
  intro ε hε
  obtain ⟨N, hN⟩ :=
    fejerKernel_tendsto_zero_uniformly_on_compact
      (T := T) Uᶜ hK h0K ε hε
  refine ⟨N, ?_⟩
  intro n hn x hx
  apply hN n hn x
  simpa using hx

lemma norm_sub_translate_le_two_norm
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (x y : AddCircle T) :
    ‖f (x - y) - f x‖ ≤ 2 * ‖f‖ := by
  calc
    ‖f (x - y) - f x‖
        ≤ ‖f (x - y)‖ + ‖f x‖ := by
          simpa [sub_eq_add_neg] using
            norm_add_le (f (x - y)) (-f x)
    _ ≤ ‖f‖ + ‖f‖ := by
      gcongr
      · exact ContinuousMap.norm_coe_le_norm f (x - y)
      · exact ContinuousMap.norm_coe_le_norm f x
    _ = 2 * ‖f‖ := by
      ring

lemma norm_fejerKernel_mul_diff_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x y : AddCircle T) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    2 * ‖f‖ * (fejerKernel (T := T) n y).re := by
  rw [norm_mul]
  have hkernel_nonneg :=
    fejerKernel_nonneg (T := T) n y
  have him :=
    fejerKernel_im (T := T) n y
  have hkernel_eq_real :
      fejerKernel (T := T) n y =
        ((fejerKernel (T := T) n y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  have hkernel_norm :
      ‖fejerKernel (T := T) n y‖ =
        (fejerKernel (T := T) n y).re := by
    rw [hkernel_eq_real]
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hkernel_nonneg
  rw [hkernel_norm]
  have hdiff :=
    norm_sub_translate_le_two_norm
      (T := T) f x y
  nlinarith

lemma norm_fejerKernel_mul_diff_le_of_diff_le
    {T : ℝ}
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x y : AddCircle T)
    (ε : ℝ)
    (hdiff : ‖f (x - y) - f x‖ ≤ ε) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    ε * (fejerKernel (T := T) n y).re := by
  rw [norm_mul]
  have hkernel_nonneg :=
    fejerKernel_nonneg (T := T) n y
  have him :=
    fejerKernel_im (T := T) n y
  have hkernel_eq_real :
      fejerKernel (T := T) n y =
        ((fejerKernel (T := T) n y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  have hkernel_norm :
      ‖fejerKernel (T := T) n y‖ =
        (fejerKernel (T := T) n y).re := by
    rw [hkernel_eq_real]
    rw [Complex.norm_real]
    exact Real.norm_of_nonneg hkernel_nonneg
  rw [hkernel_norm]
  have hmul :=
    mul_le_mul_of_nonneg_left hdiff hkernel_nonneg
  simpa [mul_comm] using hmul

lemma norm_fejerKernel_mul_diff_le_on_neighborhood
    {T : ℝ}
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T)
    (U : Set (AddCircle T))
    (ε : ℝ)
    (hU :
      ∀ x : AddCircle T, ∀ y ∈ U,
        ‖f (x - y) - f x‖ < ε)
    (y : AddCircle T)
    (hy : y ∈ U) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    ε * (fejerKernel (T := T) n y).re := by
  apply norm_fejerKernel_mul_diff_le_of_diff_le
    (T := T) f n x y ε
  exact le_of_lt (hU x y hy)

lemma integrable_fejerKernel_mul_diff
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y *
          (f (x - y) - f x))
      AddCircle.haarAddCircle := by
  have hkernel :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y) :=
    continuous_fejerKernel (T := T) n
  have htrans :
      Continuous
        (fun y : AddCircle T =>
          x - y) := by
    fun_prop
  have hftrans :
      Continuous
        (fun y : AddCircle T =>
          f (x - y)) := by
    exact f.continuous.comp htrans
  have hdiff :
      Continuous
        (fun y : AddCircle T =>
          f (x - y) - f x) := by
    exact hftrans.sub continuous_const
  have hcont :
      Continuous
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            (f (x - y) - f x)) :=
    hkernel.mul hdiff
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y *
            (f (x - y) - f x))
        AddCircle.haarAddCircle :=
    hcont.locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

lemma fejerMean_sub_eq_integral_add_compl
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T)
    (U : Set (AddCircle T))
    (hU : IsOpen U) :
    fejerMean (T := T) f n x - f x =
      (∫ y : AddCircle T in U,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle) +
      (∫ y : AddCircle T in Uᶜ,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle) := by
  rw [fejerMean_sub_eq_integral]
  symm
  exact
    MeasureTheory.integral_add_compl
      hU.measurableSet
      (integrable_fejerKernel_mul_diff
        (T := T) f n x)

lemma integrable_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    MeasureTheory.Integrable
      (fun y : AddCircle T =>
        fejerKernel (T := T) n y)
      AddCircle.haarAddCircle := by
  have hloc :
      MeasureTheory.LocallyIntegrable
        (fun y : AddCircle T =>
          fejerKernel (T := T) n y)
        AddCircle.haarAddCircle :=
    (continuous_fejerKernel (T := T) n).locallyIntegrable
  rw [← MeasureTheory.integrableOn_univ]
  exact hloc.integrableOn_isCompact isCompact_univ

lemma integral_fejerKernel_re
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    (∫ y : AddCircle T,
        (fejerKernel (T := T) n y).re
          ∂AddCircle.haarAddCircle) = 1 := by
  have h :=
    integral_re
      (integrable_fejerKernel (T := T) n)
  rw [integral_fejerKernel (T := T) n] at h
  simpa using h

lemma norm_fejerKernel_eq_re
    {T : ℝ}
    (n : ℕ)
    (y : AddCircle T) :
    ‖fejerKernel (T := T) n y‖ =
      (fejerKernel (T := T) n y).re := by
  have hnonneg :=
    fejerKernel_nonneg (T := T) n y
  have him :=
    fejerKernel_im (T := T) n y
  have heq :
      fejerKernel (T := T) n y =
        ((fejerKernel (T := T) n y).re : ℂ) := by
    apply Complex.ext
    · simp
    · simp [him]
  rw [heq]
  rw [Complex.norm_real]
  exact Real.norm_of_nonneg hnonneg

lemma integral_norm_fejerKernel
    {T : ℝ} [Fact (0 < T)]
    (n : ℕ) :
    (∫ y : AddCircle T,
        ‖fejerKernel (T := T) n y‖
          ∂AddCircle.haarAddCircle) = 1 := by
  simp_rw [norm_fejerKernel_eq_re (T := T) n]
  exact integral_fejerKernel_re (T := T) n

lemma norm_integral_fejerKernel_mul_diff_on_neighborhood_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T)
    (U : Set (AddCircle T))
    (hUmeas : MeasurableSet U)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hU :
      ∀ x : AddCircle T, ∀ y ∈ U,
        ‖f (x - y) - f x‖ < ε) :
    ‖∫ y : AddCircle T in U,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle‖
      ≤ ε := by
  let μU :=
    AddCircle.haarAddCircle.restrict U
  have hnorm_int :
      ‖∫ y : AddCircle T,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂μU‖
        ≤
      ∫ y : AddCircle T,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
        ∂μU := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hleft_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖)
        μU := by
    exact
      (integrable_fejerKernel_mul_diff
        (T := T) f n x).norm.restrict
  have hre_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          (fejerKernel (T := T) n y).re)
        AddCircle.haarAddCircle := by
    exact
      (integrable_fejerKernel (T := T) n).re
  have hright_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          ε * (fejerKernel (T := T) n y).re)
        μU := by
    exact
      (hre_int.const_mul ε).restrict
  have hpoint :
      ∀ᵐ y : AddCircle T ∂μU,
        ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ≤
        ε * (fejerKernel (T := T) n y).re := by
    apply MeasureTheory.ae_restrict_of_forall_mem hUmeas
    intro y hy
    exact
      norm_fejerKernel_mul_diff_le_on_neighborhood
        (T := T) f n x U ε hU y hy
  have hmono :
      (∫ y : AddCircle T,
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ∂μU)
        ≤
      ∫ y : AddCircle T,
        ε * (fejerKernel (T := T) n y).re
        ∂μU := by
    exact
      MeasureTheory.integral_mono_ae
        hleft_int
        hright_int
        hpoint
  have hrestrict :
      (∫ y : AddCircle T in U,
          (fejerKernel (T := T) n y).re
          ∂AddCircle.haarAddCircle)
        ≤ 1 := by
    have hμ :
        AddCircle.haarAddCircle.restrict U
          ≤ AddCircle.haarAddCircle := by
      exact MeasureTheory.Measure.restrict_le_self
    have hnonneg :
        0 ≤ᵐ[AddCircle.haarAddCircle]
          fun y : AddCircle T =>
            (fejerKernel (T := T) n y).re := by
      filter_upwards with y
      exact fejerKernel_nonneg (T := T) n y
    have hmeasure :=
      MeasureTheory.integral_mono_measure
        hμ
        hnonneg
        hre_int
    rw [integral_fejerKernel_re (T := T) n] at hmeasure
    exact hmeasure
  calc
    ‖∫ y : AddCircle T in U,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle‖
        ≤
      ∫ y : AddCircle T in U,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
          ∂AddCircle.haarAddCircle := hnorm_int
    _ ≤
      ∫ y : AddCircle T in U,
        ε * (fejerKernel (T := T) n y).re
          ∂AddCircle.haarAddCircle := hmono
    _ =
      ε *
        (∫ y : AddCircle T in U,
          (fejerKernel (T := T) n y).re
            ∂AddCircle.haarAddCircle) := by
      rw [MeasureTheory.integral_const_mul]
    _ ≤ ε * 1 := by
      exact mul_le_mul_of_nonneg_left hrestrict hε
    _ = ε := by
      ring

lemma norm_fejerKernel_mul_diff_le_of_re_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x y : AddCircle T)
    (δ : ℝ)
    (hkernel :
      (fejerKernel (T := T) n y).re ≤ δ) :
    ‖fejerKernel (T := T) n y *
        (f (x - y) - f x)‖
      ≤
    2 * ‖f‖ * δ := by
  have h :=
    norm_fejerKernel_mul_diff_le
      (T := T) f n x y
  have hcoef :
      0 ≤ 2 * ‖f‖ := by
    positivity
  exact
    le_trans h
      (mul_le_mul_of_nonneg_left hkernel hcoef)

lemma norm_fejerKernel_mul_diff_le_outside_neighborhood
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (U : Set (AddCircle T))
    (hU : IsOpen U)
    (h0 : (0 : AddCircle T) ∈ U)
    (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ x : AddCircle T,
          ∀ y : AddCircle T, y ∉ U →
            ‖fejerKernel (T := T) n y *
                (f (x - y) - f x)‖
              ≤
            2 * ‖f‖ * δ := by
  obtain ⟨N, hN⟩ :=
    fejerKernel_tendsto_zero_uniformly_outside_neighborhood
      (T := T) U hU h0 δ hδ
  refine ⟨N, ?_⟩
  intro n hn x y hy
  apply norm_fejerKernel_mul_diff_le_of_re_le
    (T := T) f n x y δ
  exact le_of_lt (hN n hn y hy)

lemma norm_integral_fejerKernel_mul_diff_outside_neighborhood_le
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (U : Set (AddCircle T))
    (hU : IsOpen U)
    (h0 : (0 : AddCircle T) ∈ U)
    (δ : ℝ)
    (hδ : 0 < δ) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ x : AddCircle T,
          ‖∫ y : AddCircle T in Uᶜ,
              fejerKernel (T := T) n y *
                (f (x - y) - f x)
                ∂AddCircle.haarAddCircle‖
            ≤
          2 * ‖f‖ * δ := by
  obtain ⟨N, hN⟩ :=
    norm_fejerKernel_mul_diff_le_outside_neighborhood
      (T := T) f U hU h0 δ hδ
  refine ⟨N, ?_⟩
  intro n hn x
  let μC :=
    AddCircle.haarAddCircle.restrict Uᶜ
  let C : ℝ :=
    2 * ‖f‖ * δ
  have hCnonneg :
      0 ≤ C := by
    dsimp [C]
    positivity
  have hnorm_int :
      ‖∫ y : AddCircle T,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂μC‖
        ≤
      ∫ y : AddCircle T,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
        ∂μC := by
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hleft_int :
      MeasureTheory.Integrable
        (fun y : AddCircle T =>
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖)
        μC := by
    exact
      (integrable_fejerKernel_mul_diff
        (T := T) f n x).norm.restrict
  have hconst_int :
      MeasureTheory.Integrable
        (fun _y : AddCircle T => C)
        AddCircle.haarAddCircle := by
    exact integrable_const C
  have hright_int :
      MeasureTheory.Integrable
        (fun _y : AddCircle T => C)
        μC := by
    exact hconst_int.restrict
  have hpoint :
      ∀ᵐ y : AddCircle T ∂μC,
        ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ≤ C := by
    apply MeasureTheory.ae_restrict_of_forall_mem
      hU.measurableSet.compl
    intro y hy
    have hyU : y ∉ U := by
      simpa using hy
    dsimp [C]
    exact hN n hn x y hyU
  have hmono :
      (∫ y : AddCircle T,
          ‖fejerKernel (T := T) n y *
            (f (x - y) - f x)‖
          ∂μC)
        ≤
      ∫ _y : AddCircle T,
        C
        ∂μC := by
    exact
      MeasureTheory.integral_mono_ae
        hleft_int
        hright_int
        hpoint
  have hrestrict :
      (∫ _y : AddCircle T in Uᶜ,
          C
          ∂AddCircle.haarAddCircle)
        ≤ C := by
    have hμ :
        AddCircle.haarAddCircle.restrict Uᶜ
          ≤ AddCircle.haarAddCircle := by
      exact MeasureTheory.Measure.restrict_le_self
    have hnonneg :
        ∀ᵐ _y : AddCircle T ∂AddCircle.haarAddCircle,
          0 ≤ C := by
      exact Filter.Eventually.of_forall (fun _ => hCnonneg)
    have hmeasure :=
      MeasureTheory.integral_mono_measure
        hμ
        hnonneg
        hconst_int
    have hfull :
        (∫ _y : AddCircle T,
            C
            ∂AddCircle.haarAddCircle) = C := by
      simp
    rw [hfull] at hmeasure
    exact hmeasure
  calc
    ‖∫ y : AddCircle T in Uᶜ,
        fejerKernel (T := T) n y *
          (f (x - y) - f x)
          ∂AddCircle.haarAddCircle‖
        ≤
      ∫ y : AddCircle T in Uᶜ,
        ‖fejerKernel (T := T) n y *
          (f (x - y) - f x)‖
          ∂AddCircle.haarAddCircle := hnorm_int
    _ ≤
      ∫ _y : AddCircle T in Uᶜ,
        C
        ∂AddCircle.haarAddCircle := hmono
    _ ≤ C := hrestrict
    _ = 2 * ‖f‖ * δ := by
      rfl

/-!
## Fejér's theorem

The following results establish uniform convergence of the Fejér means of a
continuous complex-valued function on `AddCircle T`.

We first prove an explicit uniform ε-N estimate, then package this result as
convergence in the sup norm on continuous maps and as `TendstoUniformly`.
-/

/-- Fejér's theorem in explicit uniform `ε`-`N` form: the Fejér means of a
    continuous function converge uniformly to the function. -/
lemma fejerMean_uniform_error_lt
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ∀ x : AddCircle T,
          ‖fejerMean (T := T) f n x - f x‖ < ε := by
  have hε4 :
      0 < ε / 4 := by
    positivity
  obtain ⟨U, hUopen, h0U, hUdiff⟩ :=
    exists_neighborhood_uniform_diff_lt
      (T := T) f (ε / 4) hε4
  let δ : ℝ :=
    ε / (8 * (‖f‖ + 1))
  have hnorm_nonneg :
      0 ≤ ‖f‖ := norm_nonneg f
  have hnorm_one_pos :
      0 < ‖f‖ + 1 := by
    linarith
  have hδ :
      0 < δ := by
    dsimp [δ]
    positivity
  obtain ⟨N, hNfar⟩ :=
    norm_integral_fejerKernel_mul_diff_outside_neighborhood_le
      (T := T) f U hUopen h0U δ hδ
  refine ⟨N, ?_⟩
  intro n hn x
  have hnear :
      ‖∫ y : AddCircle T in U,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖
        ≤ ε / 4 := by
    exact
      norm_integral_fejerKernel_mul_diff_on_neighborhood_le
        (T := T)
        f n x U hUopen.measurableSet
        (ε / 4)
        (le_of_lt hε4)
        hUdiff
  have hfar :
      ‖∫ y : AddCircle T in Uᶜ,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖
        ≤ 2 * ‖f‖ * δ := by
    exact hNfar n hn x
  have hfar_small :
      2 * ‖f‖ * δ ≤ ε / 4 := by
    dsimp [δ]
    have hratio :
        ‖f‖ / (‖f‖ + 1) ≤ 1 := by
      apply (div_le_one hnorm_one_pos).2
      linarith
    calc
      2 * ‖f‖ * (ε / (8 * (‖f‖ + 1))) =
          (ε / 4) * (‖f‖ / (‖f‖ + 1)) := by
        field_simp [ne_of_gt hnorm_one_pos]
        ring
      _ ≤ (ε / 4) * 1 := by
        exact
          mul_le_mul_of_nonneg_left
            hratio
            (le_of_lt hε4)
      _ = ε / 4 := by
        ring
  have hsplit :=
    fejerMean_sub_eq_integral_add_compl
      (T := T) f n x U hUopen
  rw [hsplit]
  calc
    ‖(∫ y : AddCircle T in U,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle) +
      (∫ y : AddCircle T in Uᶜ,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle)‖
        ≤
      ‖∫ y : AddCircle T in U,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖ +
      ‖∫ y : AddCircle T in Uᶜ,
          fejerKernel (T := T) n y *
            (f (x - y) - f x)
            ∂AddCircle.haarAddCircle‖ := by
      exact norm_add_le _ _
    _ ≤ ε / 4 + ε / 4 := by
      exact add_le_add hnear (le_trans hfar hfar_small)
    _ < ε := by
      linarith

lemma continuous_fejerMean
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ) :
    Continuous
      (fun x : AddCircle T =>
        fejerMean (T := T) f n x) := by
  rw [show
    (fun x : AddCircle T =>
      fejerMean (T := T) f n x) =
    (fun x : AddCircle T =>
      ∑ m ∈ fourierIndices n,
        ((((n + 1 - m.natAbs : ℕ) : ℂ) /
          ((n + 1 : ℕ) : ℂ)) *
          fourierCoeff f m *
          fourier m x)) by
    funext x
    exact fejerMean_eq_weighted_fourier_sum
      (T := T) f n x]
  fun_prop

/-- The `n`th Fejér mean bundled as a continuous map `AddCircle T → ℂ`. -/
noncomputable def fejerMeanContinuous
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ) :
    C(AddCircle T, ℂ) :=
  ⟨fun x =>
      fejerMean (T := T) f n x,
    continuous_fejerMean (T := T) f n⟩

@[simp]
lemma fejerMeanContinuous_apply
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (n : ℕ)
    (x : AddCircle T) :
    fejerMeanContinuous (T := T) f n x =
      fejerMean (T := T) f n x := by
  rfl

lemma norm_fejerMeanContinuous_sub_lt
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ))
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N : ℕ,
      ∀ n : ℕ, N ≤ n →
        ‖fejerMeanContinuous (T := T) f n - f‖ < ε := by
  obtain ⟨N, hN⟩ :=
    fejerMean_uniform_error_lt
      (T := T) f ε hε
  refine ⟨N, ?_⟩
  intro n hn
  rw [ContinuousMap.norm_lt_iff_of_nonempty]
  intro x
  simpa using hN n hn x

/-- The bundled Fejér means converge to `f` in the sup-norm topology on continuous maps. -/
theorem tendsto_fejerMeanContinuous
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) :
    Filter.Tendsto
      (fun n : ℕ =>
        fejerMeanContinuous (T := T) f n)
      Filter.atTop
      (nhds f) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    norm_fejerMeanContinuous_sub_lt
      (T := T) f ε hε
  refine ⟨N, ?_⟩
  intro n hn
  simpa [dist_eq_norm] using hN n hn

/-- The Fejér means of a continuous complex-valued function on `AddCircle T`
    converge uniformly to the function. -/
theorem tendstoUniformly_fejerMean
    {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) :
    TendstoUniformly
      (fun n : ℕ =>
        fun x : AddCircle T =>
          fejerMean (T := T) f n x)
      f
      Filter.atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ :=
    fejerMean_uniform_error_lt
      (T := T) f ε hε
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  intro x
  calc
    dist (f x) (fejerMean (T := T) f n x) =
        dist (fejerMean (T := T) f n x) (f x) := by
      exact dist_comm _ _
    _ =
        ‖fejerMean (T := T) f n x - f x‖ := by
      rw [Complex.dist_eq]
    _ < ε := hN n hn x
end AddCircle
