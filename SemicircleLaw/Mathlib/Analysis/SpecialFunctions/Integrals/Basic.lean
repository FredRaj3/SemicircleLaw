/-
Copyright (c) 2025 Fred Rajasekaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fred Rajasekaran, Richard Oh, Haoyan Jiang, Kiran Sun, Paul Yoon
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integrals of powers of `sin` and of `x ^ (2 * n) * √(1 - x ^ 2)`

Two integral computations used by the semicircle distribution, intended for
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean`:

* `integral_sin_pow_pi_div_two` (next to `integral_sin_pow_even`): the integral of `sin x ^ m`
  over `[0, π/2]` is half its integral over `[0, π]`. This is the `sin` analogue of
  `EulerSine.integral_cos_pow_eq`.
* `integral_pow_mul_sqrt_one_sub_sq` (next to `integral_sqrt_one_sub_sq`, which is the case
  `n = 0`): the even moments of `√(1 - x ^ 2)` on `[-1, 1]`, as a difference of consecutive
  Wallis-type products.
-/

open Real Set

/-- The integral of a power of `sin` over `[0, π/2]` is half its integral over `[0, π]`. -/
lemma integral_sin_pow_pi_div_two (m : ℕ) :
    ∫ x in (0 : ℝ)..(π / 2), sin x ^ m = 1 / 2 * ∫ x in (0 : ℝ)..π, sin x ^ m := by
  have h : ∫ x in (π / 2 : ℝ)..π, sin x ^ m = ∫ x in (0 : ℝ)..(π / 2), sin x ^ m := by
    have h1 := intervalIntegral.integral_comp_sub_left (a := (π / 2 : ℝ)) (b := π)
      (fun y ↦ sin y ^ m) π
    simp only [Real.sin_pi_sub, sub_self, sub_half] at h1
    exact h1
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (0 : ℝ)) (b := π / 2) (c := π)
    ((continuous_sin.pow m).intervalIntegrable _ _)
    ((continuous_sin.pow m).intervalIntegrable _ _), h]
  ring

/-- The integral of `x ^ (2 * n) * √(1 - x ^ 2)` over `[-1, 1]`, as a difference of Wallis-type
products. The case `n = 0` is `integral_sqrt_one_sub_sq`. -/
lemma integral_pow_mul_sqrt_one_sub_sq (n : ℕ) :
    ∫ x in (-1 : ℝ)..1, x ^ (2 * n) * √(1 - x ^ 2)
      = π * ((∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2))
          - ∏ i ∈ Finset.range (n + 1), (2 * (i : ℝ) + 1) / (2 * i + 2)) := by
  have hcont : Continuous fun x : ℝ ↦ x ^ (2 * n) * √(1 - x ^ 2) := by fun_prop
  have heven : ∫ x in (0 : ℝ)..1, x ^ (2 * n) * √(1 - x ^ 2)
      = ∫ x in (-1 : ℝ)..(0 : ℝ), x ^ (2 * n) * √(1 - x ^ 2) := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (fun x ↦ x ^ (2 * n) * √(1 - x ^ 2))
    simpa only [(even_two_mul n).neg_pow, neg_sq, neg_zero] using h
  have hsplit : ∫ x in (-1 : ℝ)..1, x ^ (2 * n) * √(1 - x ^ 2)
      = 2 * ∫ x in (0 : ℝ)..1, x ^ (2 * n) * √(1 - x ^ 2) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (a := (-1 : ℝ)) (b := 0) (c := 1)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _), ← heven]
    ring
  have hsub : ∫ x in (0 : ℝ)..1, x ^ (2 * n) * √(1 - x ^ 2)
      = ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ (2 * n) * (cos θ * cos θ) := by
    calc ∫ x in (0 : ℝ)..1, x ^ (2 * n) * √(1 - x ^ 2)
        = ∫ x in sin (0 : ℝ)..sin (π / 2), x ^ (2 * n) * √(1 - x ^ 2) := by
          rw [Real.sin_zero, Real.sin_pi_div_two]
      _ = ∫ θ in (0 : ℝ)..(π / 2), (sin θ ^ (2 * n) * √(1 - sin θ ^ 2)) * cos θ :=
          (intervalIntegral.integral_comp_mul_deriv (fun x _ ↦ Real.hasDerivAt_sin x)
            Real.continuousOn_cos (by fun_prop)).symm
      _ = ∫ θ in (0 : ℝ)..(π / 2), sin θ ^ (2 * n) * (cos θ * cos θ) := by
          refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
          rw [uIcc_of_le (by positivity)] at hθ
          have hcos : 0 ≤ cos θ := Real.cos_nonneg_of_mem_Icc
            ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
          rw [show 1 - sin θ ^ 2 = cos θ ^ 2 by
              rw [← Real.sin_sq_add_cos_sq θ]; ring,
            Real.sqrt_sq hcos]
          ring
  have hsc : ∀ θ : ℝ, sin θ ^ (2 * n) * (cos θ * cos θ)
      = sin θ ^ (2 * n) - sin θ ^ (2 * (n + 1)) := fun θ ↦ by
    linear_combination (sin θ ^ (2 * n)) * Real.sin_sq_add_cos_sq θ
  rw [hsplit, hsub]
  simp_rw [hsc]
  rw [intervalIntegral.integral_sub ((continuous_sin.pow _).intervalIntegrable _ _)
      ((continuous_sin.pow _).intervalIntegrable _ _),
    integral_sin_pow_pi_div_two, integral_sin_pow_pi_div_two, integral_sin_pow_even,
    integral_sin_pow_even]
  ring
