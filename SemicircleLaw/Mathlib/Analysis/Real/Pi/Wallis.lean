/-
Copyright (c) 2025 Fred Rajasekaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fred Rajasekaran, Richard Oh, Haoyan Jiang, Kiran Sun, Paul Yoon
-/
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Wallis-type products, central binomial coefficients and Catalan numbers

Two identities about the Wallis-type products `∏ i ∈ range n, (2 * i + 1) / (2 * i + 2)` used by
the semicircle distribution, intended for `Mathlib/Analysis/Real/Pi/Wallis.lean` (next to
`Real.Wallis.W_eq_factorial_ratio`):

* `prod_odd_over_even_central_choose`: the quotient of the product of the first `n` odd numbers
  by the product of the first `n` even numbers is `(2 * n).choose n / 2 ^ (2 * n)`. In terms of
  double factorials (`Nat.doubleFactorial_eq_prod_odd`/`_even`) this is
  `(2 * n - 1)‼ / (2 * n)‼ = (2 * n).choose n / 2 ^ (2 * n)`.
* `two_pow_mul_wallis_prod_sub`: `2 ^ (2 * n + 1)` times the difference of consecutive
  Wallis-type products is the `n`-th Catalan number.
-/

open scoped Real

/-- The quotient of the product of the first `n` odd numbers by the product of the first `n` even
numbers is `(2 * n).choose n / 2 ^ (2 * n)`. -/
lemma prod_odd_over_even_central_choose (n : ℕ) :
    (∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1)) / (∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1)))
      = (2 * n).choose n / 2 ^ (2 * n) := by
  have h_all : (∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1))
      * ∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1)) = (2 * n).factorial := by
    rw [← Finset.prod_mul_distrib]
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.prod_range_succ, ih, show 2 * (m + 1) = 2 * m + 1 + 1 by ring,
        Nat.factorial_succ, Nat.factorial_succ]
      push_cast
      ring
  have h_even : ∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1)) = 2 ^ n * n.factorial := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    congr 1
    exact_mod_cast Finset.prod_range_add_one_eq_factorial n
  have h_choose : ((2 * n).choose n : ℝ) * n.factorial * n.factorial = (2 * n).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
    rw [show 2 * n - n = n by omega] at h
    exact_mod_cast h
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have h_odd : (∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1))
      = (2 * n).factorial / (2 ^ n * n.factorial) := by
    rw [eq_div_iff (by positivity), ← h_even]
    exact h_all
  rw [h_odd, h_even]
  field_simp
  linear_combination (-((2 : ℝ) ^ (2 * n))) * h_choose

/-- `2 ^ (2 * n + 1)` times the difference of consecutive Wallis-type products is the `n`-th
Catalan number. -/
lemma two_pow_mul_wallis_prod_sub (n : ℕ) :
    2 ^ (2 * n + 1) * ((∏ i ∈ Finset.range n, (2 * (i : ℝ) + 1) / (2 * i + 2))
      - ∏ i ∈ Finset.range (n + 1), (2 * (i : ℝ) + 1) / (2 * i + 2)) = catalan n := by
  have hW : ∀ m : ℕ, (∏ i ∈ Finset.range m, ((2 * (i : ℝ) + 1) / (2 * i + 2)))
      = (2 * m).choose m / 2 ^ (2 * m) := fun m ↦ by
    rw [Finset.prod_div_distrib, show (∏ i ∈ Finset.range m, (2 * (i : ℝ) + 2))
        = ∏ i ∈ Finset.range m, (2 * ((i : ℝ) + 1)) from
        Finset.prod_congr rfl fun i _ ↦ by ring,
      prod_odd_over_even_central_choose]
  have hcat : ((n : ℝ) + 1) * catalan n = (2 * n).choose n := by
    have h := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom] at h
    exact_mod_cast h
  rw [Finset.prod_range_succ, hW]
  have h1 : ((2 : ℝ) * n + 2) ≠ 0 := by positivity
  field_simp
  linear_combination (-2 * (2 : ℝ) ^ (2 * n)) * hcat
