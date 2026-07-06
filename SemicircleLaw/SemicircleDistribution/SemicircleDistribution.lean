/-
Copyright (c) 2025 Fred Rajasekaran. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fred Rajasekaran, Richard Oh, Haoyan Jiang, Kiran Sun, Paul Yoon
-/
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Probability.HasLaw
import Mathlib.Probability.Moments.MGFAnalytic
import SemicircleLaw.Mathlib.Analysis.Real.Pi.Wallis
import SemicircleLaw.Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Semicircle Distributions over ℝ

We define a real-valued semicircle distribution.

## Main definitions

* `semicirclePDFReal`: the function `μ v x ↦ (1 / (2 * pi * v)) * sqrt ((4v - (x - μ)^2)₊)`,
  which is the probability density function of a semicircle distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `semicirclePDF`: `ℝ≥0∞`-valued pdf,
  `semicirclePDF μ v x = ENNReal.ofReal (semicirclePDFReal μ v x)`.
* `semicircleReal`: a semicircle measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `semicirclePDF μ v` with respect to the Lebesgue measure.

## Main results

* `semicircleReal_add_const`: if `X` is a random variable with semicircular law with mean `μ` and
  variance `v`, then `X + y` has semicircular law with mean `μ + y` and variance `v`.
* `semicircleReal_const_mul`: if `X` is a random variable with semicircular law with mean `μ` and
  variance `v`, then `c * X` has semicircular law with mean `c * μ` and variance `c ^ 2 * v`.
* `integral_id_semicircleReal`, `variance_id_semicircleReal`: the mean and variance of
  `semicircleReal μ v` are `μ` and `v`.
* `centralMoment_two_mul_semicircleReal`: the `2 * n`-th central moment of the semicircle
  distribution with variance `v` is `v ^ n` times the `n`-th Catalan number.
* `centralMoment_odd_semicircleReal`: the odd central moments of the semicircle distribution
  vanish.
-/

open scoped ENNReal NNReal Real Complex

open MeasureTheory

open Set

namespace ProbabilityTheory

section SemicirclePDF

/-- Probability density function of the semicircle distribution with mean `μ` and variance `v`.
Note that the square root of a negative number is defined to be zero. -/
noncomputable
def semicirclePDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)

lemma semicirclePDFReal_def (μ : ℝ) (v : ℝ≥0) :
    semicirclePDFReal μ v =
      fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2) := rfl

@[simp]
lemma semicirclePDFReal_zero_var (m : ℝ) : semicirclePDFReal m 0 = 0 := by
  ext x
  simp [semicirclePDFReal]

/-- The semicircle pdf is nonnegative. -/
lemma semicirclePDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ semicirclePDFReal μ v x := by
  rw [semicirclePDFReal]
  positivity

/-- The semicircle pdf is continuous. -/
@[fun_prop]
lemma continuous_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) : Continuous (semicirclePDFReal μ v) := by
  unfold semicirclePDFReal
  fun_prop

/-- The semicircle pdf is measurable. -/
@[fun_prop]
lemma measurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (semicirclePDFReal μ v) :=
  (continuous_semicirclePDFReal μ v).measurable

/-- The semicircle pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (semicirclePDFReal μ v) :=
  (measurable_semicirclePDFReal μ v).stronglyMeasurable

/-- The support of the semicircle pdf is contained in `Ioo (μ - 2 * √v) (μ + 2 * √v)`. -/
lemma support_semicirclePDF_inc (μ : ℝ) (v : ℝ≥0) :
    Function.support (semicirclePDFReal μ v) ⊆ Ioo (μ - 2 * √v) (μ + 2 * √v) := by
  refine Function.support_subset_iff'.mpr fun x hx ↦ ?_
  have h : 4 * v - (x - μ) ^ 2 ≤ 0 := by
    have h4v : 4 * (v : ℝ) = (2 * √v) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt v.coe_nonneg]; ring
    rw [mem_Ioo, not_and_or, not_lt, not_lt] at hx
    rcases hx with hx | hx <;> nlinarith [Real.sqrt_nonneg (v : ℝ)]
  simp [semicirclePDFReal, Real.sqrt_eq_zero_of_nonpos h]

/-- The semicircle pdf is integrable. -/
@[fun_prop]
lemma integrable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) : Integrable (semicirclePDFReal μ v) :=
  (integrableOn_iff_integrable_of_support_subset
    ((support_semicirclePDF_inc μ v).trans Ioo_subset_Icc_self)).mp <|
      (continuous_semicirclePDFReal μ v).continuousOn.integrableOn_compact isCompact_Icc

/-- The semicircle distribution pdf integrates to 1 when the variance is not zero. -/
lemma integral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, semicirclePDFReal μ v x = 1 := by
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h2s : (0 : ℝ) < 2 * √v := mul_pos two_pos (Real.sqrt_pos.mpr hv')
  have hπv : 2 * π * (v : ℝ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) ?_
    exact_mod_cast hv
  have hsq : ∀ x : ℝ, √(4 * v - (2 * √v * x) ^ 2) = 2 * √v * √(1 - x ^ 2) := fun x ↦ by
    rw [show 4 * (v : ℝ) - (2 * √v * x) ^ 2 = (2 * √v) ^ 2 * (1 - x ^ 2) by
      linear_combination (-4 : ℝ) * Real.sq_sqrt v.coe_nonneg,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  calc ∫ x, semicirclePDFReal μ v x
      = (2 * π * v)⁻¹ * ∫ x in (μ - 2 * √v)..(μ + 2 * √v), √(4 * v - (x - μ) ^ 2) := by
        rw [← intervalIntegral.integral_eq_integral_of_support_subset
          ((support_semicirclePDF_inc μ v).trans Ioo_subset_Ioc_self)]
        simp_rw [semicirclePDFReal, one_div, intervalIntegral.integral_const_mul]
    _ = (2 * π * v)⁻¹ * ∫ x in (-(2 * √v))..(2 * √v), √(4 * v - x ^ 2) := by
        rw [intervalIntegral.integral_comp_sub_right (fun x ↦ √(4 * v - x ^ 2)) μ]
        norm_num
    _ = (2 * π * v)⁻¹ * ((2 * √v) * ∫ x in (-1 : ℝ)..1, √(4 * v - (2 * √v * x) ^ 2)) := by
        have h := intervalIntegral.smul_integral_comp_mul_left
          (a := (-1 : ℝ)) (b := 1) (fun y ↦ √(4 * v - y ^ 2)) (2 * √v)
        rw [smul_eq_mul] at h
        rw [h]
        norm_num
    _ = (2 * π * v)⁻¹ * ((2 * √v) * ((2 * √v) * ∫ x in (-1 : ℝ)..1, √(1 - x ^ 2))) := by
        simp_rw [hsq, intervalIntegral.integral_const_mul]
    _ = 1 := by
        rw [integral_sqrt_one_sub_sq, show 2 * √v * (2 * √v * (π / 2)) = 2 * π * v by
          linear_combination (2 * π) * Real.mul_self_sqrt v.coe_nonneg]
        exact inv_mul_cancel₀ hπv

/-- The semicircle distribution pdf has Lebesgue integral 1 when the variance is not zero. -/
lemma lintegral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (semicirclePDFReal μ v x) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_semicirclePDFReal _ _)
    (ae_of_all _ (semicirclePDFReal_nonneg _ _)), integral_semicirclePDFReal_eq_one μ h,
    ENNReal.ofReal_one]

/-- Translating the argument of the semicircle pdf translates its mean. -/
lemma semicirclePDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x - y) = semicirclePDFReal (μ + y) v x := by
  simp only [semicirclePDFReal]
  rw [sub_add_eq_sub_sub_swap]

/-- Translating the argument of the semicircle pdf translates its mean. -/
lemma semicirclePDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x + y) = semicirclePDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← semicirclePDFReal_sub, sub_eq_add_neg, neg_neg]

/-- Rescaling the argument of the semicircle pdf rescales its mean and variance. -/
lemma semicirclePDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c⁻¹ * x)
    = |c| * semicirclePDFReal (c * μ) (NNReal.mk (c ^ 2) (sq_nonneg _) * v) x := by
  simp only [semicirclePDFReal, NNReal.coe_mul, NNReal.coe_mk]
  rw [show 4 * (v : ℝ) - (c⁻¹ * x - μ) ^ 2 = (c⁻¹) ^ 2 * (4 * (c ^ 2 * v) - (x - c * μ) ^ 2) by
      field_simp,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_inv, ← sq_abs c]
  linear_combination (-(2 * π * (v : ℝ))⁻¹ * |c|⁻¹ * √(4 * (|c| ^ 2 * v) - (x - c * μ) ^ 2)) *
    mul_inv_cancel₀ (abs_ne_zero.mpr hc)

/-- Rescaling the argument of the semicircle pdf rescales its mean and variance. -/
lemma semicirclePDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c * x)
      = |c⁻¹| * semicirclePDFReal (c⁻¹ * μ)
        (NNReal.mk ((c^2)⁻¹) (inv_nonneg.mpr (sq_nonneg _)) * v) x := by
  conv_lhs => rw [← inv_inv c, semicirclePDFReal_inv_mul (inv_ne_zero hc)]
  simp

/-- The pdf of a semicircle distribution on ℝ with mean `μ` and variance `v`. -/
noncomputable
def semicirclePDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (semicirclePDFReal μ v x)

lemma semicirclePDF_def (μ : ℝ) (v : ℝ≥0) :
    semicirclePDF μ v = fun x ↦ ENNReal.ofReal (semicirclePDFReal μ v x) := rfl

@[simp]
lemma semicirclePDF_zero_var (μ : ℝ) : semicirclePDF μ 0 = 0 := by ext; simp [semicirclePDF]

@[simp]
lemma toReal_semicirclePDF {μ : ℝ} {v : ℝ≥0} (x : ℝ) :
    (semicirclePDF μ v x).toReal = semicirclePDFReal μ v x := by
  rw [semicirclePDF, ENNReal.toReal_ofReal (semicirclePDFReal_nonneg μ v x)]

lemma semicirclePDF_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ semicirclePDF μ v x :=
  zero_le

lemma semicirclePDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x < ∞ := by
  simp [semicirclePDF]

lemma semicirclePDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x ≠ ∞ := by
  simp [semicirclePDF]

/-- The support of the semicircle pdf with mean `μ` and variance `v ≠ 0` is
`Ioo (μ - 2 * √v) (μ + 2 * √v)`. -/
@[simp]
lemma support_semicirclePDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Function.support (semicirclePDF μ v) = Ioo (μ - 2 * √v) (μ + 2 * √v) := by
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have h4v : 4 * (v : ℝ) = (2 * √v) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt v.coe_nonneg]; ring
  ext x
  simp only [Function.mem_support, semicirclePDF, semicirclePDFReal, ne_eq,
    ENNReal.ofReal_eq_zero, not_le, mem_Ioo]
  rw [mul_pos_iff_of_pos_left
      (one_div_pos.mpr (mul_pos (mul_pos two_pos Real.pi_pos) hv')),
    Real.sqrt_pos, sub_pos, h4v,
    sq_lt_sq, abs_of_nonneg (show (0 : ℝ) ≤ 2 * √v by positivity), abs_sub_lt_iff]
  constructor <;> exact fun h ↦ ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

@[fun_prop]
lemma measurable_semicirclePDF (μ : ℝ) (v : ℝ≥0) : Measurable (semicirclePDF μ v) :=
  (measurable_semicirclePDFReal _ _).ennreal_ofReal

@[simp]
lemma lintegral_semicirclePDF_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, semicirclePDF μ v x = 1 :=
  lintegral_semicirclePDFReal_eq_one μ h

end SemicirclePDF

section SemicircleDistribution

/-- A semicircle distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def semicircleReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (semicirclePDF μ v)

lemma semicircleReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v = volume.withDensity (semicirclePDF μ v) := if_neg hv

@[simp]
lemma semicircleReal_zero_var (μ : ℝ) : semicircleReal μ 0 = Measure.dirac μ := if_pos rfl

instance instIsProbabilityMeasureSemicircleReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (semicircleReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [semicircleReal_of_var_ne_zero, h]

lemma noAtoms_semicircleReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (semicircleReal μ v) := by
  rw [semicircleReal_of_var_ne_zero _ h]
  infer_instance

lemma semicircleReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    semicircleReal μ v s = ∫⁻ x in s, semicirclePDF μ v x := by
  rw [semicircleReal_of_var_ne_zero _ hv, withDensity_apply' _ s]

lemma semicircleReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    semicircleReal μ v s = ENNReal.ofReal (∫ x in s, semicirclePDFReal μ v x) := by
  rw [semicircleReal_apply _ hv s, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_semicirclePDFReal _ _).restrict
  · exact ae_of_all _ (semicirclePDFReal_nonneg _ _)

lemma semicircleReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    semicircleReal μ v ≪ volume := by
  rw [semicircleReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

lemma rnDeriv_semicircleReal (μ : ℝ) (v : ℝ≥0) :
    ∂(semicircleReal μ v)/∂volume =ₐₛ semicirclePDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, semicircleReal_zero_var, semicirclePDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero, add_zero]
  · rw [semicircleReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_semicirclePDF μ v)

lemma integral_semicircleReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) :
    ∫ x, f x ∂(semicircleReal μ v) = ∫ x, semicirclePDFReal μ v x • f x := by
  simp [semicircleReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_semicirclePDF _ _)
      (ae_of_all _ fun _ ↦ semicirclePDF_lt_top)]

section Transformations

variable {μ : ℝ} {v : ℝ≥0}

lemma _root_.MeasurableEquiv.semicircleReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (semicircleReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * semicirclePDFReal μ v (f x)) := by
  rw [semicircleReal_of_var_ne_zero _ hv, semicirclePDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (semicirclePDFReal_nonneg _ _)) (integrable_semicirclePDFReal _ _)

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_add_const (y : ℝ) :
    (semicircleReal μ v).map (· + y) = semicircleReal (μ + y) v := by
  by_cases hv : v = 0
  · simp [hv, semicircleReal_zero_var]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (semicircleReal μ v).map e.symm = semicircleReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.semicircleReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
  rw [semicircleReal_apply_eq_integral _ hv s']
  simp [e, semicirclePDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_const_add (y : ℝ) :
    (semicircleReal μ v).map (y + ·) = semicircleReal (μ + y) v := by
  simp_rw [add_comm y]
  exact semicircleReal_map_add_const y

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_const_mul (c : ℝ) :
    (semicircleReal μ v).map (c * ·)
    = semicircleReal (c * μ) (NNReal.mk (c ^ 2) (sq_nonneg _) * v) := by
  by_cases hv : v = 0
  · simp [hv, mul_zero, semicircleReal_zero_var]
  by_cases hc : c = 0
  · simp [hc, zero_mul]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x ↦ c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (semicircleReal μ v).map e.symm
    = semicircleReal (c * μ) (.mk (c ^ 2) (sq_nonneg _) * v)
  ext s' hs'
  rw [MeasurableEquiv.semicircleReal_map_symm_apply hv e he' hs',
    semicircleReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    semicirclePDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_mul_const (c : ℝ) :
    (semicircleReal μ v).map (· * c)
    = semicircleReal (c * μ) (NNReal.mk (c ^ 2) (sq_nonneg _) * v) := by
  simp_rw [mul_comm _ c]
  exact semicircleReal_map_const_mul c

/-- The map of a semicircle distribution by negation is semicircular. -/
lemma semicircleReal_map_neg : (semicircleReal μ v).map (fun x ↦ -x) = semicircleReal (-μ) v := by
  simpa using semicircleReal_map_const_mul (μ := μ) (v := v) (-1)

/-- The map of a semicircle distribution by subtraction of a constant is semicircular. -/
lemma semicircleReal_map_sub_const (y : ℝ) :
    (semicircleReal μ v).map (· - y) = semicircleReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, semicircleReal_map_add_const]

/-- The map of a semicircle distribution by subtraction from a constant is semicircular. -/
lemma semicircleReal_map_const_sub (y : ℝ) :
    (semicircleReal μ v).map (y - ·) = semicircleReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x ↦ y + -x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), semicircleReal_map_neg,
    semicircleReal_map_const_add, add_comm]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X : Ω → ℝ}

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`X + y` has semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_add_const (hX : HasLaw X (semicircleReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ X ω + y) (semicircleReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, semicircleReal_map_add_const y⟩ hX

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`y + X` has semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_const_add (hX : HasLaw X (semicircleReal μ v) P) (y : ℝ) :
    HasLaw (fun ω ↦ y + X ω) (semicircleReal (μ + y) v) P :=
  HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_add y⟩ hX

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`c * X` has semicircular law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma semicircleReal_const_mul (hX : HasLaw X (semicircleReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ c * X ω) (semicircleReal (c * μ) (NNReal.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, semicircleReal_map_const_mul c⟩ hX

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`X * c` has semicircular law with mean `c * μ` and variance `c ^ 2 * v`. -/
lemma semicircleReal_mul_const (hX : HasLaw X (semicircleReal μ v) P) (c : ℝ) :
    HasLaw (fun ω ↦ X ω * c) (semicircleReal (c * μ) (NNReal.mk (c ^ 2) (sq_nonneg _) * v)) P :=
  HasLaw.comp ⟨by fun_prop, semicircleReal_map_mul_const c⟩ hX

end Transformations

section Moments

open Real

variable {μ : ℝ} {v : ℝ≥0}

/-- The product of the semicircle pdf with a power of the centering `x - μ` is integrable. -/
lemma integrable_pow_mul_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) (k : ℕ) :
    Integrable fun x ↦ semicirclePDFReal μ v x * (x - μ) ^ k := by
  refine (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_left _ _).trans
      ((support_semicirclePDF_inc μ v).trans Ioo_subset_Icc_self))).mp ?_
  exact (((continuous_semicirclePDFReal μ v).mul (by fun_prop)).continuousOn).integrableOn_compact
    isCompact_Icc

/-- The integral of an odd power against the centered semicircle pdf vanishes, by symmetry. -/
lemma integral_odd_pow_mul_semicirclePDFReal (v : ℝ≥0) {k : ℕ} (hk : Odd k) :
    ∫ x, semicirclePDFReal 0 v x * x ^ k = 0 := by
  have h : ∀ x : ℝ, semicirclePDFReal 0 v (-x) * (-x) ^ k
      = -(semicirclePDFReal 0 v x * x ^ k) := fun x ↦ by
    rw [hk.neg_pow]
    simp only [semicirclePDFReal, sub_zero, neg_sq]
    ring
  have h2 := integral_neg_eq_self (fun x ↦ semicirclePDFReal 0 v x * x ^ k) volume
  simp only [h, integral_neg] at h2
  linarith

/-- The mean of a real semicircle distribution `semicircleReal μ v` is
its mean parameter `μ`. -/
@[simp]
lemma integral_id_semicircleReal : ∫ x, x ∂semicircleReal μ v = μ := by
  by_cases hv : v = 0
  · simp [hv]
  rw [integral_semicircleReal_eq_integral_smul hv]
  have h : ∀ x : ℝ, semicirclePDFReal μ v x • x
      = semicirclePDFReal μ v x * (x - μ) ^ 1 + μ * semicirclePDFReal μ v x := fun x ↦ by
    simp only [smul_eq_mul, pow_one]
    ring
  simp_rw [h]
  rw [integral_add (integrable_pow_mul_semicirclePDFReal μ v 1)
      ((integrable_semicirclePDFReal μ v).const_mul μ),
    show (fun x : ℝ ↦ semicirclePDFReal μ v x * (x - μ) ^ 1)
        = fun x ↦ (fun y ↦ semicirclePDFReal 0 v y * y ^ 1) (x - μ) by
      funext x
      simp only [semicirclePDFReal_sub x μ, zero_add],
    integral_sub_right_eq_self (fun y ↦ semicirclePDFReal 0 v y * y ^ 1) μ,
    integral_odd_pow_mul_semicirclePDFReal v odd_one, zero_add, integral_const_mul,
    integral_semicirclePDFReal_eq_one μ hv, mul_one]

/-- All the moments of a real semicircle distribution are finite. That is, the identity is in Lp
for all finite `p`. -/
lemma memLp_id_semicircleReal (p : ℝ≥0) : MemLp id p (semicircleReal μ v) := by
  refine MemLp.of_bound (by fun_prop) (|μ| + 2 * √v) ?_
  by_cases hv : v = 0
  · rw [hv, semicircleReal_zero_var, ae_dirac_eq]
    refine Filter.eventually_pure.mpr ?_
    simp
  · have h0 : semicircleReal μ v (Ioo (μ - 2 * √v) (μ + 2 * √v))ᶜ = 0 := by
      rw [semicircleReal_apply _ hv,
        setLIntegral_congr_fun measurableSet_Ioo.compl
          (fun x hx ↦ Function.notMem_support.mp (support_semicirclePDF hv ▸ hx)),
        lintegral_zero]
    refine ae_iff.mpr (measure_mono_null ?_ h0)
    intro x hx
    simp only [mem_setOf_eq, id_eq, Real.norm_eq_abs, not_le] at hx
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt]
    by_contra hcon
    push Not at hcon
    rcases abs_cases x with ⟨hx', _⟩ | ⟨hx', _⟩ <;> rcases abs_cases μ with ⟨hμ', _⟩ | ⟨hμ', _⟩ <;>
      linarith [Real.sqrt_nonneg (v : ℝ), hcon.1, hcon.2]

/-- All the moments of a real semicircle distribution are finite. That is, the identity is in Lp
for all finite `p`. -/
lemma memLp_id_semicircleReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (semicircleReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_semicircleReal p

/-- The `2 * n`-th central moment of the semicircle distribution with variance `v` is
`v ^ n` times the `n`-th Catalan number. -/
lemma centralMoment_fun_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) (2 * n) (semicircleReal μ v) = v ^ n * catalan n := by
  by_cases hv : v = 0
  · subst hv
    rcases n with - | m
    · simp [centralMoment]
    · simp [centralMoment, integral_dirac, zero_pow]
  have hv' : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : (0 : ℝ) < √v := Real.sqrt_pos.mpr hv'
  have hsq : ∀ x : ℝ, √(4 * v - (2 * √v * x) ^ 2) = 2 * √v * √(1 - x ^ 2) := fun x ↦ by
    rw [show 4 * (v : ℝ) - (2 * √v * x) ^ 2 = (2 * √v) ^ 2 * (1 - x ^ 2) by
      linear_combination (-4 : ℝ) * Real.sq_sqrt v.coe_nonneg,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hsupp : Function.support (fun y : ℝ ↦ semicirclePDFReal 0 v y * y ^ (2 * n))
      ⊆ Ioc (2 * √v * (-1)) (2 * √v * 1) := by
    refine (Function.support_mul_subset_left _ _).trans
      ((support_semicirclePDF_inc 0 v).trans fun x hx ↦ ?_)
    rw [zero_sub, zero_add, mem_Ioo] at hx
    rw [mem_Ioc]
    constructor <;> nlinarith [hx.1, hx.2]
  simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, integral_id_semicircleReal]
  rw [integral_semicircleReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul]
  rw [show (fun x : ℝ ↦ semicirclePDFReal μ v x * (x - μ) ^ (2 * n))
      = fun x ↦ (fun y ↦ semicirclePDFReal 0 v y * y ^ (2 * n)) (x - μ) by
      funext x
      simp only [semicirclePDFReal_sub x μ, zero_add],
    integral_sub_right_eq_self (fun y ↦ semicirclePDFReal 0 v y * y ^ (2 * n)) μ,
    ← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  have hcomp := intervalIntegral.smul_integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun y ↦ semicirclePDFReal 0 v y * y ^ (2 * n)) (2 * √v)
  rw [smul_eq_mul] at hcomp
  rw [← hcomp]
  have hint : ∀ x : ℝ, semicirclePDFReal 0 v (2 * √v * x) * (2 * √v * x) ^ (2 * n)
      = (2 * √v * (2 ^ (2 * n) * v ^ n) / (2 * π * v)) * (x ^ (2 * n) * √(1 - x ^ 2)) := fun x ↦ by
    simp only [semicirclePDFReal, sub_zero]
    rw [hsq x, mul_pow, show ((2 : ℝ) * √v) ^ (2 * n) = 2 ^ (2 * n) * v ^ n by
      rw [mul_pow, pow_mul (√(v : ℝ)) 2 n, Real.sq_sqrt v.coe_nonneg]]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_const_mul, integral_pow_mul_sqrt_one_sub_sq n,
    ← two_pow_mul_wallis_prod_sub n, ← mul_assoc,
    show (2 * √(v : ℝ)) * (2 * √v * (2 ^ (2 * n) * v ^ n) / (2 * π * v))
        = 2 ^ (2 * n + 1) * v ^ n / π by
      field_simp
      linear_combination (2 * (2 : ℝ) ^ (2 * n)) * Real.mul_self_sqrt v.coe_nonneg]
  field_simp

/-- The `2 * n`-th central moment of the semicircle distribution with variance `v` is
`v ^ n` times the `n`-th Catalan number. -/
lemma centralMoment_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (semicircleReal μ v) = v ^ n * catalan n := by
  exact centralMoment_fun_two_mul_semicircleReal μ v n

/-- The variance of a real semicircle distribution `semicircleReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_fun_id_semicircleReal : Var[fun x ↦ x; semicircleReal μ v] = v := by
  rw [← centralMoment_two_eq_variance (by fun_prop)]
  simpa [catalan_one] using centralMoment_fun_two_mul_semicircleReal μ v 1

/-- The variance of a real semicircle distribution `semicircleReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_id_semicircleReal : Var[id; semicircleReal μ v] = v :=
  variance_fun_id_semicircleReal

/-- The odd central moments of the semicircle distribution vanish. -/
lemma centralMoment_fun_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) ((2 * n) + 1) (semicircleReal μ v) = 0 := by
  by_cases hv : v = 0
  · subst hv
    simp [centralMoment, integral_dirac, zero_pow]
  simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, integral_id_semicircleReal]
  rw [integral_semicircleReal_eq_integral_smul hv]
  simp_rw [smul_eq_mul]
  rw [show (fun x : ℝ ↦ semicirclePDFReal μ v x * (x - μ) ^ (2 * n + 1))
      = fun x ↦ (fun y ↦ semicirclePDFReal 0 v y * y ^ (2 * n + 1)) (x - μ) by
      funext x
      simp only [semicirclePDFReal_sub x μ, zero_add],
    integral_sub_right_eq_self (fun y ↦ semicirclePDFReal 0 v y * y ^ (2 * n + 1)) μ,
    integral_odd_pow_mul_semicirclePDFReal v (odd_two_mul_add_one n)]

/-- The odd central moments of the semicircle distribution vanish. -/
lemma centralMoment_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id ((2 * n) + 1) (semicircleReal μ v) = 0 := by
  exact centralMoment_fun_odd_semicircleReal μ v n

end Moments

end SemicircleDistribution

end ProbabilityTheory
