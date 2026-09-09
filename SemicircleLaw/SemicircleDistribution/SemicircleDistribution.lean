/-Default imports-/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.Tactic

/-Richard's imports-/
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Tactic.Continuity
import Mathlib.Topology.Basic
import Aesop

/-Option settings-/

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

* `semicircleReal_add_const`: if `X` is a random variable with semicircle distribution with mean `μ`
 and variance `v`, then `X + y` is semicircular with mean `μ + y` and variance `v`.
* `semicircleReal_const_mul`: if `X` is a random variable with semicircle distribution with mean `μ`
 and variance `v`, then `c * X` is semicircular with mean `c * μ` and variance `c^2 * v`.
* `centralMoment_two_mul_semicircleReal`: the 2nth moment of the semicircle distribution is equal
to the nth Catalan number
* `centralMoment_odd_semicircleReal`: the odd moments of the semicircle distribution are zero
-/

open scoped ENNReal NNReal Real Complex

open MeasureTheory

/-Opened by Richard-/
open Set

namespace ProbabilityTheory

section SemicirclePDF

/-- Probability density function of the semicircle distribution with mean `μ` and variance `v`.
Note that the squared root of a negative number is defined to be zero.  -/
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
lemma Cont_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) : Continuous (semicirclePDFReal μ v) := by
    rw [semicirclePDFReal_def]
    set f := fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)
    have h : Continuous f := by continuity
    exact h

/-- The semicircle pdf is measurable. -/
@[fun_prop]
lemma measurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (semicirclePDFReal μ v) := by
  have h : Continuous (semicirclePDFReal μ v) := by apply Cont_semicirclePDFReal
  apply Continuous.borel_measurable h

/-- The semicircle pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (semicirclePDFReal μ v) :=
  (measurable_semicirclePDFReal μ v).stronglyMeasurable

/-- The support of the semicircle pdf is contained in [μ - 2 * √v, μ + 2 * √v]. --/
lemma support_semicirclePDF_inc (μ : ℝ) (v : ℝ≥0) :
Function.support (semicirclePDFReal μ v) ⊆ Icc (μ - 2 * √v) (μ + 2 * √v) := by
  set f := fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)
  set I := Icc (μ - 2 * √v) (μ + 2 * √v) with hI
  intro x hx
  by_contra hxI
  have h1 : f x = 0 := by
    rw [hI, ← mem_Icc_iff_abs_le, not_le] at hxI
    simp [f, Real.sqrt_eq_zero_of_nonpos (show 4 * (v : ℝ) - (x - μ) ^ 2 ≤ 0 by
      nlinarith [Real.sq_sqrt v.coe_nonneg, Real.sqrt_nonneg (v : ℝ), sq_abs (μ - x)])]
  have h2 : x ∉ Function.support f := by simpa [Function.support] using h1
  exact h2 hx

/-- The semicircle pdf is integrable. -/
@[fun_prop]
lemma integrable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (semicirclePDFReal μ v) := by
  rw [semicirclePDFReal_def]
  set f := fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)
  have h1 : Continuous f := by apply Cont_semicirclePDFReal
  set I := Icc (μ - 2 * √v) (μ + 2 * √v) with hI
  have h2 : IsCompact I := by simpa using isCompact_Icc
  have h3 : IntegrableOn f I := by simpa using (h1.continuousOn).integrableOn_compact h2
  have h4 : Function.support f ⊆ I := by apply support_semicirclePDF_inc
  exact (integrableOn_iff_integrable_of_support_subset h4).mp h3

/-- The semicircle distribution pdf integrates to 1 when the variance is not zero. -/
lemma integral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, semicirclePDFReal μ v x = 1 := by
  rw [semicirclePDFReal_def]
  simp
  set I := Icc (μ - 2 * √v) (μ + 2 * √v) with hI
  set A := (2 * π * v)⁻¹
  have hA : A ≠ 0 := by
    simp [A]; grind
  have c1 : ∫ (x : ℝ), (v)⁻¹ * (π⁻¹ * 2⁻¹) * √(4 * v - (x - μ) ^ 2)
  = ∫ (x : ℝ), (2 * π * v)⁻¹ * √(4 * v - (x - μ) ^ 2) := by
    apply integral_congr_ae
    simp_all only [ne_eq, mul_inv_rev, mul_eq_zero, inv_eq_zero, NNReal.coe_eq_zero,
    OfNat.ofNat_ne_zero, or_false, false_or, NNReal.coe_inv, Filter.EventuallyEq.refl, A, I]
  have c2 : ∫ x in I, (2 * π * v)⁻¹ * √(4 * v - (x - μ) ^ 2)
  = ∫ (x : ℝ), (2 * π * v)⁻¹ * √(4 * v - (x - μ) ^ 2) := by
    set f := fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)
    have c21 : Function.support f ⊆ I := by apply support_semicirclePDF_inc
    have c22 : f = fun x ↦ (2 * π * v)⁻¹ * √(4 * v - (x - μ) ^ 2) := by simp [f]
    refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
    apply ae_of_all
    intro a haI
    have c23 : a ∉ Function.support f := by exact fun a_1 ↦ haI (c21 a_1)
    have c24 : f a = 0 := by simpa [Function.mem_support] using c23
    simpa [c22] using c24
  have c3 : ∫ x in I, A * √(4 * v - (x - μ) ^ 2) = A * ∫ x in I, √(4 * v - (x - μ) ^ 2) := by
    exact integral_const_mul A fun a ↦ √(4 * v - (a - μ) ^ 2)
  have c4 : ∫ x in I, √(4 * v - (x - μ) ^ 2) = A⁻¹ := by
    have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    have hsq : √(v : ℝ) ^ 2 = (v : ℝ) := Real.sq_sqrt v.coe_nonneg
    have hs : 0 < √(v : ℝ) := Real.sqrt_pos.mpr hv0
    -- pointwise form of the integrand after scaling
    have hpt : ∀ t : ℝ, √(4 * (v : ℝ) - (2 * √v * t) ^ 2) = 2 * √v * √(1 - t ^ 2) := by
      intro t
      have h4 : 4 * (v : ℝ) - (2 * √v * t) ^ 2 = (2 * √v) ^ 2 * (1 - t ^ 2) := by
        nlinarith [hsq]
      rw [h4, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    -- set integral over Icc  →  interval integral
    have h1 : ∫ x in I, √(4 * (v : ℝ) - (x - μ) ^ 2)
        = ∫ x in (μ - 2 * √v)..(μ + 2 * √v), √(4 * (v : ℝ) - (x - μ) ^ 2) := by
      rw [intervalIntegral.integral_of_le (by nlinarith), hI,
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    -- translate by μ
    have h2 : ∫ x in (μ - 2 * √v)..(μ + 2 * √v), √(4 * (v : ℝ) - (x - μ) ^ 2)
        = ∫ y in (-(2 * √v))..(2 * √v), √(4 * (v : ℝ) - y ^ 2) := by
      have h := intervalIntegral.integral_comp_sub_right
        (a := μ - 2 * √(v : ℝ)) (b := μ + 2 * √(v : ℝ))
        (fun y : ℝ => √(4 * (v : ℝ) - y ^ 2)) μ
      rw [show μ - 2 * √(v : ℝ) - μ = -(2 * √(v : ℝ)) by ring,
          show μ + 2 * √(v : ℝ) - μ = 2 * √(v : ℝ) by ring] at h
      exact h
    -- rescale by 2√v
    have h3 : ∫ y in (-(2 * √v))..(2 * √v), √(4 * (v : ℝ) - y ^ 2)
        = (2 * √v) * ∫ t in (-1 : ℝ)..1, √(4 * (v : ℝ) - (2 * √v * t) ^ 2) := by
      have h := intervalIntegral.smul_integral_comp_mul_left
        (a := (-1 : ℝ)) (b := (1 : ℝ))
        (fun y : ℝ => √(4 * (v : ℝ) - y ^ 2)) (2 * √(v : ℝ))
      simp only [smul_eq_mul, mul_neg, mul_one] at h
      exact h.symm
    rw [h1, h2, h3]
    simp only [hpt, intervalIntegral.integral_const_mul, integral_sqrt_one_sub_sq, A]
    field_simp
    nlinarith [hsq]
  calc
    ∫ (x : ℝ), (v)⁻¹ * (π⁻¹ * 2⁻¹) * √(4 * v - (x - μ) ^ 2)
    = ∫ (x : ℝ), (2 * π * v)⁻¹ * √(4 * v - (x - μ) ^ 2) := by apply c1
    _ = ∫ x in I, A * √(4 * v - (x - μ) ^ 2) := by rw [← c2]
    _ = A * ∫ x in I, √(4 * v - (x - μ) ^ 2) := by exact c3
    _ = A * A⁻¹ := by rw [c4]
    _ = 1 := by rw [mul_inv_cancel₀ hA]

/-- The semicircle distribution pdf integrates to 1 when the variance is not zero. -/
lemma lintegral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (semicirclePDFReal μ v x) = 1 := by
  rw [semicirclePDFReal_def]
  set f := fun x ↦ 1 / (2 * π * ↑v) * √(4 * ↑v - (x - μ) ^ 2) with hf
  have c1 := semicirclePDFReal_nonneg
  have c3 := stronglyMeasurable_semicirclePDFReal
  have c4 : AEStronglyMeasurable (semicirclePDFReal μ v) := by
    apply StronglyMeasurable.aestronglyMeasurable; apply c3
  have c6 :  0 ≤ᶠ[ae ℙ] (semicirclePDFReal μ v) := by
    apply ae_of_all; simp; apply c1
  have c7 : ∫ (x : ℝ), (semicirclePDFReal μ v x)
    = (∫⁻ (x : ℝ), ENNReal.ofReal (semicirclePDFReal μ v x)).toReal := by
    apply integral_eq_lintegral_of_nonneg_ae; exact c6; exact c4
  have c8 : 1 = (∫⁻ (x : ℝ), ENNReal.ofReal (semicirclePDFReal μ v x)).toReal := by
    have c81 :  ∫ (x : ℝ), (semicirclePDFReal μ v x) = 1 := by
      apply integral_semicirclePDFReal_eq_one; exact h
    rw [← c81]; apply c7
  have c9 : ENNReal.toReal (1 : ℝ≥0∞) = (1 : ℝ) := by exact rfl
  have c10 : ∫⁻ (x : ℝ), ENNReal.ofReal (semicirclePDFReal μ v x) = (1 : ℝ≥0∞) := by
    rw [← c9] at c8
    apply (ENNReal.toReal_eq_one_iff (∫⁻ (x : ℝ), ENNReal.ofReal (semicirclePDFReal μ v x))).mp
    exact id (Eq.symm c8)
  have c11 : ∫⁻ (x : ℝ), ENNReal.ofReal ((fun x ↦ 1 / (2 * π * ↑v) * √(4 * ↑v - (x - μ) ^ 2)) x)
    = ∫⁻ (x : ℝ), ENNReal.ofReal (semicirclePDFReal μ v x) := by rw [← semicirclePDFReal_def]
  rw [c11, ← c10]

lemma semicirclePDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x - y) = semicirclePDFReal (μ + y) v x := by
  simp only [semicirclePDFReal]
  rw [sub_add_eq_sub_sub_swap]

lemma semicirclePDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x + y) = semicirclePDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← semicirclePDFReal_sub, sub_eq_add_neg, neg_neg]

lemma semicirclePDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c⁻¹ * x)
    = |c| * semicirclePDFReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) x := by
  have key : 4 * ((c : ℝ) ^ 2 * v) - (x - c * μ) ^ 2
      = c ^ 2 * (4 * v - (c⁻¹ * x - μ) ^ 2) := by field_simp
  simp only [semicirclePDFReal, NNReal.coe_mul, NNReal.coe_mk, key,
    Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
  field_simp
  rw [sq_abs, mul_comm]

lemma semicirclePDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c * x)
      = |c⁻¹| * semicirclePDFReal (c⁻¹ * μ) (⟨(c^2)⁻¹, inv_nonneg.mpr (sq_nonneg _)⟩ * v) x := by
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

lemma semicirclePDF_nonneg (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 ≤ semicirclePDF μ v x := by
  rw [semicirclePDF]; positivity


lemma semicirclePDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x < ∞ := by
simp [semicirclePDF]

lemma semicirclePDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x ≠ ∞ := by
simp [semicirclePDF]

/-- The support of the semicircle pdf with mean μ and variance v is [μ - 2√ v, μ + 2√ v]
Need to set the interval correctly in the statement of the lemma-/
@[simp]
lemma support_semicirclePDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Function.support (semicirclePDF μ v) = Ioo (μ - 2 * √v) (μ + 2 * √v) := by
  have hv0 : (0 : ℝ) < v := by
    have : 0 < v := pos_iff_ne_zero.mpr hv
    exact_mod_cast this
  have hs : √(v : ℝ) ^ 2 = v := Real.sq_sqrt hv0.le
  have hspos : 0 < √(v : ℝ) := Real.sqrt_pos.mpr hv0
  have hconst : 0 < 1 / (2 * π * (v : ℝ)) := by positivity
  ext x
  simp only [Function.mem_support, ne_eq, semicirclePDF, semicirclePDFReal,
    ENNReal.ofReal_eq_zero, not_le, mem_Ioo]
  have hmul : 0 < 1 / (2 * π * (v : ℝ)) * √(4 * (v : ℝ) - (x - μ) ^ 2)
      ↔ 0 < √(4 * (v : ℝ) - (x - μ) ^ 2) := by
    refine ⟨fun h => ?_, fun h => mul_pos hconst h⟩
    rcases (Real.sqrt_nonneg (4 * (v : ℝ) - (x - μ) ^ 2)).lt_or_eq with h' | h'
    · exact h'
    · rw [← h', mul_zero] at h; exact absurd h (lt_irrefl 0)
  rw [hmul, Real.sqrt_pos]
  constructor
  · intro h
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    nlinarith

@[measurability, fun_prop]
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

instance instIsProbabilityMeasuresemicircleReal (μ : ℝ) (v : ℝ≥0) :
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

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_add_const (y : ℝ) :
    (semicircleReal μ v).map (· + y) = semicircleReal (μ + y) v := by
  by_cases hv : v = 0
  · rw [hv, semicircleReal_zero_var, semicircleReal_zero_var]
    rw [Measure.map_dirac (measurable_id'.add_const y)]

  · apply Measure.ext
    intro s hs
    rw [semicircleReal_of_var_ne_zero μ hv, semicircleReal_of_var_ne_zero (μ + y) hv]
    --convert LHS and RHS to density
    rw [Measure.map_apply (measurable_add_const y) hs]
    rw [withDensity_apply' _]
    rw [withDensity_apply' _]

    --change of variables
    have h_change : ∫⁻ (a : ℝ) in (fun x ↦ x + y) ⁻¹' s, semicirclePDF μ v a =
                         ∫⁻ (u : ℝ) in s, semicirclePDF μ v (u - y) := by

      have h_meas : Measurable (fun x ↦ x + y) := measurable_add_const y

      have h1 : ∫⁻ (a : ℝ) in (fun x ↦ x + y) ⁻¹' s, semicirclePDF μ v a
      = ∫⁻ (a : ℝ) in (fun x ↦ x + y) ⁻¹' s, semicirclePDF μ v ((a + y) - y) := by
        apply lintegral_congr_ae
        filter_upwards [] with a
        ring_nf
      have h_comp : Measurable (fun u ↦ semicirclePDF μ v (u - y)) :=
              (measurable_semicirclePDF μ v).comp (measurable_sub_const y)
      rw [h1]
      -- this is the key lemma which helps us convert LHS
      rw [<- setLIntegral_map hs h_comp]
      rw [map_add_right_eq_self volume y]
      simp [h_meas]
    rw[h_change]
    apply lintegral_congr_ae
    filter_upwards [] with x
    -- the original semicirclePDFReal needs to be modified
    have semicirclePDFReal_sub_ENNReal {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
             ENNReal.ofReal (semicirclePDFReal μ v (x - y)) =
             ENNReal.ofReal (semicirclePDFReal (μ + y) v x) := by
      rw [semicirclePDFReal_sub x y]

    exact semicirclePDFReal_sub_ENNReal x y

/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_const_add (y : ℝ) :
    (semicircleReal μ v).map (y + ·) = semicircleReal (μ + y) v := by
  simp_rw [add_comm y]
  exact semicircleReal_map_add_const y

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_const_mul (c : ℝ) :
    (semicircleReal μ v).map (c * ·) = semicircleReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases hv : v = 0
  · rw [hv, semicircleReal_zero_var]
    simp [mul_zero]
    rw [Measure.map_dirac (measurable_const_mul c)]
  · apply Measure.ext
    intro s hs
    rw [semicircleReal_of_var_ne_zero μ hv]
    have h_nonzero : ⟨c^2, sq_nonneg _⟩ * v ≠ 0 := by
      rw [ne_eq, mul_eq_zero, not_or]
      constructor
      · intro h
        have h_sq : c^2 = 0 := by
          have : (⟨c^2, sq_nonneg _⟩ : ℝ≥0).val = 0 := by rw [h]; rfl
          exact this
        have h_c : c = 0 := by rwa [sq_eq_zero_iff] at h_sq
        exact hc h_c
      · exact hv
    rw [semicircleReal_of_var_ne_zero (c * μ) h_nonzero]
    rw [Measure.map_apply (measurable_const_mul c) hs]
    rw [withDensity_apply' _]
    rw [withDensity_apply' _]
    have h1 : ∫⁻ (a : ℝ) in (c * ·) ⁻¹' s, semicirclePDF μ v a
      = ∫⁻ (a : ℝ) in (c * ·) ⁻¹' s, semicirclePDF μ v (c⁻¹ * (c * a)) := by
        apply lintegral_congr_ae
        filter_upwards [] with a
        congr 1
        rw [← mul_assoc]
        symm
        have h_ne : c ≠ 0 := hc
        rw [inv_mul_cancel₀ h_ne]
        rw [one_mul]
    rw [h1]
    have h_map : ∫⁻ (a : ℝ) in (c * ·) ⁻¹' s, semicirclePDF μ v ((c⁻¹ * (c * a)))
                = ∫⁻ (u : ℝ) in s, (ENNReal.ofReal (|c|⁻¹)) * semicirclePDF μ v (c⁻¹ * u) := by
          have h_meas : Measurable (c * ·) := measurable_const_mul c
          have h_comp : Measurable (fun u ↦ semicirclePDF μ v (c⁻¹ * u)) := by
              apply Measurable.comp (measurable_semicirclePDF μ v) (measurable_const_mul (c⁻¹))
          rw [← setLIntegral_map hs h_comp]

          have h_volume : (volume : Measure ℝ).map (c * ·) = ENNReal.ofReal (|c|⁻¹) • volume := by
             ext t ht
             rw [Measure.map_apply (measurable_const_mul c) ht]
             rw [Measure.smul_apply]
             simp only [smul_eq_mul]
             rw [Real.volume_preimage_mul_left hc t]
             congr 1
             rw [abs_inv]

          rw [h_volume]
          rw [setLIntegral_smul_measure]
          rw [lintegral_const_mul]
          rw [ENNReal.ofReal]
          rfl
          exact h_comp
          exact h_meas
    rw [h_map]
    apply lintegral_congr_ae
    filter_upwards [] with a
    simp only [semicirclePDF]
    rw [<- ENNReal.ofReal_mul]
    · congr 1
      have hnc: |c|⁻¹ ≠  0 := by
         intro H
         exact hc (abs_eq_zero.1 (inv_eq_zero.1 H))
      rw[semicirclePDFReal_inv_mul hc]
      rw [← mul_assoc]
      have : |c|⁻¹ * |c| = 1 := inv_mul_cancel₀ (abs_ne_zero.2 hc)
      rw [this]
      rw [one_mul]
    exact inv_nonneg.2 (abs_nonneg c)

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_mul_const (c : ℝ) :
    (semicircleReal μ v).map (· * c) = semicircleReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact semicircleReal_map_const_mul c

lemma semicircleReal_map_neg : (semicircleReal μ v).map (fun x ↦ -x) = semicircleReal (-μ) v := by
  simpa using semicircleReal_map_const_mul (μ := μ) (v := v) (-1)

lemma semicircleReal_map_sub_const (y : ℝ) :
    (semicircleReal μ v).map (· - y) = semicircleReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, semicircleReal_map_add_const]

lemma semicircleReal_map_const_sub (y : ℝ) :
    (semicircleReal μ v).map (y - ·) = semicircleReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x ↦ y + -x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), semicircleReal_map_neg,
    semicircleReal_map_const_add, add_comm]

variable {Ω : Type} [MeasureSpace Ω]

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`X + y` has a semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_add_const {X : Ω → ℝ} (hX : Measure.map X ℙ = semicircleReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ X ω + y) ℙ = semicircleReal (μ + y) v := by
  have hXm : AEMeasurable X := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ ω + y) ∘ X) ℙ = semicircleReal (μ + y) v
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.add_const _).aemeasurable hXm, hX,
    semicircleReal_map_add_const y]

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`y + X` has a semicircular law with mean `μ + y` and variance `v`. -/
lemma semicircleReal_const_add {X : Ω → ℝ} (hX : Measure.map X ℙ = semicircleReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ y + X ω) ℙ = semicircleReal (μ + y) v := by
  simp_rw [add_comm y]
  exact semicircleReal_add_const hX y

/-- If `X` is a real random variable with semicircular law with mean `μ` and variance `v`, then
`c * X` has a semicircular law with mean `c * μ` and variance `c^2 * v`. -/
lemma semicircleReal_const_mul {X : Ω → ℝ} (hX : Measure.map X ℙ = semicircleReal μ v) (c : ℝ) :
    Measure.map (fun ω ↦ c * X ω) ℙ = semicircleReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  have hXm : AEMeasurable X := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ c * ω) ∘ X) ℙ = semicircleReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.const_mul c).aemeasurable hXm, hX]
  exact semicircleReal_map_const_mul c

/-- If `X` is a real random variable with semicircualr law with mean `μ` and variance `v`,
then `X * c` has a semicircular law with mean `c * μ` and variance `c^2 * v`. -/
lemma semicircleReal_mul_const {X : Ω → ℝ} (hX : Measure.map X ℙ = semicircleReal μ v) (c : ℝ) :
    Measure.map (fun ω ↦ X ω * c) ℙ = semicircleReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact semicircleReal_const_mul hX c

end Transformations

section Moments

variable {μ : ℝ} {v : ℝ≥0}

/-- The mean of a real semicircle distribution `semicircleReal μ v` is its mean parameter `μ`. -/
@[simp]
lemma integral_id_semicircleReal : ∫ x, x ∂semicircleReal μ v = μ := by
    by_cases hv : v = 0
    · simp [hv]
    rw [integral_semicircleReal_eq_integral_smul hv]
    have : (fun x => semicirclePDFReal μ v x • x) =
         (fun x => semicirclePDFReal μ v x * (x - μ + μ)) := by
        ext x
        simp [smul_eq_mul]
    rw [this]
    have : (fun x => semicirclePDFReal μ v x * (x - μ + μ)) =
         (fun x => semicirclePDFReal μ v x * (x - μ) + semicirclePDFReal μ v x * μ) := by
         ext x
         ring_nf
    rw [this]
    rw [integral_add]
    have h_symm : ∫ (a : ℝ), semicirclePDFReal μ v a * (a - μ) = 0 := by
       rw [semicirclePDFReal_def]
       have : ∫ (a : ℝ), (1 / (2 * π * ↑v) * √(4 * ↑v - (a - μ) ^ 2)) * (a - μ) =
         ∫ (y : ℝ), (1 / (2 * π * ↑v) * √(4 * ↑v - y ^ 2)) * y := by
           rw [ eq_comm, ← MeasureTheory.integral_sub_right_eq_self _ μ ]
       rw [this]
       have h_odd : ∀ y, (1 / (2 * π * ↑v) * √(4 * ↑v - (-y) ^ 2) * (-y)) =
                    -(1 / (2 * π * ↑v) * √(4 * ↑v - y ^ 2) * y) := by
            intro y
            ring_nf
       have h_neg : ∫ (y : ℝ), (1 / (2 * π * ↑v) * √(4 * ↑v - y ^ 2)) * y =
               ∫ (y : ℝ), (1 / (2 * π * ↑v) * √(4 * ↑v - (-y) ^ 2)) * (-y) := by
        /- By substituting $y$ with $-y$, we can show that the integral of the function over
        the entire real line is equal to the integral of its negative.-/
        have h_subst : ∀ {f : ℝ → ℝ}, (∫ y, f y) = (∫ y, f (-y)) := by
          intro f; rw [ ← MeasureTheory.integral_neg_eq_self ] ;
        rw [ h_subst ]
       simp only [h_odd] at h_neg
       rw [integral_neg] at h_neg
       linarith
    rw [h_symm, zero_add]
    have : (fun a => semicirclePDFReal μ v a * μ) = (fun a => μ * semicirclePDFReal μ v a) := by
       ext a; ring
    rw [this]
    rw [integral_const_mul]
    rw [integral_semicirclePDFReal_eq_one μ hv]
    ring_nf
    /- Since the semicircle PDF is continuous and compactly supported,
    the product with (x - μ) is also continuous and compactly supported, hence integrable.-/
    have h_cont_compact : Continuous (fun x => semicirclePDFReal μ v x * (x - μ)) ∧ ∃ C,
      ∀ x, abs (semicirclePDFReal μ v x * (x - μ)) ≤ C := by
      aesop
      generalize_proofs at *;
      · exact Continuous.mul
          ( ProbabilityTheory.Cont_semicirclePDFReal μ v ) ( continuous_id.sub continuous_const );
      · /- Since the semicircle PDF is continuous and compactly supported, the product with (x - μ)
         is also continuous and compactly supported, hence bounded.-/
        have h_cont_compact : ContinuousOn (fun x => semicirclePDFReal μ v x * (x - μ))
          (Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v)) := by
          exact Continuous.continuousOn ( by exact Continuous.mul ( by
            exact ProbabilityTheory.Cont_semicirclePDFReal μ v) (continuous_id.sub continuous_const));
        /- Since the function is continuous on a compact interval,
        it attains a maximum and minimum there.-/
        obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v),
          abs (semicirclePDFReal μ v x * (x - μ)) ≤ M := by
          /- By the Extreme Value Theorem, since the function is continuous on a compact interval,
          it attains a maximum and minimum on this interval.-/
          have h_extreme_value : ∃ M, ∀ x ∈ Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v),
              abs (semicirclePDFReal μ v x * (x - μ)) ≤ M := by
            have h_compact : IsCompact (Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v)) := by
              exact CompactIccSpace.isCompact_Icc
            exact IsCompact.exists_bound_of_continuousOn h_compact h_cont_compact |>
              fun ⟨ M, hM ⟩ => ⟨ M, fun x hx => hM x hx ⟩
          generalize_proofs at *;
          exact h_extreme_value;
        /- Since the semicircle PDF is zero outside the interval [μ - 2√v, μ + 2√v],
          the product with (x - μ) is also zero outside this interval. -/
        have h_zero_outside : ∀ x, x ∉ Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v)
         → semicirclePDFReal μ v x * (x - μ) = 0 := by
          intro x hx
          unfold ProbabilityTheory.semicirclePDFReal; aesop;
          apply Or.inl
          apply Real.sqrt_eq_zero_of_nonpos
          simp
          rw [imp_iff_not_or] at hx
          rcases hx with hx | hx
          · nlinarith [Real.sqrt_nonneg v, Real.sq_sqrt (NNReal.coe_nonneg v)]
          · nlinarith [Real.sqrt_nonneg v, Real.sq_sqrt (NNReal.coe_nonneg v)]
        simp_rw [← abs_mul]
        exact ⟨ Max.max M 0, fun x => if hx : x ∈ Set.Icc ( μ - 2 * Real.sqrt v ) ( μ + 2 * Real.sqrt v ) then  le_trans (hM x hx) ( le_max_left M 0 ) else by rw [ h_zero_outside x hx ] ; norm_num ⟩;
    have h_integrable : MeasureTheory.IntegrableOn (fun x => semicirclePDFReal μ v x * (x - μ)) (fun x => x ∈ Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v)) := by
      -- Since the function is continuous on a compact interval, it is integrable.
      have h_cont : ContinuousOn (fun x => semicirclePDFReal μ v x * (x - μ)) (Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v)) := by
        exact h_cont_compact.1.continuousOn;
      exact h_cont.integrableOn_Icc;
    convert h_integrable using 1;
    ext;
    rw [ MeasureTheory.integrableOn_iff_integrable_of_support_subset ];
    intro x hx; contrapose! hx; aesop;
    exact False.elim <| a <| by rw [ ProbabilityTheory.semicirclePDFReal ] ; exact mul_eq_zero_of_right _ <| Real.sqrt_eq_zero_of_nonpos <| le_of_not_gt fun h' => hx <| ⟨ by nlinarith [ Real.sqrt_nonneg v, Real.sq_sqrt <| show ( v : ℝ ) ≥ 0 by positivity ], by nlinarith [ Real.sqrt_nonneg v, Real.sq_sqrt <| show ( v : ℝ ) ≥ 0 by positivity ] ⟩ ;
    -- Since ProbabilityTheory.semicirclePDFReal μ v x is integrable, multiplying it by a constant μ preserves integrability.
    have h_integrable : MeasureTheory.Integrable (fun x => ProbabilityTheory.semicirclePDFReal μ v x) := by
      exact?;
    -- Since the semicircle PDF is integrable, multiplying it by a constant μ preserves integrability.
    apply MeasureTheory.Integrable.mul_const h_integrable μ

/-- The variance of a real semicircle distribution `semicircleReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_fun_id_semicircleReal : Var[fun x ↦ x; semicircleReal μ v] = v := by
  norm_num [ ProbabilityTheory.variance, ProbabilityTheory.evariance] at *;
  rw [ ProbabilityTheory.semicircleReal] ; aesop;
  have h_integral : ∫ x, (x - μ) ^ 2 * semicirclePDFReal μ v x = v := by
    --Rewrite the integral in terms of the semicircle PDF
    have h_integral' : ∫ x in Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v), (x - μ)^2 *
    (Real.sqrt (4 * v - (x - μ)^2)) = (v : ℝ) * (2 * Real.pi * v) := by
      --Suffices to calculate the integral by centering around 0 instead of μ
      suffices h_integral_simplified : ∫ x in Set.Icc (-2 * Real.sqrt v) (2 * Real.sqrt v),
      x^2 * Real.sqrt (4 * v - x^2) = (v : ℝ) * (2 * Real.pi * v) by
        rw [ ← h_integral_simplified, ← MeasureTheory.integral_indicator,
        ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
        rw [ ← MeasureTheory.integral_add_right_eq_self _ μ ] ; congr ; ext ; aesop;
        · exact Or.inr <| Real.sqrt_eq_zero_of_nonpos <| by
            contrapose! a; constructor <;>
            nlinarith [ Real.sqrt_nonneg v, Real.sq_sqrt <| show 0 ≤ ( v : ℝ ) by positivity];
        · exact absurd ( h_1 ( by linarith ) ) ( by linarith );
      -- Simplify the integral using the substitution $x = 2\sqrt{v} \sin \theta$.
      suffices h_integral_subst : ∫ θ in Set.Icc (-Real.pi / 2) (Real.pi / 2),
      (2 * Real.sqrt v * Real.sin θ)^2 * Real.sqrt (4 * v - (2 * Real.sqrt v * Real.sin θ)^2) *
      (2 * Real.sqrt v * Real.cos θ) = (v : ℝ) * (2 * Real.pi * v) by
        rw [ ← h_integral_subst, MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos, Real.sqrt_nonneg v ] ) ];
        rw [ MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos ] ) ];
        symm;
        convert intervalIntegral.integral_comp_mul_deriv _ _ _ using 2;
        any_goals intro x hx; exact HasDerivAt.const_mul ( 2 * Real.sqrt v) (Real.hasDerivAt_sin x);
        · rfl;
        · norm_num [ neg_div ];
        · norm_num;
        · exact Continuous.continuousOn ( by continuity );
        · continuity;
      -- Simplify the integrand using trigonometric identities, and show it equals 2*π*v.
      suffices h_integral_simplified : ∫ θ in Set.Icc (-Real.pi / 2) (Real.pi / 2),
      16 * v^2 * Real.sin θ^2 * Real.cos θ^2 = (v : ℝ) * (2 * Real.pi * v) by
        convert h_integral_simplified using 1;
        refine' MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => _ ; ring;
        norm_num [ Real.sin_sq, h ] ; ring;
        rw [ Real.sqrt_mul <| by positivity, Real.sqrt_mul <| by positivity ] ; ring;
        rw [ show ( Real.sqrt v ) ^ 4 = ( Real.sqrt v ^ 2 ) ^ 2 by
          ring, Real.sq_sqrt <| by positivity ];
          rw[Real.sqrt_sq <| Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos, hx.1 ], hx.2 ⟩];
          ring;
      rw [ MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ( by linarith [ Real.pi_pos ] ) ] ;
      norm_num [ mul_assoc, neg_div ] ; ring;
      norm_num [ mul_two ];
    /- Use the above simplifications to deduce that the integral of $(x - \mu)^2$ over the
    semicircle distribution is $v$ to conclude the proof. -/
    have h_final : ∫ x, (x - μ)^2 * (semicirclePDFReal μ v x) =
    (∫ x in Set.Icc (μ - 2 * Real.sqrt v) (μ + 2 * Real.sqrt v),
    (x - μ)^2 * (Real.sqrt (4 * v - (x - μ)^2))) / (2 * Real.pi * v) := by
      rw [ ← MeasureTheory.integral_indicator ] <;> norm_num [ Set.indicator ];
      rw [ ← MeasureTheory.integral_div ] ; congr ; ext x ; aesop;
      · unfold ProbabilityTheory.semicirclePDFReal; ring;
      · contrapose! h_1;
        constructor <;> contrapose! h_1 <;> unfold ProbabilityTheory.semicirclePDFReal at * <;>
        aesop;
        · rw [ Real.sqrt_eq_zero_of_nonpos ( by
            nlinarith [ Real.sqrt_nonneg v,
            Real.mul_self_sqrt ( show 0 ≤ ( v : ℝ ) by positivity ) ] ) ];
        · rw [ Real.sqrt_eq_zero_of_nonpos ( by
            nlinarith [ Real.sqrt_nonneg v,
            Real.mul_self_sqrt ( show 0 ≤ ( v : ℝ ) by positivity ) ] ) ];
    rw [ h_final, h_integral', mul_div_cancel_right₀ _ ( by positivity ) ];
  convert h_integral using 1;
  /-Show equivalence of (∫⁻ (ω : ℝ), ‖ω - μ‖ₑ ^ 2 ∂ℙ.withDensity (semicirclePDF μ v)).toReal
  = ∫ (x : ℝ), (x - μ) ^ 2 * semicirclePDFReal μ v x via measure theory lemmas-/
  rw [ MeasureTheory.integral_eq_lintegral_of_nonneg_ae ];
  · rw [ MeasureTheory.lintegral_withDensity_eq_lintegral_mul ];
    · norm_num [ mul_comm, ProbabilityTheory.semicirclePDF ];
      congr! 2;
      ext; rw [ ENNReal.ofReal_mul ( sq_nonneg _ ) ] ;
      norm_num [ ← ENNReal.ofReal_pow, Real.enorm_eq_ofReal_abs ];
    · exact Measurable.ennreal_ofReal ( ProbabilityTheory.measurable_semicirclePDFReal μ v );
    · fun_prop;
  · exact Filter.Eventually.of_forall fun x =>
      mul_nonneg ( sq_nonneg _ ) ( ProbabilityTheory.semicirclePDFReal_nonneg _ _ _ );
  · exact Continuous.aestronglyMeasurable ( by
      exact Continuous.mul ( by continuity ) ( by
       exact ProbabilityTheory.Cont_semicirclePDFReal μ v ) )

/-- The variance of a real semicircle distribution `semicircleReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_id_semicircleReal : Var[id; semicircleReal μ v] = v :=
  variance_fun_id_semicircleReal

/-- All the moments of a real semicircle distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_semicircleReal (p : ℝ≥0) : MemLp id p (semicircleReal μ v) := by
  -- The semicircle distribution is in L∞
  have h_L_infty : MeasureTheory.MemLp (fun x => x) ⊤ (ProbabilityTheory.semicircleReal μ v) := by
   -- The semicircle distribution is compactly supported.
    have h_compact_support : ∃ M : ℝ, ∀ x ∈ Function.support (semicirclePDF μ v), |x| ≤ M := by
      by_cases hv : v = 0;
      · aesop;
      · have := ProbabilityTheory.support_semicirclePDF ( μ := μ ) ( hv := hv );
        exact ⟨ |μ| + 2 * Real.sqrt v, fun x hx => abs_le.mpr ⟨ by
           cases abs_cases μ <;> linarith [ Set.mem_Ioo.mp ( this ▸ hx ) ], by
             cases abs_cases μ <;> linarith [ Set.mem_Ioo.mp ( this ▸ hx ) ] ⟩ ⟩;
    -- Since the semicircle distribution is compactly supported, the identity is bounded ae.
    have h_bounded : ∃ M : ℝ, ∀ᵐ x ∂ProbabilityTheory.semicircleReal μ v, |x| ≤ M := by
      unfold ProbabilityTheory.semicircleReal; aesop;
      · exact ⟨ _, le_rfl ⟩;
      · use w; rw [ MeasureTheory.ae_withDensity_iff ]; aesop;
        exact measurable_semicirclePDF μ v;
    -- Since the identity function is bounded by M almost everywhere, it is in L^∞.
    refine' ⟨ _, _ ⟩;
    · fun_prop;
    · refine' lt_of_le_of_lt ( csInf_le _ _ ) _ <;> norm_num;
      exact ENNReal.ofReal ( h_bounded.choose );
      · filter_upwards [ h_bounded.choose_spec ] with x hx using by
         simpa only [ Real.enorm_eq_ofReal_abs ] using ENNReal.ofReal_le_ofReal hx;
      · exact ENNReal.ofReal_lt_top;
  exact h_L_infty.mono_exponent ( by simp +decide );

/-- All the moments of a real semicircle distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_semicircleReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (semicircleReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_semicircleReal p


/- Setup lemmas for lemma centralMoment_fun_two_mul_semicircleReal -/
noncomputable def w (k : ℕ) : ℝ := ((2 : ℝ) * (k : ℝ) + 1) / ((2 : ℝ) * ((k : ℝ) + 1))

lemma integral_cos_pow_even (n : ℕ) : (∫ x in 0..π, Real.cos x ^ (2 * n))
    = π * ∏ k ∈ Finset.range n, ((2 * k + 1) : ℝ) / (2 * (k + 1)) := by
  induction n
  case zero =>
    dsimp
    have c0 : ∫ (x : ℝ) in 0..π, Real.cos x ^ 0 = π := by simp
    simp
  case succ n ih =>
    have c1 : ∀ (m : ℕ),
    ∫ (x : ℝ) in 0..π, Real.cos x ^ (m + 2) =
    (Real.cos π ^ (m + 1) * Real.sin π - Real.cos 0 ^ (m + 1) * Real.sin 0 +
    (m + 1) * ∫ (x : ℝ) in 0..π, Real.cos x ^ m) -
    (m + 1) * ∫ (x : ℝ) in 0..π, Real.cos x ^ (m + 2) := by
      apply integral_cos_pow_aux (a := 0) (b := π)
    simp at c1
    set A := ∫ (x : ℝ) in 0..π, Real.cos x ^ (2 * n + 2)
    set B := ∫ (x : ℝ) in 0..π, Real.cos x ^ (2 * n)
    have c2 : A = (2 * n + 1) * B - (2 * n + 1) * A := by
      dsimp [A, B]
      have c21:= c1 (2 * n)
      have c22 : ((2 * n) : ℝ) = (2 : ℝ) * (n : ℝ) := by grind
      simpa [c22, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
         two_mul, add_comm, add_left_comm, add_assoc,
         mul_comm, mul_left_comm, mul_assoc] using c21
    have c3 : ((2 * n + 2) : ℝ) * A = ((2 * n + 1) : ℝ) * B := by grind
    set C := ((2 * n + 2) : ℝ)
    set D := ((2 * n + 1) : ℝ)
    have c4 : A = D / C * B := by
      have c41 : C⁻¹ * (C * A) = C⁻¹ * (D * B) := by
        exact congrArg (HMul.hMul C⁻¹) c3
      have c42 : (C⁻¹ * C) * A = (C⁻¹ * D) * B := by
        rw [mul_assoc, mul_assoc]; exact c41
      have c43 : C⁻¹ * C = 1 := by
        dsimp [C]; refine inv_mul_cancel₀ ?_; positivity
      rw [c43] at c42
      simp at c42
      have c44 : (C⁻¹ * D) * B = D / C * B := by grind
      rw [← c44]; exact c42
    dsimp [A, B] at c4
    have c5 : ∫ (x : ℝ) in 0..π, Real.cos x ^ (2 * (n + 1))
      = (2 * n + 1) / (2 * n + 2) * ∫ (x : ℝ) in 0..π, Real.cos x ^ (2 * n) := by
      dsimp [C,D] at c4; exact c4
    have c6 :π * ∏ k ∈ Finset.range (n + 1), w k
    = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) * π * ∏ k ∈ Finset.range n, w k := by
      have := Finset.prod_range_succ (f := fun k ↦ w k) n
      calc
        π * ∏ k ∈ Finset.range (n + 1), w k
        = π * ((∏ k ∈ Finset.range n, w k) * w n) := by grind
      _ = π * (∏ k ∈ Finset.range n, w k) * w n := by ring_nf
      _ = ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2))
            * (π * ∏ k ∈ Finset.range n, w k) := by
              rw [mul_comm]; dsimp [w]; grind
      _ = (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)
            * π * ∏ k ∈ Finset.range n, w k := by ring_nf
    rw [c5]; dsimp [B] at ih; rw [ih]; dsimp [w] at c6; rw [c6]
    grind

lemma measurable_ofNNReal : Measurable (ENNReal.ofNNReal) := by
  have h1 : Measurable fun (x : ℝ≥0) ↦ (x : ℝ) := measurable_subtype_coe
  have h2 : Measurable fun (x : ℝ) ↦ ENNReal.ofReal x := ENNReal.measurable_ofReal
  have h3 : Measurable fun (x : ℝ≥0) ↦ ENNReal.ofReal (x : ℝ) := h2.comp h1
  simpa [ENNReal.ofReal_coe_nnreal] using h3

@[simp]
lemma semicirclePDF_toReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) (h₀ : 0 ≤ semicirclePDFReal μ v x) :
  (ENNReal.ofReal (semicirclePDFReal μ v x)).toReal = semicirclePDFReal μ v x := by
  exact ENNReal.toReal_ofReal h₀

lemma prod_two_mul_factorial (n : ℕ) : ∏ x ∈ Finset.range n, (2 : ℝ) * (↑x + 1)
  = 2 ^ n * (↑n.factorial : ℝ) := by
  induction' n with n ih
  · simp
  · have h : ∏ x ∈ Finset.range (n + 1), (2 : ℝ) * (↑x + 1)
    = (∏ x ∈ Finset.range n, (2 : ℝ) * (↑x + 1)) * ((2 : ℝ) * (↑n + 1)) := by
      exact Finset.prod_range_succ (fun x : ℕ => (2 : ℝ) * (↑x + 1)) n
    have h' : ∏ x ∈ Finset.range (n + 1), (2 : ℝ) * (↑x + 1)
    = 2 ^ (n + 1) * (↑(Nat.factorial (n + 1)) : ℝ) := by
      calc
        ∏ x ∈ Finset.range (n + 1), (2 : ℝ) * (↑x + 1)
          = (∏ x ∈ Finset.range n, (2 : ℝ) * (↑x + 1)) * ((2 : ℝ) * (↑n + 1)) := h
        _ = (2 ^ n * (↑(Nat.factorial n) : ℝ)) * ((2 : ℝ) * (↑n + 1)) := by simp [ih]
        _ = 2 ^ (n + 1) * (↑(Nat.factorial (n + 1)) : ℝ) := by
          simp [pow_succ, Nat.factorial_succ, mul_comm, mul_left_comm,
                mul_assoc, Nat.cast_mul, Nat.cast_add]
    simpa [Nat.succ_eq_add_one] using h'

lemma prod_odd_over_even_central_choose (n : ℕ) :
  (∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1)) /
    (∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1))) =
    (Nat.choose (2 * n) n : ℝ) / 2 ^ (2 * n) := by
  let P_odd := ∏ x ∈ Finset.range n, (2 * (x : ℝ) + 1)
  let P_even := ∏ x ∈ Finset.range n, (2 * ((x : ℝ) + 1))
  have h_P_even : P_even = (2 : ℝ) ^ n * (Nat.factorial n : ℝ) := by
    unfold P_even
    rw [prod_two_mul_factorial]
  have h_prod_all : P_odd * P_even = (Nat.factorial (2 * n) : ℝ) := by
    have h_nat_prod_id : ∀ k, ∏ i ∈ Finset.range k, ((2 * i + 1) * (2 * i + 2))
      = Nat.factorial (2 * k) := by
      intro k
      induction k with
      | zero => simp
      | succ k IH =>
        rw [Finset.prod_range_succ, IH]
        rw [show Nat.factorial (2 * (k + 1)) = Nat.factorial (2 * k + 2) by ring_nf]
        rw [Nat.factorial_succ, Nat.factorial_succ]
        ring
    unfold P_odd P_even
    rw [← Finset.prod_mul_distrib]
    conv_lhs => arg 2; ext x; rw [show (2 * (x : ℝ) + 1) * (2 * ((x : ℝ) + 1))
      = ((2 * x + 1) * (2 * x + 2) : ℝ) by ring]
    rw [show ∏ x ∈ Finset.range n, ((2 * x + 1) * (2 * x + 2) : ℝ)
      = (∏ x ∈ Finset.range n, (2 * x + 1) * (2 * x + 2) : ℕ) by simp [Nat.cast_prod]]
    rw [h_nat_prod_id]
  have h_P_even_ne_zero : P_even ≠ 0 := by
    rw [h_P_even]
    apply mul_ne_zero
    exact pow_ne_zero _ two_ne_zero
    simp [Nat.factorial_ne_zero]
  calc
    P_odd / P_even
    _ = (↑(Nat.factorial (2 * n)) / P_even) / P_even := by field_simp; grind
    _ = ↑(Nat.factorial (2 * n)) / (P_even * P_even) := by rw [div_div]
    _ = ↑(Nat.factorial (2 * n))
      / (((2 : ℝ) ^ n * ↑(Nat.factorial n)) ^ 2) := by rw [h_P_even]; ring
    _ = ↑(Nat.factorial (2 * n))
      / (2 ^ (2 * n) * (↑(Nat.factorial n)) ^ 2) := by rw [mul_pow, ← pow_mul, mul_comm n 2]
    _ = (↑(Nat.choose (2 * n) n)) / 2 ^ (2 * n) := by
      rw [show (Nat.choose (2 * n) n : ℝ)
        = (2 * n).factorial / (n.factorial * n.factorial) by
        rw [Nat.choose_eq_factorial_div_factorial (by grind : n ≤ 2 * n)]
        rw [show 2 * n - n = n by grind]
        norm_cast
        have : n.factorial * n.factorial ∣ (2 * n).factorial := by
          convert Nat.factorial_mul_factorial_dvd_factorial (by grind : n ≤ 2 * n)
          grind
        rw [Nat.cast_div this]
        simp [Nat.factorial_ne_zero]]
      ring

/-- The integral `∫_0^π cos^(2m)` expressed with the central binomial coefficient. -/
lemma integral_cos_pow_even_centralBinom (m : ℕ) :
    (∫ x in (0:ℝ)..π, Real.cos x ^ (2 * m)) = π * (Nat.centralBinom m) / 4 ^ m := by
  rw [integral_cos_pow_even m]
  have h := prod_odd_over_even_central_choose m
  have h2 : (∏ x ∈ Finset.range m, (2 * ((x : ℝ) + 1))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ ↦ by positivity
  rw [div_eq_div_iff h2 (by positivity)] at h
  rw [show ∏ k ∈ Finset.range m, ((2 * (k : ℝ) + 1)) / (2 * ((k : ℝ) + 1))
      = (∏ k ∈ Finset.range m, (2 * (k : ℝ) + 1)) / ∏ k ∈ Finset.range m, (2 * ((k : ℝ) + 1)) by
    rw [Finset.prod_div_distrib], Nat.centralBinom]
  field_simp
  rw [show ((4 : ℝ)) ^ m = 2 ^ (2 * m) by rw [pow_mul]; norm_num]
  linarith [h]

/-- `4 * C(2n, n) - C(2n + 2, n + 1)` is twice the `n`-th Catalan number. -/
lemma four_mul_centralBinom_sub_centralBinom_succ (n : ℕ) :
    4 * (Nat.centralBinom n : ℝ) - (Nat.centralBinom (n + 1) : ℝ) = 2 * catalan n := by
  have h1 : ((n : ℝ) + 1) * catalan n = Nat.centralBinom n := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (succ_mul_catalan_eq_centralBinom n)
  have h2 : ((n : ℝ) + 1) * Nat.centralBinom (n + 1) = 2 * (2 * n + 1) * Nat.centralBinom n := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (Nat.succ_mul_centralBinom_succ n)
  refine mul_left_cancel₀ (show ((n : ℝ) + 1) ≠ 0 by positivity) ?_
  linear_combination -h2 - 2 * h1

/-- The even moments of the unit semicircle profile `√(1 - t²)` on `[-1, 1]`: substituting
`t = cos θ` turns the integral into `∫_0^π cos^(2n) θ sin² θ dθ`. -/
lemma integral_pow_mul_sqrt_one_sub_sq (n : ℕ) :
    (∫ t in (-1:ℝ)..1, t ^ (2 * n) * √(1 - t ^ 2)) = π * catalan n / (2 * 4 ^ n) := by
  have hsub := intervalIntegral.integral_comp_smul_deriv (a := π) (b := 0)
    (f := Real.cos) (f' := fun x ↦ -Real.sin x) (g := fun t : ℝ ↦ t ^ (2 * n) * √(1 - t ^ 2))
    (fun x _ ↦ Real.hasDerivAt_cos x) (by fun_prop) (by fun_prop)
  simp only [Real.cos_pi, Real.cos_zero, Function.comp] at hsub
  rw [← hsub, intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
  have key : ∫ x in (0:ℝ)..π, -(-Real.sin x • (Real.cos x ^ (2 * n) * √(1 - Real.cos x ^ 2)))
      = ∫ x in (0:ℝ)..π, (Real.cos x ^ (2 * n) - Real.cos x ^ (2 * (n + 1))) := by
    refine intervalIntegral.integral_congr fun x hx ↦ ?_
    rw [uIcc_of_le Real.pi_pos.le] at hx
    rw [show √(1 - Real.cos x ^ 2) = Real.sin x by
      rw [← Real.sin_sq x, Real.sqrt_sq (Real.sin_nonneg_of_mem_Icc hx)], smul_eq_mul]
    linear_combination (Real.cos x ^ (2 * n)) * Real.sin_sq x
  rw [key, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun x : ℝ ↦ Real.cos x ^ (2 * n)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun x : ℝ ↦ Real.cos x ^ (2 * (n + 1))).intervalIntegrable _ _),
    integral_cos_pow_even_centralBinom n, integral_cos_pow_even_centralBinom (n + 1)]
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  linear_combination (2 * 4 ^ n : ℝ) * four_mul_centralBinom_sub_centralBinom_succ n

/-- The same integral over the whole line: the integrand vanishes outside `[-1, 1]`. -/
lemma integral_pow_mul_sqrt_one_sub_sq_real (n : ℕ) :
    (∫ t : ℝ, t ^ (2 * n) * √(1 - t ^ 2)) = π * catalan n / (2 * 4 ^ n) := by
  rw [← integral_pow_mul_sqrt_one_sub_sq n,
    intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro x hx
  simp only [mem_Ioc, not_and_or, not_lt, not_le] at hx
  rw [Real.sqrt_eq_zero_of_nonpos (by rcases hx with h | h <;> nlinarith), mul_zero]

lemma centralMoment_fun_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) (2 * n) (semicircleReal μ v) = v ^ n * catalan n := by
  by_cases hv : v = 0
  · subst hv
    cases n <;> simp [centralMoment]
  have hv0 : (0 : ℝ) < v := lt_of_le_of_ne v.coe_nonneg (by simpa [eq_comm] using hv)
  have hsq : √(v : ℝ) ^ 2 = v := Real.sq_sqrt hv0.le
  simp only [centralMoment, integral_id_semicircleReal, Pi.pow_apply, Pi.sub_apply]
  rw [integral_semicircleReal_eq_integral_smul hv]
  simp only [smul_eq_mul, semicirclePDFReal, mul_assoc, integral_const_mul]
  -- rescaling by `2√v` reduces the integral to the unit semicircle profile
  have h4 : ∀ y : ℝ, √(4 * (v : ℝ) - (2 * √(v : ℝ) * y) ^ 2) * (2 * √(v : ℝ) * y) ^ (2 * n)
      = 2 * √(v : ℝ) * (4 * (v : ℝ)) ^ n * (y ^ (2 * n) * √(1 - y ^ 2)) := by
    intro y
    have hpow : (2 * √(v : ℝ) * y) ^ (2 * n) = (4 * (v : ℝ)) ^ n * y ^ (2 * n) := by
      rw [mul_pow, pow_mul, show (2 * √(v : ℝ)) ^ 2 = 4 * (v : ℝ) by linear_combination 4 * hsq]
    rw [hpow, show 4 * (v : ℝ) - (2 * √(v : ℝ) * y) ^ 2 = (2 * √(v : ℝ)) ^ 2 * (1 - y ^ 2) by
      linear_combination (-4 : ℝ) * hsq, Real.sqrt_mul (by positivity),
      Real.sqrt_sq (by positivity)]
    ring
  have h3 := Measure.integral_comp_mul_left
    (fun u : ℝ ↦ √(4 * (v : ℝ) - u ^ 2) * u ^ (2 * n)) (2 * √(v : ℝ))
  simp only [h4, integral_const_mul, integral_pow_mul_sqrt_one_sub_sq_real, smul_eq_mul,
    abs_of_pos (show (0 : ℝ) < (2 * √(v : ℝ))⁻¹ by positivity)] at h3
  rw [integral_sub_right_eq_self (fun u : ℝ ↦ √(4 * (v : ℝ) - u ^ 2) * u ^ (2 * n)) μ]
  have h5 : ∫ y : ℝ, √(4 * (v : ℝ) - y ^ 2) * y ^ (2 * n)
      = 2 * √(v : ℝ) * (2 * √(v : ℝ) * (4 * (v : ℝ)) ^ n * (π * catalan n / (2 * 4 ^ n))) := by
    field_simp at h3 ⊢
    linarith [h3]
  rw [h5, show (4 * (v : ℝ)) ^ n = 4 ^ n * (v : ℝ) ^ n by rw [mul_pow]]
  have h4n : (4 : ℝ) ^ n ≠ 0 := by positivity
  field_simp
  linear_combination (catalan n : ℝ) * hsq

lemma centralMoment_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (semicircleReal μ v)
    = v ^ n * catalan n := by
  unfold id; apply centralMoment_fun_two_mul_semicircleReal

lemma centralMoment_fun_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) ((2 * n) + 1) (semicircleReal μ v)
    = 0 := by
    by_cases hv : v = 0;
    · simp +decide [ hv, ProbabilityTheory.centralMoment, ProbabilityTheory.semicircleReal ];
    · -- Use the substitution $u = x - \mu$ to transform the integral.
      have h_subst : ∫ x, (x - μ) ^ (2 * n + 1) * semicirclePDFReal μ v x =
        ∫ u, u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ) := by
        rw [ ← MeasureTheory.integral_add_right_eq_self _ μ ] ; congr ; ext ; ring;
      -- Use the fact that the integral of an odd function over the entire real line is zero.
      have h_odd_integral : ∫ u, u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ) =
        ∫ u, -u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ) := by
        rw [ ← MeasureTheory.integral_neg_eq_self ] ; congr ; ext ; ring_nf;
        simp +decide [ ProbabilityTheory.semicirclePDFReal ];
      have h_zero : ∫ u, u ^ (2 * n + 1) * semicirclePDFReal μ v (u + μ) = 0 := by
        norm_num [ MeasureTheory.integral_neg ] at * ; linarith;
      convert h_zero using 1;
      rw [ ← h_subst, ProbabilityTheory.centralMoment ];
      rw [ integral_semicircleReal_eq_integral_smul ] ; aesop;
      · simpa only [ mul_comm ] using h_subst;
      · assumption

lemma centralMoment_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id ((2 * n) + 1) (semicircleReal μ v)
    = 0 := by
  unfold id; apply centralMoment_fun_odd_semicircleReal

end Moments

lemma catalan_recur (n : ℕ): (n + 2) * catalan (n + 1) = (4 * n + 2) * (catalan n) := by
  -- By definition of Catalan numbers, we know that $C_n = \frac{1}{n+1} \binom{2n}{n}$.
  have h_catalan_def : ∀ n, catalan n = Nat.centralBinom n / (n + 1) := by
    norm_num [ Nat.centralBinom, catalan_eq_centralBinom_div ];
  norm_num [ h_catalan_def, Nat.centralBinom ];
  rw [ ← Nat.mul_div_assoc, ← Nat.mul_div_assoc ];
  · rw [ show 2 * ( n + 1 ) = 2 * n + 2 by ring ];
    rw [ show 2 * n + 2 = 2 * n + 1 + 1 by ring, Nat.choose_succ_succ ];
    rw [ Nat.succ_eq_add_one, Nat.choose_symm_of_eq_add ] <;> simp +arith +decide;
    exact Eq.symm ( Nat.div_eq_of_eq_mul_left ( Nat.succ_pos _ ) ( by nlinarith [ Nat.succ_mul_choose_eq ( 2 * n ) n, Nat.succ_mul_choose_eq ( 2 * n + 1 ) ( n + 1 ) ] ) );
  · have h := Nat.succ_mul_choose_eq ( 2 * n ) n;
    rw [ Nat.choose_succ_succ ] at h;
    exact ⟨ Nat.choose ( 2 * n ) n - Nat.choose ( 2 * n ) ( n + 1 ), by rw [ Nat.mul_sub_left_distrib, eq_tsub_iff_add_eq_of_le ] <;> nlinarith ⟩;
  · have h := Nat.succ_mul_choose_eq ( 2 * ( n + 1 ) ) ( n + 1 );
    exact Nat.Coprime.dvd_of_dvd_mul_left ( by norm_num [ ( by ring : 2 * ( n + 1 ) + 1 = n + 1 + 1 + ( n + 1 ) ) ] ) ( h.symm ▸ dvd_mul_left _ _ )

end SemicircleDistribution

end ProbabilityTheory
