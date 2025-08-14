/-Default imports-/
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Hammer

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

/-- The semicircle pdf is integrable. -/
@[fun_prop]
lemma integrable_semicirclePDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (semicirclePDFReal μ v) := by
  rw [semicirclePDFReal_def]
  set f := fun x ↦ 1 / (2 * π * v) * √(4 * v - (x - μ) ^ 2)
  have h1 : Continuous f := by apply Cont_semicirclePDFReal
  set I := uIcc (μ + √v) (μ - √v) with hI
  have h2 : IsCompact I := by simpa [hI] using isCompact_uIcc
  have h3 : IntegrableOn f I := by simpa using (h1.continuousOn).integrableOn_compact h2
  have h4 : IntegrableOn f Iᶜ := by sorry
  have h : IntegrableOn f (I ∪ Iᶜ) := IntegrableOn.union h3 h4
  have h' : I ∪ Iᶜ = Set.univ := Set.union_compl_self I
  rw [h'] at h
  rw [← integrableOn_univ]; exact h


/-- The semicircle distribution pdf integrates to 1 when the variance is not zero. -/
lemma lintegral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (semicirclePDFReal μ v x) = 1 := by
  sorry

/-- The semicircle distribution pdf integrates to 1 when the variance is not zero. -/
lemma integral_semicirclePDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, semicirclePDFReal μ v x = 1 := by
  sorry

lemma semicirclePDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x - y) = semicirclePDFReal (μ + y) v x := by
  simp only [semicirclePDFReal]
  rw [sub_add_eq_sub_sub_swap]

lemma semicirclePDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    semicirclePDFReal μ v (x + y) = semicirclePDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← semicirclePDFReal_sub, sub_eq_add_neg, neg_neg]

lemma semicirclePDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    semicirclePDFReal μ v (c⁻¹ * x) = |c| * semicirclePDFReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) x := by
  sorry

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
  sorry

lemma semicirclePDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x < ∞ := by
simp [semicirclePDF]

lemma semicirclePDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : semicirclePDF μ v x ≠ ∞ := by
simp [semicirclePDF]

/-- The support of the semicircle pdf with mean μ and variance v is [μ - √ v, μ + √ v]
Need to set the interval correctly in the statement of the lemma-/
@[simp]
lemma support_semicirclePDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Function.support (semicirclePDF μ v) = Set.univ := by
  sorry

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
  sorry


/-- The map of a semicircle distribution by addition of a constant is semicircular. -/
lemma semicircleReal_map_const_add (y : ℝ) :
    (semicircleReal μ v).map (y + ·) = semicircleReal (μ + y) v := by
  simp_rw [add_comm y]
  exact semicircleReal_map_add_const y

/-- The map of a semicircle distribution by multiplication by a constant is semicircular. -/
lemma semicircleReal_map_const_mul (c : ℝ) :
    (semicircleReal μ v).map (c * ·) = semicircleReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  sorry

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
  sorry

/-- The variance of a real semicircle distribution `semicircleReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_fun_id_semicircleReal : Var[fun x ↦ x; semicircleReal μ v] = v := by
  sorry

/-- The variance of a real semicircle distribution `semicircleReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_id_semicircleReal : Var[id; semicircleReal μ v] = v :=
  variance_fun_id_semicircleReal

/-- All the moments of a real semicircle distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_semicircleReal (p : ℝ≥0) : MemLp id p (semicircleReal μ v) :=
  sorry

/-- All the moments of a real semicircle distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_semicircleReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (semicircleReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_semicircleReal p

lemma centralMoment_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id (2 * n) (semicircleReal μ v)
    = v ^ n * catalan n := by
  sorry

lemma centralMoment_fun_two_mul_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) (2 * n) (semicircleReal μ v)
    = v ^ n * catalan n :=
  sorry

lemma centralMoment_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment id ((2 * n) + 1) (semicircleReal μ v)
    = 0 := by
  sorry

lemma centralMoment_fun_odd_semicircleReal (μ : ℝ) (v : ℝ≥0) (n : ℕ) :
    centralMoment (fun x ↦ x) ((2 * n) + 1) (semicircleReal μ v)
    = 0 :=
  sorry


end Moments

section Scribbles

def f (_ : ℝ) : ℝ := 1

def g (x : ℝ) : ℝ := x

def h (x : ℝ) : ℝ := x^2 - 1

lemma g_cont : Continuous g := by
  unfold g
  continuity

lemma h_cont : Continuous h := by
  unfold h
  continuity

end Scribbles

end SemicircleDistribution

end ProbabilityTheory
