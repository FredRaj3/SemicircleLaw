import SemicircleLaw.Experiments.WignerMatrix
import SemicircleLaw.SemicircleDistribution.SemicircleDistribution
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Wigner's semicircle law for matrix moments (Kemp, Theorem 2.4)

Let `𝐗ₙ = (1/√n) 𝐘ₙ` be a sequence of Wigner matrices with `𝔼(Y_{ij}) = 0`, `𝔼(Y₁₂²) = t`
and all moments of `Y₁₁`, `Y₁₂` finite. For each fixed `k`, the random variable
`w ↦ (1/n) Tr(𝐗ₙ(w)ᵏ)` converges in probability to `∫ xᵏ dσ_t` as `n → ∞`.

We first check that `w ↦ (1/n) Tr(𝐗ₙ(w)ᵏ)` is indeed a random variable (a measurable map
`Ω → ℝ`): the entries of `𝐗ₙ(w)ᵏ` are polynomials in the entries of `𝐗ₙ(w)`.
-/

open MeasureTheory Filter Topology RandomMatrixTheory ProbabilityTheory
open scoped NNReal

namespace RandomMatrix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The normalized trace moment `w ↦ (1/n) Tr(X(w)ᵏ)` of an `n × n` random matrix `X`. -/
noncomputable def traceMoment {n : ℕ} (X : Ω → Matrix (Fin n) (Fin n) ℝ) (k : ℕ) : Ω → ℝ :=
  fun w => (n : ℝ)⁻¹ * (X w ^ k).trace

/-- Powers of a random matrix are random matrices: every entry of `w ↦ X(w)ᵏ` is measurable. -/
theorem IsRandomMatrix.pow {n : ℕ} {X : Ω → Matrix (Fin n) (Fin n) ℝ} (hX : IsRandomMatrix X)
    (k : ℕ) : IsRandomMatrix (fun w => X w ^ k) := by
  induction k with
  | zero =>
    intro i j
    simp only [pow_zero]
    exact measurable_const
  | succ k ih =>
    intro i j
    simp only [pow_succ, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun l _ => (ih i l).mul (hX l j)

/-- `w ↦ (1/n) Tr(X(w)ᵏ)` is a real random variable whenever `X` is a random matrix. -/
theorem IsRandomMatrix.measurable_traceMoment {n : ℕ} {X : Ω → Matrix (Fin n) (Fin n) ℝ}
    (hX : IsRandomMatrix X) (k : ℕ) : Measurable (traceMoment X k) := by
  unfold traceMoment Matrix.trace Matrix.diag
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ => IsRandomMatrix.pow hX k i i)

/-- For a sequence of Wigner matrices, each `w ↦ (1/n) Tr(𝐗ₙ(w)ᵏ)` is a random variable. -/
theorem IsWignerMatrixSeq.measurable_traceMoment {P : Measure Ω} [IsProbabilityMeasure P]
    {X : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ} (hX : IsWignerMatrixSeq P X) (n k : ℕ) :
    Measurable (traceMoment (X n) k) :=
  IsRandomMatrix.measurable_traceMoment (hX.isRandomMatrix_isSymm n).1 k

/-- **Wigner's semicircle law for matrix moments** Let `𝐗ₙ = (1/√n) 𝐘ₙ`
be a sequence of Wigner matrices on `(Ω, 𝓕, ℙ)`, built from a Wigner family
`{Y_{ij}}_{1 ≤ i ≤ j}` with
* `𝔼(Y_{ij}) = 0` for all `1 ≤ i ≤ j`,
* `𝔼(Y₁₂²) = t`,
* `𝔼(|Y₁₁|ᵏ) < ∞` and `𝔼(|Y₁₂|ᵏ) < ∞` for all `k ≥ 1`.

Then for every fixed `k ∈ ℕ`, the random variables `w ↦ (1/n) Tr(𝐗ₙ(w)ᵏ)` converge in
probability (`TendstoInMeasure`) to the constant `∫ xᵏ dσ_t`, where `σ_t = semicircleReal 0 t`:
for every `ε > 0`, `ℙ(|(1/n) Tr(𝐗ₙ(w)ᵏ) - ∫ xᵏ dσ_t| ≥ ε) → 0` as `n → ∞`. -/
theorem wigner_semicircle_law_moments {P : Measure Ω} [IsProbabilityMeasure P]
    {X : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ} {Y : ℕ → ℕ → Ω → ℝ}
    (hY : IsWignerFamily P Y) (hXY : ∀ n, X n = wignerMatrix Y n)
    (hmean : ∀ i j, 1 ≤ i → i ≤ j → ∫ w, Y i j w ∂P = 0)
    {t : ℝ≥0} (hvar : ∫ w, Y 1 2 w ^ 2 ∂P = t)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Integrable (fun w => |Y 1 1 w| ^ k) P ∧ Integrable (fun w => |Y 1 2 w| ^ k) P)
    (k : ℕ) :
    TendstoInMeasure P (fun n => traceMoment (X n) k) atTop
      (fun _ => ∫ x, x ^ k ∂semicircleReal 0 t) := by
  sorry

end RandomMatrix
