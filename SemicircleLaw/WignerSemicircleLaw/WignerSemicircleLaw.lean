import SemicircleLaw.EmpiricalMeasure.EmpiricalSpectralDistribution
import SemicircleLaw.SemicircleDistribution.SemicircleDistribution
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction

/-!
# Wigner's semicircle law
Let `𝐗ₙ = (1/√n) 𝐘ₙ` be a sequence of Wigner matrices built from the family
`{Y_{ij}}_{1 ≤ i ≤ j}` (see `RandomMatrixTheory.IsWignerFamily`), with
`𝔼(Y_{ij}) = 0`, `𝔼(Y_{12}²) = t` and all moments of `Y₁₁` and `Y₁₂` finite. Then the
empirical spectral distributions `μ_{𝐗ₙ}` converge to the semicircle law
`σ_t = semicircleReal 0 t` (density `(1/(2πt)) √((4t - x²)₊)`, and `δ₀` if `t = 0`) *weakly in
probability*: for every `f ∈ C_b(ℝ)` and `ε > 0`,
`ℙ(|∫ f dμ_{𝐗ₙ}(·, w) - ∫ f dσ_t| > ε) → 0` as `n → ∞`.
-/

open MeasureTheory Filter Topology RandomMatrixTheory ProbabilityTheory
open scoped NNReal
open scoped BoundedContinuousFunction
namespace RandomMatrix

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Wigner's semicircle law** Let `𝐗ₙ = (1/√n) 𝐘ₙ` be a sequence of
Wigner matrices on the probability space `(Ω, 𝓕, ℙ)`, built from a Wigner family
`{Y_{ij}}_{1 ≤ i ≤ j}` whose entries satisfy
* `𝔼(Y_{ij}) = 0` for all `1 ≤ i ≤ j`,
* `𝔼(Y_{12}²) = t`,
* `𝔼(|Y₁₁|ᵏ) < ∞` and `𝔼(|Y₁₂|ᵏ) < ∞` for all `k ≥ 1`.
Then `μ_{𝐗ₙ} → σ_t` weakly in probability: for every `f ∈ C_b(ℝ)` and `ε > 0`,
`lim_{n → ∞} ℙ(|∫ f dμ_{𝐗ₙ}(·, w) - ∫ f dσ_t| > ε) = 0`. -/
theorem wigner_semicircle_law {P : Measure Ω} [IsProbabilityMeasure P]
    {X : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ} {Y : ℕ → ℕ → Ω → ℝ}
    (hY : IsWignerFamily P Y) (hXY : ∀ n, X n = wignerMatrix Y n)
    (hmean : ∀ i j, 1 ≤ i → i ≤ j → ∫ w, Y i j w ∂P = 0)
    {t : ℝ≥0} (hvar : ∫ w, Y 1 2 w ^ 2 ∂P = t)
    (hmom : ∀ k : ℕ, 1 ≤ k →
      Integrable (fun w => |Y 1 1 w| ^ k) P ∧ Integrable (fun w => |Y 1 2 w| ^ k) P)
    (f : ℝ →ᵇ ℝ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n => P {w | ε <
        |∫ x, f x ∂(RandomSymmMatrix.ofWigner ⟨Y, hY, hXY⟩ n).esd w -
          ∫ x, f x ∂semicircleReal 0 t|}) atTop (𝓝 0) := by
  sorry
