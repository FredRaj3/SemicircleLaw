import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)]

/-- Second moment about `m` decomposes as variance plus squared bias. -/
lemma integral_sub_const_sq_eq {X : Ω → ℝ} (hX : MemLp X 2) (m : ℝ) :
    𝔼[fun ω => (X ω - m) ^ 2] = Var[X] + (𝔼[X] - m) ^ 2 := by
  rw [variance_eq_sub hX]
  have h2 : Integrable (fun ω => X ω ^ 2) := hX.integrable_sq
  have h1 : Integrable X := hX.integrable one_le_two
  have h3 : Integrable (fun ω => X ω ^ 2 - 2 * m * X ω) := h2.sub (h1.const_mul _)
  have : (fun ω => (X ω - m) ^ 2) = fun ω => (X ω ^ 2 - 2 * m * X ω) + m ^ 2 := by
    ext ω; ring
  rw [this, integral_add h3 (integrable_const _),
    integral_sub h2 (h1.const_mul _), integral_const_mul]
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    one_mul, Pi.pow_apply]
  ring

/-- Step (i)+(ii): `ℙ(|X - m| ≥ ε) ≤ (√Var X + |𝔼 X - m|)² / ε²`. -/
theorem measureReal_abs_sub_ge_le {X : Ω → ℝ} (hX : MemLp X 2) (m : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (ℙ : Measure Ω).real {ω | ε ≤ |X ω - m|} ≤
      (Real.sqrt Var[X] + |𝔼[X] - m|) ^ 2 / ε ^ 2 := by
  -- (i) Markov's inequality applied to `(X - m)²` at level `ε²`
  have hY : Integrable (fun ω => (X ω - m) ^ 2) := (hX.sub (memLp_const m)).integrable_sq
  have hM := mul_meas_ge_le_integral_of_nonneg (μ := ℙ)
    (Eventually.of_forall fun ω => sq_nonneg (X ω - m)) hY (ε ^ 2)
  have hset : {ω | ε ≤ |X ω - m|} = {ω | ε ^ 2 ≤ (X ω - m) ^ 2} := by
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [← sq_abs (X ω - m)]
    exact (pow_le_pow_iff_left₀ hε.le (abs_nonneg _) two_ne_zero).symm
  rw [hset, le_div_iff₀ (by positivity), mul_comm]
  refine hM.trans ?_
  -- (ii) bound `𝔼[(X - m)²] = Var X + (𝔼 X - m)² ≤ (√Var X + |𝔼 X - m|)²`
  rw [integral_sub_const_sq_eq hX m]
  have hv : 0 ≤ Var[X] := variance_nonneg _ _
  have := Real.sq_sqrt hv
  nlinarith [Real.sqrt_nonneg Var[X], abs_nonneg (𝔼[X] - m), sq_abs (𝔼[X] - m)]

/-- If `𝔼[X_n²] < ∞`, `𝔼[X_n] → m` and `Var[X_n] → 0`, then `X_n → m` in probability. -/
theorem tendstoInMeasure_of_mean_variance (X : ℕ → Ω → ℝ) (m : ℝ)
    (hX : ∀ n, MemLp (X n) 2)
    (hmean : Tendsto (fun n => 𝔼[X n]) atTop (𝓝 m))
    (hvar : Tendsto (fun n => Var[X n]) atTop (𝓝 0)) :
    TendstoInMeasure ℙ X atTop (fun _ => m) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hb : Tendsto (fun n => (Real.sqrt Var[X n] + |𝔼[X n] - m|) ^ 2 / ε ^ 2)
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => Real.sqrt Var[X n]) atTop (𝓝 0) := by
      simpa using hvar.sqrt
    have h2 : Tendsto (fun n => |𝔼[X n] - m|) atTop (𝓝 0) := by
      simpa using (hmean.sub_const m).abs
    have := ((h1.add h2).pow 2).div_const (ε ^ 2)
    rwa [add_zero, zero_pow two_ne_zero, zero_div] at this
  have hreal : Tendsto (fun n => (ℙ : Measure Ω).real {ω | ε ≤ dist (X n ω) m})
      atTop (𝓝 0) := by
    refine squeeze_zero (fun n => measureReal_nonneg) (fun n => ?_) hb
    simpa [Real.dist_eq] using measureReal_abs_sub_ge_le (hX n) m hε
  have := ENNReal.tendsto_ofReal hreal
  rw [ENNReal.ofReal_zero] at this
  refine this.congr fun n => ?_
  exact ofReal_measureReal (measure_ne_top _ _)
