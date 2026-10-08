import SemicircleLaw.EmpiricalMeasure.EigenvalueContinuity
import Mathlib.Data.Sym.Card
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Operator norm vs. coordinate norm on `Sym_n(ℝ)`

With `d = n(n+1)/2` and `‖A‖_coord = √(∑_{i ≤ j} aᵢⱼ²)`, for symmetric `A`
`‖A‖_coord / √d ≤ ‖A‖_op ≤ √2 ‖A‖_coord`.
Consequently the canonical map `Φ : Sym_n(ℝ) → ℝ^d`, `Φ(A) = (aᵢⱼ)_{i ≤ j}`, is a
homeomorphism (both directions Lipschitz), and `λⱼ ∘ Φ⁻¹` is continuous and Borel measurable.
-/

open scoped Matrix.Norms.L2Operator

namespace EigenvalueContinuity

variable {n : ℕ}

/-- Index set `{(i, j) : i ≤ j}` of the upper-triangular coordinates. -/
abbrev UpperIdx (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}

/-- The coordinate Euclidean norm `‖A‖_coord = √(∑_{i ≤ j} aᵢⱼ²)`. -/
noncomputable def coordNorm (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ p : UpperIdx n, A p.1.1 p.1.2 ^ 2)

lemma card_upperIdx (n : ℕ) : Fintype.card (UpperIdx n) = n * (n + 1) / 2 := by
  have hb : Function.Bijective (fun p : UpperIdx n => (s(p.1.1, p.1.2) : Sym2 (Fin n))) := by
    constructor
    · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨c, d⟩, hcd⟩ h
      simp only [Sym2.eq_iff] at h
      apply Subtype.ext
      simp only [Prod.mk.injEq]
      rcases h with h | ⟨rfl, rfl⟩
      · exact h
      · dsimp at hab hcd; constructor <;> omega
    · intro z
      induction z using Sym2.ind with
      | _ a b =>
        rcases le_total a b with h | h
        · exact ⟨⟨(a, b), h⟩, rfl⟩
        · exact ⟨⟨(b, a), h⟩, Sym2.eq_swap⟩
  rw [Fintype.card_of_bijective hb, Sym2.card, Fintype.card_fin, Nat.choose_two_right,
    Nat.add_sub_cancel, Nat.mul_comm]

/-- Sum over the upper-triangular index set as a double sum. -/
lemma sum_upperIdx (f : Fin n → Fin n → ℝ) :
    ∑ p : UpperIdx n, f p.1.1 p.1.2 = ∑ i, ∑ j, if i ≤ j then f i j else 0 := by
  rw [← Fintype.sum_prod_type' (f := fun i j => if i ≤ j then f i j else 0), ← Finset.sum_filter]
  exact (Finset.sum_subtype _ (by simp) (fun p : Fin n × Fin n => f p.1 p.2)).symm

/-- `|aᵢⱼ| ≤ ‖A‖_op`. -/
lemma abs_entry_le_opNorm (A : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : |A i j| ≤ ‖A‖ := by
  have h1 : A i j = (Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.single j 1)) i := by
    change A i j = (Matrix.mulVec A (EuclideanSpace.single j (1:ℝ)).ofLp) i
    simp [Matrix.mulVec_single]
  rw [h1, ← Real.norm_eq_abs]
  calc _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A (EuclideanSpace.single j 1)‖ :=
        PiLp.norm_apply_le _ _
    _ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖EuclideanSpace.single j (1:ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖A‖ := by rw [EuclideanSpace.norm_single, norm_one, mul_one]; rfl

/-- `‖A‖_op ≤ ‖A‖_F`. -/
lemma opNorm_le_frobenius (A : Matrix (Fin n) (Fin n) ℝ) :
    ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := by
  -- The L2 operator norm of `A` is, by definition, the norm of `toEuclideanCLM A`.
  -- (Stated via `rfl` rather than a named lemma, since lemma names differ between
  -- Mathlib versions.)
  have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ = ‖A‖ := rfl
  rw [← hnorm]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul (by positivity), EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  -- Cauchy–Schwarz for row `i`, with the ring `ℝ` and both functions given explicitly so
  -- that no typeclass argument is left as a metavariable.
  have h := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) Finset.univ (fun j => A i j) (fun j => x j)
  simp only [Real.norm_eq_abs, sq_abs]
  -- `(A x)ᵢ = ∑ⱼ Aᵢⱼ xⱼ` holds definitionally, so `h` closes the goal as is.
  exact h

/-- For symmetric `A`, `‖A‖_F² ≤ 2 ‖A‖_coord²`. -/
lemma frobenius_sq_le_two_coord {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ∑ i, ∑ j, A i j ^ 2 ≤ 2 * ∑ p : UpperIdx n, A p.1.1 p.1.2 ^ 2 := by
  rw [sum_upperIdx (fun i j => A i j ^ 2), two_mul]
  nth_rewrite 2 [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  have hs : A j i = A i j := by simpa using congrFun (congrFun hA i) j
  rw [hs]
  rcases le_total i j with h | h
  · simp [h]; split_ifs <;> positivity
  · simp [h]; split_ifs <;> positivity

/-- Left inequality: `‖A‖_coord / √d ≤ ‖A‖_op`, `d = n(n+1)/2`. -/
theorem coordNorm_div_le_opNorm (A : Matrix (Fin n) (Fin n) ℝ) :
    coordNorm A / Real.sqrt (n * (n + 1) / 2 : ℕ) ≤ ‖A‖ := by
  have hsq : ∑ p : UpperIdx n, A p.1.1 p.1.2 ^ 2 ≤ (n * (n + 1) / 2 : ℕ) * ‖A‖ ^ 2 := by
    calc ∑ p : UpperIdx n, A p.1.1 p.1.2 ^ 2 ≤ ∑ _p : UpperIdx n, ‖A‖ ^ 2 := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (abs_entry_le_opNorm A _ _) 2
      _ = _ := by simp [card_upperIdx]
  have hc : coordNorm A ≤ Real.sqrt (n * (n + 1) / 2 : ℕ) * ‖A‖ := by
    rw [coordNorm, ← Real.sqrt_sq (norm_nonneg A), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hsq
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (n * (n + 1) / 2 : ℕ)) with h | h
  · rw [← h, div_zero]; exact norm_nonneg _
  · rw [div_le_iff₀ h, mul_comm]; exact hc

/-- Right inequality: `‖A‖_op ≤ √2 ‖A‖_coord` for symmetric `A`. -/
theorem opNorm_le_sqrt_two_mul_coordNorm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    ‖A‖ ≤ Real.sqrt 2 * coordNorm A := by
  calc ‖A‖ ≤ Real.sqrt (∑ i, ∑ j, A i j ^ 2) := opNorm_le_frobenius A
    _ ≤ Real.sqrt (2 * ∑ p : UpperIdx n, A p.1.1 p.1.2 ^ 2) :=
        Real.sqrt_le_sqrt (frobenius_sq_le_two_coord hA)
    _ = Real.sqrt 2 * coordNorm A := by rw [Real.sqrt_mul (by norm_num), coordNorm]

/-- The canonical coordinate map `Φ : Sym_n(ℝ) → ℝ^d`, `Φ(A) = (aᵢⱼ)_{i ≤ j}`. -/
noncomputable def toCoord (A : SymMat n) : EuclideanSpace ℝ (UpperIdx n) :=
  WithLp.toLp 2 (fun p => A.1 p.1.1 p.1.2)

/-- Symmetric extension of upper-triangular coordinates to a matrix. -/
def symmExt (x : EuclideanSpace ℝ (UpperIdx n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if h : i ≤ j then x ⟨(i, j), h⟩ else x ⟨(j, i), le_of_not_ge h⟩

lemma symmExt_isSymm (x : EuclideanSpace ℝ (UpperIdx n)) : (symmExt x).IsSymm := by
  ext i j
  simp only [symmExt, Matrix.transpose_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.mpr h]
  · rfl
  · simp [h.le, not_le.mpr h]

/-- The inverse map `Φ⁻¹ : ℝ^d → Sym_n(ℝ)`. -/
def ofCoord (x : EuclideanSpace ℝ (UpperIdx n)) : SymMat n := ⟨symmExt x, symmExt_isSymm x⟩

lemma toCoord_ofCoord (x : EuclideanSpace ℝ (UpperIdx n)) : toCoord (ofCoord x) = x := by
  ext p
  simp [toCoord, ofCoord, symmExt, p.2]

lemma ofCoord_toCoord (A : SymMat n) : ofCoord (toCoord A) = A := by
  apply Subtype.ext
  ext i j
  simp only [ofCoord, symmExt, toCoord, Matrix.of_apply]
  split_ifs with h
  · rfl
  · simpa using congrFun (congrFun A.2 i) j

lemma norm_toCoord_sub (A C : SymMat n) : ‖toCoord A - toCoord C‖ = coordNorm (A.1 - C.1) := by
  rw [EuclideanSpace.norm_eq, coordNorm]
  simp [toCoord]

lemma symmExt_sub (x y : EuclideanSpace ℝ (UpperIdx n)) :
    symmExt x - symmExt y = symmExt (x - y) := by
  ext i j
  simp only [symmExt, Matrix.sub_apply, Matrix.of_apply]
  split_ifs <;> simp

lemma coordNorm_symmExt (x : EuclideanSpace ℝ (UpperIdx n)) : coordNorm (symmExt x) = ‖x‖ := by
  rw [EuclideanSpace.norm_eq, coordNorm]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp [symmExt, p.2]

/-- `Φ` is `√d`-Lipschitz from `(Sym_n(ℝ), ‖·‖_op)` to `(ℝ^d, ‖·‖_coord)` (left inequality). -/
lemma lipschitz_toCoord :
    LipschitzWith ⟨Real.sqrt (n * (n + 1) / 2 : ℕ), Real.sqrt_nonneg _⟩ (toCoord (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun A C => ?_
  rw [dist_eq_norm, norm_toCoord_sub, NNReal.coe_mk]
  have h := coordNorm_div_le_opNorm (A.1 - C.1)
  have hd : dist A C = ‖A.1 - C.1‖ := dist_eq_norm A.1 C.1
  rw [hd]
  rcases eq_or_lt_of_le (Real.sqrt_nonneg (n * (n + 1) / 2 : ℕ)) with h0 | h0
  · -- `d = 0`, i.e. `n = 0`: everything vanishes
    have hn : n * (n + 1) / 2 = 0 := by
      have := h0.symm
      rw [Real.sqrt_eq_zero (by positivity)] at this
      exact_mod_cast this
    have hc : coordNorm (A.1 - C.1) = 0 := by
      rw [coordNorm]
      have : Fintype.card (UpperIdx n) = 0 := by rw [card_upperIdx, hn]
      haveI := Fintype.card_eq_zero_iff.mp this
      simp
    rw [hc, ← h0, zero_mul]
  · rwa [div_le_iff₀ h0, mul_comm] at h

/-- `Φ⁻¹` is `√2`-Lipschitz from `(ℝ^d, ‖·‖_coord)` to `(Sym_n(ℝ), ‖·‖_op)` (right inequality). -/
lemma lipschitz_ofCoord :
    LipschitzWith ⟨Real.sqrt 2, Real.sqrt_nonneg _⟩ (ofCoord (n := n)) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hd : dist (ofCoord x) (ofCoord y) = ‖symmExt x - symmExt y‖ :=
    dist_eq_norm (symmExt x) (symmExt y)
  rw [hd, symmExt_sub, dist_eq_norm, NNReal.coe_mk, ← coordNorm_symmExt]
  exact opNorm_le_sqrt_two_mul_coordNorm (symmExt_isSymm _)

/-- **The canonical homeomorphism** `Φ : Sym_n(ℝ) ≃ₜ ℝ^{n(n+1)/2}`, `Φ(A) = (aᵢⱼ)_{i ≤ j}`.
Its continuity in both directions comes from the norm equivalence
`‖A‖_coord / √d ≤ ‖A‖_op ≤ √2 ‖A‖_coord`; hence the operator-norm topology and the
coordinate topology on `Sym_n(ℝ)` agree. -/
noncomputable def coordHomeomorph (n : ℕ) : SymMat n ≃ₜ EuclideanSpace ℝ (UpperIdx n) where
  toFun := toCoord
  invFun := ofCoord
  left_inv := ofCoord_toCoord
  right_inv := toCoord_ofCoord
  continuous_toFun := lipschitz_toCoord.continuous
  continuous_invFun := lipschitz_ofCoord.continuous

/-- In coordinates: `x ↦ λⱼ(Φ⁻¹ x)` is continuous on `ℝ^{n(n+1)/2}`. -/
theorem continuous_eigenvalueMap_coord (j : Fin n) :
    Continuous (fun x : EuclideanSpace ℝ (UpperIdx n) => eigenvalueMap j (ofCoord x)) :=
  (continuous_eigenvalueMap j).comp lipschitz_ofCoord.continuous

/-- In coordinates: `x ↦ λⱼ(Φ⁻¹ x)` is Borel measurable on `ℝ^{n(n+1)/2}`. -/
theorem measurable_eigenvalueMap_coord (j : Fin n) :
    Measurable (fun x : EuclideanSpace ℝ (UpperIdx n) => eigenvalueMap j (ofCoord x)) :=
  (continuous_eigenvalueMap_coord j).measurable

end EigenvalueContinuity
