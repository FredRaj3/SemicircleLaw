import SemicircleLaw.EmpiricalMeasure.CourantFischer
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Weyl's perturbation inequality

Let `λ₀(A) ≥ ⋯ ≥ λₙ₋₁(A)` be the eigenvalues of a real symmetric matrix `A`
(`CourantFischer.eigenvaluesDesc`, `0`-based indices).  For real symmetric `A, C`,
`|λⱼ(C) - λⱼ(A)| ≤ ‖C - A‖_op`, where `‖·‖_op` is the operator norm of a matrix acting on
Euclidean space `ℝⁿ` (`Matrix.Norms.L2Operator`).  The proof uses the Courant–Fischer theorem.
-/

open Module CourantFischer
open scoped Matrix.Norms.L2Operator

namespace WeylPerturbation

variable {n : ℕ}

/-- `⟪x, (C - A) x⟫ = ⟪x, C x⟫ - ⟪x, A x⟫`. -/
lemma inner_op_sub (A C : Matrix (Fin n) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (op (C - A) x) = inner ℝ x (op C x) - inner ℝ x (op A x) := by
  simp [op, map_sub, LinearMap.sub_apply, inner_sub_right]

/-- Cauchy–Schwarz and the definition of the operator norm:
for a unit vector `x`, `⟪x, E x⟫ ≤ ‖E‖_op`. -/
lemma inner_op_le_opNorm (E : Matrix (Fin n) (Fin n) ℝ) {x : EuclideanSpace ℝ (Fin n)}
    (hx : ‖x‖ = 1) : inner ℝ x (op E x) ≤ ‖E‖ := by
  calc inner ℝ x (op E x) ≤ ‖x‖ * ‖op E x‖ := real_inner_le_norm _ _
    _ = ‖x‖ * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E x‖ := rfl
    _ ≤ ‖x‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ * ‖x‖) := by
        gcongr; exact ContinuousLinearMap.le_opNorm _ _
    _ = ‖E‖ := by
        -- The L2 operator norm of `E` is, by definition, the norm of `toEuclideanCLM E`.
        -- (Stated via `rfl` rather than a named lemma, since the lemma names differ between
        -- Mathlib versions.)
        have hnorm : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E‖ = ‖E‖ := rfl
        rw [hnorm, hx, one_mul, mul_one]

/-- One-sided Weyl inequality: `λⱼ(C) ≤ λⱼ(A) + ‖C - A‖_op`. -/
theorem eigenvaluesDesc_le_add_opNorm {A C : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hC : C.IsSymm) (j : Fin n) :
    eigenvaluesDesc hC j ≤ eigenvaluesDesc hA j + ‖C - A‖ := by
  -- Courant–Fischer for `C`: a `(j+1)`-dimensional `S` on which `min ⟪x, C x⟫ = λⱼ(C)`.
  obtain ⟨S, hS, hmin⟩ := (courant_fischer hC j).1
  -- Courant–Fischer for `A`: `S` contains a unit vector `x` with `⟪x, A x⟫ ≤ λⱼ(A)`.
  obtain ⟨x, hxS, hx1, hxA⟩ := exists_unit_inner_le hA j S hS
  have hxC : eigenvaluesDesc hC j ≤ inner ℝ x (op C x) := hmin.2 ⟨x, hxS, hx1, rfl⟩
  have hE := inner_op_le_opNorm (C - A) hx1
  rw [inner_op_sub] at hE
  linarith

/-- **Weyl's perturbation inequality.** For real symmetric matrices `A` and `C`,
`|λⱼ(C) - λⱼ(A)| ≤ ‖C - A‖_op` for every `j`. -/
theorem abs_eigenvaluesDesc_sub_le {A C : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)
    (hC : C.IsSymm) (j : Fin n) :
    |eigenvaluesDesc hC j - eigenvaluesDesc hA j| ≤ ‖C - A‖ := by
  have h1 := eigenvaluesDesc_le_add_opNorm hA hC j
  have h2 := eigenvaluesDesc_le_add_opNorm hC hA j
  rw [norm_sub_rev] at h2
  rw [abs_le]
  constructor <;> linarith

end WeylPerturbation
