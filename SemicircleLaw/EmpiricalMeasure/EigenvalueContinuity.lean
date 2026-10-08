import SemicircleLaw.EmpiricalMeasure.WeylsEstimate
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Continuity and measurability of the eigenvalue maps

Let `Sym_n(ℝ) = {A : Matrix (Fin n) (Fin n) ℝ // A.IsSymm}` with the subspace topology
(equivalently, the one induced by the operator norm `‖·‖_op`).  For each `j`, the map
`λⱼ : Sym_n(ℝ) → ℝ`, `A ↦ λⱼ(A)` (the `j`-th largest eigenvalue) is continuous, hence
Borel measurable.  The proof is the `ε`–`δ` argument with `δ = ε`, using Weyl's
perturbation inequality `|λⱼ(C) - λⱼ(A)| ≤ ‖C - A‖_op`.
-/

open CourantFischer WeylPerturbation
open scoped Matrix.Norms.L2Operator

namespace EigenvalueContinuity

variable {n : ℕ}

/-- The space `Sym_n(ℝ)` of real symmetric `n × n` matrices. -/
abbrev SymMat (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℝ // A.IsSymm}

/-- The `j`-th eigenvalue map `λⱼ : Sym_n(ℝ) → ℝ`. -/
noncomputable def eigenvalueMap (j : Fin n) : SymMat n → ℝ :=
  fun A => eigenvaluesDesc A.2 j

/-- **Continuity of eigenvalues.** For each `j`, `λⱼ : Sym_n(ℝ) → ℝ` is continuous.
Proof: given `ε > 0` take `δ = ε`; if `‖C - A‖_op < δ` then by Weyl
`|λⱼ(C) - λⱼ(A)| ≤ ‖C - A‖_op < ε`. -/
theorem continuous_eigenvalueMap (j : Fin n) : Continuous (eigenvalueMap (n := n) j) := by
  rw [Metric.continuous_iff]
  intro A ε hε
  refine ⟨ε, hε, fun C hC => ?_⟩
  rw [Real.dist_eq]
  calc |eigenvalueMap j C - eigenvalueMap j A| ≤ ‖C.1 - A.1‖ :=
        abs_eigenvaluesDesc_sub_le A.2 C.2 j
    _ = dist C A := (dist_eq_norm C.1 A.1).symm
    _ < ε := hC

/-- **Measurability of eigenvalues.** For each `j`, `λⱼ : Sym_n(ℝ) → ℝ` is Borel measurable
(with the Borel σ-algebra of `Sym_n(ℝ)` on the domain and of `ℝ` on the codomain). -/
theorem measurable_eigenvalueMap (j : Fin n) :
    @Measurable (SymMat n) ℝ (borel (SymMat n)) _ (eigenvalueMap j) := by
  letI : MeasurableSpace (SymMat n) := borel (SymMat n)
  haveI : BorelSpace (SymMat n) := ⟨rfl⟩
  exact (continuous_eigenvalueMap j).measurable

end EigenvalueContinuity
