import SemicircleLaw.RandomMatrixAlternative.RandomMatrix
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Real.Sqrt

/-!
# Wigner matrices

Throughout, `(Ω, 𝓕)` is a measurable space (`[MeasurableSpace Ω]`) and `P : Measure Ω` is a
probability measure (`[IsProbabilityMeasure P]`), so `(Ω, 𝓕, P)` is a probability space.

The family `{Y_{ij}}_{1 ≤ i ≤ j}` is encoded as `Y : ℕ → ℕ → Ω → ℝ` with **1-based** indices
(`Y i j` is `Y_{ij}`); see `RequestProject.RandomMatrix` for the conventions and for the
symmetric matrix `𝐘ₙ = symmetricMatrix Y n`.
-/

open MeasureTheory ProbabilityTheory

namespace RandomMatrixTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses of the Wigner-matrix definition on the 1-based family `{Y_{ij}}_{1 ≤ i ≤ j}`:
* every `Y_{ij}` with `1 ≤ i ≤ j` is a real-valued random variable;
* (1) the family `{Y_{ij}}_{1 ≤ i ≤ j}` is (mutually) independent;
* (2) the diagonal entries `{Y_{ii}}_{i ≥ 1}` are identically distributed;
* (3) the off-diagonal entries `{Y_{ij}}_{1 ≤ i < j}` are identically distributed.

"Identically distributed" is expressed by comparing each entry with a fixed representative
(`Y₁₁` on the diagonal, `Y₁₂` off the diagonal), which is equivalent since `IdentDistrib`
is an equivalence relation. -/
structure IsWignerFamily (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → ℕ → Ω → ℝ) :
    Prop where
  measurable : ∀ i j, 1 ≤ i → i ≤ j → Measurable (Y i j)
  indep : iIndepFun (fun p : UpperIndex => Y p.1.1 p.1.2) P
  identDistrib_diag : ∀ i, 1 ≤ i → IdentDistrib (Y i i) (Y 1 1) P P
  identDistrib_offDiag : ∀ i j, 1 ≤ i → i < j → IdentDistrib (Y i j) (Y 1 2) P P

/-- The scaled matrices `𝐗ₙ := (1/√n) 𝐘ₙ`. -/
noncomputable def wignerMatrix (Y : ℕ → ℕ → Ω → ℝ) (n : ℕ) : Ω → Matrix (Fin n) (Fin n) ℝ :=
  fun ω => (1 / Real.sqrt n) • symmetricMatrix Y n ω

/-- A sequence `X = (𝐗ₙ)ₙ` of `n × n` random matrices is a sequence of **Wigner matrices**
if `𝐗ₙ = (1/√n) 𝐘ₙ` for some family `{Y_{ij}}_{1 ≤ i ≤ j}` satisfying the Wigner hypotheses. -/
def IsWignerMatrixSeq (P : Measure Ω) [IsProbabilityMeasure P]
    (X : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ Y : ℕ → ℕ → Ω → ℝ, IsWignerFamily P Y ∧ ∀ n, X n = wignerMatrix Y n

omit [MeasurableSpace Ω] in
/-- Each Wigner matrix `𝐗ₙ(ω)` is symmetric. -/
theorem wignerMatrix_isSymm (Y : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (wignerMatrix Y n ω).IsSymm :=
  (symmetricMatrix_isSymm Y n ω).smul _

/-- Each Wigner matrix `𝐗ₙ` is a random matrix. -/
theorem wignerMatrix_isRandomMatrix {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → ℕ → Ω → ℝ} (hY : IsWignerFamily P Y) (n : ℕ) :
    IsRandomMatrix (wignerMatrix Y n) := by
  intro i j
  exact (symmetricMatrix_isRandomMatrix hY.measurable n i j).const_mul _

/-- The canonical sequence `n ↦ (1/√n) 𝐘ₙ` of a Wigner family is a sequence of Wigner matrices. -/
theorem isWignerMatrixSeq_wignerMatrix {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : ℕ → ℕ → Ω → ℝ} (hY : IsWignerFamily P Y) :
    IsWignerMatrixSeq P (wignerMatrix Y) :=
  ⟨Y, hY, fun _ => rfl⟩

/-- Every member of a sequence of Wigner matrices is a symmetric random matrix. -/
theorem IsWignerMatrixSeq.isRandomMatrix_isSymm {P : Measure Ω} [IsProbabilityMeasure P]
    {X : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ} (hX : IsWignerMatrixSeq P X) (n : ℕ) :
    IsRandomMatrix (X n) ∧ ∀ ω, (X n ω).IsSymm := by
  obtain ⟨Y, hY, hXY⟩ := hX
  rw [hXY n]
  exact ⟨wignerMatrix_isRandomMatrix hY n, wignerMatrix_isSymm Y n⟩

end RandomMatrixTheory
