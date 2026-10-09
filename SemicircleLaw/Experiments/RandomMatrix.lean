import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Random matrices

Throughout, `(Ω, 𝓕)` is a measurable space (`[MeasurableSpace Ω]`).
`ℝ` carries its Borel σ-algebra `𝓑(ℝ)` (Mathlib's default `MeasurableSpace ℝ` instance), and a
real-valued *random variable* is a measurable map `Ω → ℝ`.

## Conventions (1-based indexing)

* The family `{Y_{ij}}_{1 ≤ i ≤ j}` is encoded as `Y : ℕ → ℕ → Ω → ℝ` with **1-based** indices:
  `Y i j` *is* `Y_{ij}`. Only the values with `1 ≤ i ≤ j` are ever used; the values `Y 0 j`
  and `Y i j` with `i > j` are irrelevant junk.
  The index set of the family is `UpperIndex = {(i, j) : ℕ × ℕ // 1 ≤ i ∧ i ≤ j}`.
* An `n × n` matrix is a `Matrix (Fin n) (Fin n) ℝ` (Mathlib's standard choice). The element
  `k : Fin n` stands for the row/column number `k + 1 ∈ {1, …, n}`; the lemma
  `symmetricMatrix_apply_of_le` states the entry formula directly in 1-based terms.
-/

open MeasureTheory

namespace RandomMatrixTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## Random matrices -/

/-- A **random matrix** of size `n × n`: a matrix-valued map `X : Ω → Matrix (Fin n) (Fin n) ℝ`
all of whose entries `ω ↦ X ω i j` are (real-valued) random variables, i.e. measurable
with respect to `𝓕` and the Borel σ-algebra on `ℝ`. -/
def IsRandomMatrix {n : ℕ} (X : Ω → Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j : Fin n, Measurable fun ω => X ω i j

/-! ## Symmetric random matrices built from a family `{Y_{ij}}_{1 ≤ i ≤ j}` -/

/-- The index set `{(i, j) | 1 ≤ i ≤ j}` of the family `{Y_{ij}}_{1 ≤ i ≤ j}` (1-based). -/
abbrev UpperIndex : Type := {p : ℕ × ℕ // 1 ≤ p.1 ∧ p.1 ≤ p.2}

/-- The symmetric matrix `𝐘ₙ` built from the 1-based family `Y`: for `1 ≤ i, j ≤ n`,
`[𝐘ₙ]_{ij} = Y_{ij}` if `i ≤ j` and `[𝐘ₙ]_{ij} = Y_{ji}` if `i > j`.
(The row/column `k : Fin n` corresponds to the 1-based number `k + 1`.) -/
def symmetricMatrix (Y : ℕ → ℕ → Ω → ℝ) (n : ℕ) : Ω → Matrix (Fin n) (Fin n) ℝ :=
  fun ω i j => if i ≤ j then Y (i + 1) (j + 1) ω else Y (j + 1) (i + 1) ω

omit [MeasurableSpace Ω] in
/-- Entry formula in 1-based terms: for `1 ≤ i ≤ j ≤ n`, the `(i, j)` entry of `𝐘ₙ`
(i.e. the entry in row `i - 1`, column `j - 1` of the underlying `Fin n`-indexed matrix)
is `Y_{ij}`. -/
theorem symmetricMatrix_apply_of_le (Y : ℕ → ℕ → Ω → ℝ) {n i j : ℕ} (hi : 1 ≤ i)
    (hij : i ≤ j) (hjn : j ≤ n) (ω : Ω) :
    symmetricMatrix Y n ω ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ = Y i j ω := by
  have h : (⟨i - 1, by omega⟩ : Fin n) ≤ ⟨j - 1, by omega⟩ := by
    rw [Fin.mk_le_mk]; omega
  simp only [symmetricMatrix, h, if_true]
  congr 2 <;> omega

omit [MeasurableSpace Ω] in
/-- Entry formula in 1-based terms below the diagonal: for `1 ≤ j < i ≤ n`, the `(i, j)` entry
of `𝐘ₙ` is `Y_{ji}`. -/
theorem symmetricMatrix_apply_of_lt (Y : ℕ → ℕ → Ω → ℝ) {n i j : ℕ} (hj : 1 ≤ j)
    (hji : j < i) (hin : i ≤ n) (ω : Ω) :
    symmetricMatrix Y n ω ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ = Y j i ω := by
  have h : ¬ (⟨i - 1, by omega⟩ : Fin n) ≤ ⟨j - 1, by omega⟩ := by
    rw [Fin.mk_le_mk]; omega
  simp only [symmetricMatrix, h, if_false]
  congr 2 <;> omega

omit [MeasurableSpace Ω] in
/-- Each `𝐘ₙ(ω)` is a symmetric matrix. -/
theorem symmetricMatrix_isSymm (Y : ℕ → ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    (symmetricMatrix Y n ω).IsSymm := by
  ext i j
  simp only [Matrix.transpose_apply, symmetricMatrix]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h.le, not_le.mpr h]
  · rfl
  · simp [h.le, not_le.mpr h]

/-- If every `Y_{ij}` (`1 ≤ i ≤ j`) is a random variable, then each `𝐘ₙ` is a random matrix. -/
theorem symmetricMatrix_isRandomMatrix {Y : ℕ → ℕ → Ω → ℝ}
    (hY : ∀ i j, 1 ≤ i → i ≤ j → Measurable (Y i j)) (n : ℕ) :
    IsRandomMatrix (symmetricMatrix Y n) := by
  intro i j
  unfold symmetricMatrix
  by_cases h : i ≤ j
  · simpa [h] using hY (i + 1) (j + 1) (by omega) (by simpa using (Fin.le_iff_val_le_val.mp h))
  · simpa [h] using
      hY (j + 1) (i + 1) (by omega) (by simpa using (Fin.le_iff_val_le_val.mp (not_le.mp h).le))

omit [MeasurableSpace Ω] in
/-- Sanity check: `𝐘₂ = !![Y₁₁, Y₁₂; Y₁₂, Y₂₂]`, now literally with 1-based indices. -/
example (Y : ℕ → ℕ → Ω → ℝ) (ω : Ω) :
    symmetricMatrix Y 2 ω = !![Y 1 1 ω, Y 1 2 ω; Y 1 2 ω, Y 2 2 ω] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symmetricMatrix]

end RandomMatrixTheory
