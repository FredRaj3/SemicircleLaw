import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.HasLaw
import SemicircleLaw.RandomMatrix.RandomMatrix
import Mathlib.Combinatorics.Enumerative.Catalan

import Hammer


/-!
# Wigner Matrices

We define real Wigner random matrices and random matrix ensembles.

## Main definitions

*

## Main results

*
-/

open scoped ENNReal NNReal Real Complex

open MeasureTheory ProbabilityTheory

variable {n : ℕ}
variable (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ_moments : ∀ (k : ℕ), Integrable (fun x ↦ x^k) μ)
  (hν_moments : ∀ (k : ℕ), Integrable (fun x ↦ x^k) ν)
  (hμ_mean : integral μ id = 0) (hν_mean : integral ν id = 0)
  (hμ_var : integral μ (fun x ↦ x^2) = 1) (hν_var : integral ν (fun x ↦ x^2) = 1)

instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ ) := by
   unfold Matrix; infer_instance

/-- The index set for the strictly upper-triangular entries of an `n x n` matrix. -/
def OffDiagIndex (n : ℕ) := { p : Fin n × Fin n // p.1 < p.2 }

instance : Fintype (OffDiagIndex n) := by
  rw[OffDiagIndex]
  infer_instance


/-- The index set for the independent random variables of a Wigner matrix.
This is the disjoint union of indices for the diagonal (`Fin n`) and the
off diagonal (`OffDiagIndex n`) entries. -/
def Index (n : ℕ) := (Fin n) ⊕ (OffDiagIndex n)

instance : Fintype (Index n) := by
  rw[Index]
  infer_instance


/-- The sample space for an `n x n` Wigner matrix. It is the product of ℝ over Index n. -/
abbrev WignerSpace (n : ℕ) := Index n → ℝ

instance (n : ℕ) : MeasurableSpace (WignerSpace n) := by
  infer_instance

/-- The measure distribution for a Wigner matrix. It assigns the measure `ν` to diagonal
entries and `μ` to off-diagonal entries. -/
def wignerMeasureDist (n : ℕ) : Index n → Measure ℝ
  | Sum.inl _ => ν -- Diagonal entries get measure ν
  | Sum.inr _ => μ -- Off diagonal entries get measure μ


/-- The probability measure on the sample space `WignerSpace n`, which makes the
coordinate projections independent random variables with distributions given by
`wignerMeasureDist`. -/
noncomputable
def WignerMeasure (n : ℕ) : Measure (WignerSpace n) :=
  Measure.pi (wignerMeasureDist μ ν n)

instance instIsProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (WignerMeasure μ ν n) := by
  rw[WignerMeasure]
  --apply MeasureTheory.Measure.pi.instIsProbabilityMeasure
  sorry

/-- The function that takes an element of WignerSpace (a map (Fin n)⊕(OffDiagIndex n) → ℝ)
to the corresponding function (Fin n) → (Fin n) → ℝ that respects the symmetric structure of Wigner
matrices.-/
def wignerMatrixEntryFunction (ω : WignerSpace n) : (Fin n) → (Fin n) → ℝ :=
  fun i j =>
    if h_eq : i = j then
      ω (Sum.inl i)
    else if h_lt : i < j then
      ω (Sum.inr ⟨(i, j), h_lt⟩)
    else
      have h_gt : j < i := by
         apply lt_of_le_of_ne
         apply le_of_not_gt h_lt
         grind
      ω (Sum.inr ⟨(j, i),h_gt⟩)


def wignerMatrixMap' (ω : WignerSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (wignerMatrixEntryFunction ω)

/-- A wigner matrix is defined as a matrix valued random variable.-/
def wignerMatrixMap (n : ℕ) : (WignerSpace n) → Matrix (Fin n) (Fin n) ℝ :=
  fun (ω : WignerSpace n) ↦ wignerMatrixMap' ω

/--For any `(n : ℕ)` the map `wignerMatrixMap` is measurable from `WignerSpace n` to
  `Matrix (Fin n) (Fin n) ℝ`-/
@[fun_prop]
lemma wignerMatrixMapMeasurable (n : ℕ) : Measurable (wignerMatrixMap n) := by
  sorry

/--For any `(n : ℕ)` the map `wignerMatrixMap` is `AEMeasurable` from `WignerSpace n` to
  `Matrix (Fin n) (Fin n) ℝ`-/
@[fun_prop]
lemma wignerMatrixMapAEMeasurable (n : ℕ) : AEMeasurable (wignerMatrixMap n) := by
  fun_prop


/-An `n × n` Wigner matrix measure is a measure on `Matrix (Fin n) (Fin n) ℝ` which is given by
the pushworward of `WignerMeasure` by the map `wignerMatrixMap`. -/
noncomputable
def wignerMatrixMeasure (n : ℕ) (μ ν : Measure ℝ ) : Measure (Matrix (Fin n) (Fin n) ℝ) :=
  Measure.map (wignerMatrixMap n) (WignerMeasure μ ν n)


/- UNDER CONSTRUCTION-/


/-Lemmas that will be useful for working with Wigner Matrices-/

/--The measure `wignerMatrixMeasure` is indeed a `ProbabilityMeasure`.-/
instance (n : ℕ) : IsProbabilityMeasure (wignerMatrixMeasure n μ ν) := by
  sorry

/--The diagonal entry of a Wigner Matrix is a measurable function from `WignerSpace` to `ℝ`-/
@[fun_prop]
lemma diagonalEntryMeasurable (n : ℕ) (i : Fin n) :
      Measurable (fun ω ↦ (wignerMatrixMap n ω) i i):= by
  apply measurable_entry
  apply wignerMatrixMapMeasurable

/--The off-diagonal entry of a Wigner Matrix is a measurable function from `WignerSpace` to `ℝ`-/
@[fun_prop]
lemma offDiagonalEntryMeasurable (n : ℕ) (i j : Fin n) :
      Measurable (fun ω ↦ (wignerMatrixMap n ω) i j):= by
  apply measurable_entry
  apply wignerMatrixMapMeasurable

/--The diagonal entries of a Wigner Matrix have law ν -/
lemma diagonalHasLaw (n : ℕ) (i : Fin n) :
    HasLaw (fun ω ↦ (wignerMatrixMap n ω) i i) ν (WignerMeasure μ ν n) := by
  sorry

/--The upper diagonal entries of a Wigner Matrix have law μ -/
lemma offDiagonalHasLaw' (n : ℕ) {i j : Fin n} (h : i < j) :
    HasLaw (fun ω ↦ (wignerMatrixMap n ω) i j) μ (WignerMeasure μ ν n) := by
  sorry

/--The off-diagonal entries of a Wigner Matrix have law μ -/
lemma offDiagonalHasLaw (n : ℕ) {i j : Fin n} (h : i ≠ j) :
    HasLaw (fun ω ↦ (wignerMatrixMap n ω) i j) μ (WignerMeasure μ ν n) := by
  sorry

/-- The map that sends a Wigner Matrix to its kth power is measurable.-/
@[fun_prop]
lemma wignerMatrixPowMeasurable (n : ℕ) (k : ℕ) :
    Measurable (fun ω ↦ ((wignerMatrixMap n ω)^k)) := by
  apply matrix_measurable_pow
  apply wignerMatrixMapMeasurable


variable {ω : WignerSpace n}
variable {k : ℕ}
#check ((wignerMatrixMap n ω)^k).trace

def wignerMatrixTracePower (n : ℕ) (k : ℕ) : (WignerSpace n) → ℝ :=
  fun ω ↦ ((wignerMatrixMap n ω)^k).trace

/-- The map that sends a Wigner Matrix to the trace of its kth power is measurable.-/
@[fun_prop]
lemma wignerMatrixTracePowerMeasurable (n : ℕ) (k : ℕ) :
    Measurable (wignerMatrixTracePower n k) := by
  apply measurable_trace
  apply wignerMatrixPowMeasurable

/--The expectation of the trace of the kth power of a Wigner matrix is equal to 0 when k is odd.-/
theorem wignerMatrixMomentOddExpectation (n : ℕ) (k : ℕ) (hk : Odd k) :
  (WignerMeasure μ ν n)[wignerMatrixTracePower n k] = 0 := by
  sorry

/--The expectation of the trace of the kth power of a Wigner matrix is equal to the k/2 Catalan
number when k is even.-/
theorem wignerMatrixMomentEvenExpectation (n : ℕ) (k : ℕ) (hk : Even k) (hk' : k > 0) :
  (WignerMeasure μ ν n)[wignerMatrixTracePower n k] = (catalan (k/2) : ℝ) := by
  sorry
