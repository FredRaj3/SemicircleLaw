import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Combinatorics.Enumerative.Catalan
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

import Hammer


/-!
# Random Matrices

We define random matrices and random matrix ensembles.

## Main definitions

*

## Main results

*
-/

open scoped ENNReal NNReal Real Complex

open MeasureTheory ProbabilityTheory

variable {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [PolishSpace α] [BorelSpace α]
  [Ring α] [IsTopologicalRing α]
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {m n : ℕ }


namespace ProbabilityTheory

instance : MeasurableSpace (Matrix (Fin m) (Fin n) α) := by
   unfold Matrix; infer_instance

/-
What I would like to do in this file:
1.  Define an m × n random matrix as a measurable map from a probability space `Ω` to
  the space of m × n matrices over α.
2.  Define a random matrix ensemble as a map (m : ℕ) → (n : ℕ) → `Ω` → {m × n random matrices}
3.  Using the above definitions, I would like to be able to:
  2. State and prove a lemma stating that the (i,j)-th entry is a random variable `Ω` → `α`
  3. Access the (m, n)-th matrix in a random matrix ensemble.
  4. Prove that the (m, n)-th matrix in an ensemble is a random matrix, i.e. a measurable map
      `Ω` → Matrix (Fin m) (Fin n)
  5. Prove that any nonnegative integer of a random matrix is a random matrix
  6. Prove that the trace of a random matrix is a random variable `Ω` → `α`



-/



/- An m × n random matrix is defined as a map from a `ProbabilitySpace Ω` to the m × n matrices. We
require that this map be measurable.

Here we follow the mathlib convention that a random variable is just a function from a
ProbabilitySpace to a MeasureSpace along with a proof that it is measurable.
We do not construct an extra structure or type for random matrices.-/
variable {Ω : Type*} [MeasurableSpace Ω] {rmtx : Ω → Matrix (Fin m) (Fin n) α}
  (hrmtx : Measurable rmtx)

/--A map from `Ω` to `Matrix (Fin m) (Fin n) α` is measurable if the corresponding map for each
entry is measurable.-/
@[fun_prop]
lemma measurable_matrix_map (m n : ℕ ) (X : Ω → Matrix (Fin m) (Fin n) α)
    (hmeas_entry : ∀ (i : Fin m) (j : Fin n), Measurable (fun ω ↦ X ω i j)) : Measurable X := by
  rw[measurable_pi_iff]
  intro i
  rw[measurable_pi_iff]
  intro j
  apply hmeas_entry

/-- For any i ≤ m and j ≤ n, The (i, j)-th entry of an m × n random matrix is a random variable.-/
lemma measurable_entry {m n : ℕ} (X : Ω → Matrix (Fin m) (Fin n) α) (hX : Measurable X) :
∀ (i : Fin m) (j : Fin n), Measurable (fun ω ↦ X ω i j) := by
  intros i j
  fun_prop

/-- Any natural number power of a random square matrix is also a random matrix. -/
@[fun_prop]
lemma matrix_measurable_pow {n : ℕ} (X : Ω → Matrix (Fin n) (Fin n) α) (hX : Measurable X)
    (k : ℕ) : Measurable (fun ω ↦ (X ω) ^ k) := by
  sorry

/-- The trace of a random square matrix is a random variable. -/
@[fun_prop]
lemma measurable_trace {n : ℕ} (X : Ω → Matrix (Fin n) (Fin n) α) (hX : Measurable X) :
  Measurable (fun ω ↦ (X ω).trace) := by
  unfold Matrix.trace
  unfold Matrix.diag
  apply Finset.measurable_sum
  intro i
  simp
  apply measurable_entry
  apply hX




/-Now I define a random matrix ensemble as a map ℕ → ℕ → {measurable maps from Ω to
Matrix (Fin m) (Fin n) α}, where m and n are the two inputs from ℕ.

Section still needs work. -/

/- I tried to make this not take in `Ω` and `α` as parameters, but I was getting some typeclass
errors. Not sure if this is the right way to do this.-/
def RandomMatrixEnsemble (Ω α : Type*) [MeasurableSpace Ω] [MeasurableSpace α] :=
  (m : ℕ) → (n : ℕ) → {f : Ω → Matrix (Fin m) (Fin n) α // Measurable f }


-- def RandomMatrixEnsemble :=
--   (m : ℕ) → (n : ℕ) → { f : Ω → Matrix (Fin m) (Fin n) α // Measurable f }

#check RandomMatrixEnsemble Ω α

variable  (X_ens : RandomMatrixEnsemble Ω α)

#check X_ens

-- 5 x 10 random matrix
def X_5_10 := X_ens 5 10

#check X_5_10
#print X_5_10



/-Here is an alternative approach to defining random matrices using by defining a RandomMatrix
structure. However this is not the convention in mathlib for random variables so we won't use it.-/

/-- An `m × n` random matrix is a measurable function from a `ProbabilitySpace Ω`
to the space of `m × n` matrices, bundled with its measurability proof. -/
structure RandomMatrix (Ω α : Type*) [MeasurableSpace Ω] [MeasurableSpace α] (m n : ℕ) where
  toFun : Ω → Matrix (Fin m) (Fin n) α
  measurable' : Measurable toFun

/-- An ensemble of random matrices, defined as a sequence of `RandomMatrix` structures
indexed by their dimensions. -/
def RandomMatrixEnsemble' (Ω α : Type*) [MeasurableSpace Ω] [MeasurableSpace α] :=
  (m n : ℕ) → RandomMatrix Ω α m n

#check RandomMatrixEnsemble'

end ProbabilityTheory
