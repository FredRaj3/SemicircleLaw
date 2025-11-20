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
import Mathlib.Topology.Filter
import Mathlib.Order.Filter.Defs
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Sym.Sym2

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

open MeasureTheory ProbabilityTheory Filter Topology

variable {n : ℕ}
variable (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (hμ_moments : ∀ (k : ℕ), Integrable (fun x ↦ x^k) μ)
  (hν_moments : ∀ (k : ℕ), Integrable (fun x ↦ x^k) ν)
  (hμ_mean : integral μ id = 0) (hν_mean : integral ν id = 0)
  (hμ_var : integral μ (fun x ↦ x^2) = 1)
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (X : Ω → Matrix (Fin n) (Fin n) ℝ)


instance : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ ) := by
   unfold Matrix; infer_instance

@[ext]
structure isWignerMatrix
    (k : ℕ) (μ ν : Measure ℝ) (X : Ω → Matrix (Fin k) (Fin k) ℝ) (P : Measure Ω) where
  meas : Measurable X
  diag_dist : ∀ i : (Fin k), HasLaw (fun ω ↦ X ω i i) ν P
  off_diag_dist : ∀ i j : (Fin k), i > j → HasLaw (fun ω ↦ X ω i j) μ P
  symm : ∀ i j : (Fin k), ∀ ω : Ω, X ω i j = X ω j i
  indep : iIndepFun (fun (x : {p : Fin k × Fin k // p.1 ≤ p.2}) ↦ fun ω ↦ X ω x.val.1 x.val.2) P

#check isWignerMatrix

@[simp]
lemma is_measurable_Wigner (Y : isWignerMatrix n μ ν X P) : Measurable X := by
  exact Y.meas

/-- The index set for the independent random variables of a Wigner matrix. -/
def Index (n : ℕ) := { p : Fin n × Fin n // p.1 ≤ p.2 }

instance : Fintype (Index n) := by
  rw[Index]
  infer_instance

@[simp]
lemma off_diagonal_law (Y : isWignerMatrix n μ ν X P) (i j : Fin n) (hij : i ≠ j) :
  HasLaw (fun ω ↦ X ω i j) μ P:= by
  -- Since $i \neq j$, we have either $i < j$ or $j < i$. We can handle these cases separately using the off_diag_dist and the symmetry of the Wigner matrix.
  by_cases h : j < i;
  · -- Since $j < i$, we can apply the off_diag_dist condition directly.
    apply Y.off_diag_dist i j h
    all_goals unreachable!;
  · -- Since $i < j$, we can apply the off_diag_dist hypothesis with $i$ and $j$ swapped.
    have h_swap : HasLaw (fun ω ↦ X ω j i) μ P := by
      cases lt_or_gt_of_ne hij <;> aesop
      generalize_proofs at *;
      have := Y.off_diag_dist j i h_1; aesop;
    generalize_proofs at *;
    -- Since $X$ is symmetric, we have $X i j = X j i$.
    have h_symm : ∀ ω, X ω i j = X ω j i := by
      -- By the symmetry of the Wigner matrix, we have $X i j = X j i$ for all $i$ and $j$.
      intros ω; exact Y.symm i j ω
    generalize_proofs at *;
    aesop;

@[simp]
lemma diagonal_law (Y : isWignerMatrix n μ ν X P) (i : Fin n) : HasLaw (fun ω ↦ X ω i i) ν P:= by
   apply Y.diag_dist i

@[simp]
lemma symmetric (Y : isWignerMatrix n μ ν X P) : ∀ (ω : Ω), (X ω).IsSymm := by
  intro ω
  apply Matrix.IsSymm.ext
  intros i j
  apply Y.symm

@[simp]
lemma indep_entries (Y : isWignerMatrix n μ ν X P) (i j k l : Fin n) (hdiff : Sym2.mk (i,j) ≠ Sym2.mk (k,l)) :
    IndepFun (fun ω ↦ X ω i j) (fun ω ↦ X ω k l) P := by
  -- Define the projections from the Wigner matrix to its entries.
  let proj : {p : Fin n × Fin n // p.1 ≤ p.2} → Ω → ℝ := fun p ↦ (fun ω ↦ X ω p.val.1 p.val.2);
  -- By definition of Y.indep, the projections proj are independent.
  have h_indep : iIndepFun (fun (p : {p : Fin n × Fin n // p.1 ≤ p.2}) ↦ proj p) P := by
    -- Apply the hypothesis that the projections are independent.
    apply Y.indep;
  -- By definition of proj, we have that (fun ω => X ω i j) = proj ⟨(i, j), by sorry⟩ and (fun ω => X ω k l) = proj ⟨(k, l), by sorry⟩.
  have h_eq_proj : (fun ω => X ω i j) = proj ⟨(min i j, max i j), by
    exact min_le_max⟩ ∧ (fun ω => X ω k l) = proj ⟨(min k l, max k l), by
    exact min_le_max⟩ := by
    simp +zetaDelta at *;
    generalize_proofs at *;
    cases le_total i j <;> cases le_total k l <;> simp +decide [ * ];
    · exact funext fun ω => Y.symm k l ω ▸ rfl;
    · exact funext fun ω => by simpa [ eq_comm ] using Y.symm j i ω;
    · exact ⟨ funext fun ω => Y.symm _ _ _, funext fun ω => Y.symm _ _ _ ⟩
  generalize_proofs at *;
  rw [ h_eq_proj.1, h_eq_proj.2 ];
  apply_rules [ ProbabilityTheory.iIndepFun.indepFun ];
  cases le_total i j <;> cases le_total k l <;> aesop


/-

What I would like to do:

For each n, have a probability space Ω n with some measure P.
On Ω n under P, we have n(n+1)/2 independent random variables. n of them have law
μ, and n(n-1)/2 of them have law ν. I would then like to include them into
a matrix such that the strict upper triangular entries are those random variables
with law μ, the diagonal random variables have law ν, and the lower trianglular
 entries are such that the matrix is symmetric.

I would like to have the following lemmas. If X : Ω n → Matrix (Fin n) (Fin n) is
the matrix constructed above,

lemma has_law_diag (i j : Fin n) (hij : i = j): HasLaw (fun ω ↦ X ω i j) ν P

lemma has_law_off_diag (i j : Fin n) (hij : i ≠ j) : HasLaw (fun ω ↦ X ω i j) μ P

lemma symmetric_entries (i j : Fin n) (ω : Ω): X ω i j = X ω j i

lemma ident_distrib_diag (i j k l: Fin n) (hij : i = j) (hkl : k = l) :
    IdentDistrib (fun ω ↦ X ω i j) (fun ω ↦ X ω k l) P P

lemma ident_distrib_off_diag (i j k l: Fin n) (hij : i ≠ j) (hkl : k ≠ l) :
    IdentDistrib (fun ω ↦ X ω i j) (fun ω ↦ X ω k l) P P

lemma indep_entries ... :
    iIndepFun ...

lemma indep_entries_pair ... :
    IndepFun ...


-/


/-- The sample space for an `n x n` Wigner matrix. It is the product of ℝ over Index n. -/
abbrev WignerSpace (n : ℕ) := Index n → ℝ

instance (n : ℕ) : MeasurableSpace (WignerSpace n) := by
  infer_instance

/-- The measure distribution for a Wigner matrix. It assigns the measure `ν` to diagonal
entries and `μ` to off-diagonal entries. -/
def wignerMeasureDist (n : ℕ) : Index n → Measure ℝ :=
  fun (p : Index n) =>
    if p.val.1 = p.val.2 then ν
    else μ


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

/-- The function that takes an element of WignerSpace (a map Index n → ℝ)
to the corresponding function (Fin n) → (Fin n) → ℝ that respects the symmetric structure of Wigner
matrices.-/
@[grind, simp]
def wignerMatrixEntryFunction (ω : WignerSpace n) : (Fin n) → (Fin n) → ℝ :=
  fun i j =>
    if h_eq : i = j then
      ω (⟨(i, i), le_refl i⟩)
    else if h_lt : i < j then
      ω (⟨(i, j), le_of_lt h_lt⟩)
    else
      have h_gt : j < i := by
         apply lt_of_le_of_ne
         apply le_of_not_gt h_lt
         grind
      ω (⟨(j, i), le_of_lt h_gt⟩)


lemma wignerMatrixEntryFunctionSymmetric (ω : WignerSpace n) {i : Fin n} {j : Fin n} :
  wignerMatrixEntryFunction ω i j = wignerMatrixEntryFunction ω j i := by
  rw[wignerMatrixEntryFunction, wignerMatrixEntryFunction]

  sorry

def wignerMatrixMap' (ω : WignerSpace n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (wignerMatrixEntryFunction ω)

/-- A wigner matrix is defined as a matrix valued random variable.-/
noncomputable
def wignerMatrixMap (n : ℕ) : (WignerSpace n) → Matrix (Fin n) (Fin n) ℝ :=
  fun (ω : WignerSpace n) ↦ (wignerMatrixMap' ω)

/-- A wigner matrix is defined as a matrix valued random variable, rescaled by 1/√n.-/
noncomputable
def wignerMatrixMapScaled (n : ℕ) : (WignerSpace n) → Matrix (Fin n) (Fin n) ℝ :=
  fun (ω : WignerSpace n) ↦ (1 / Real.sqrt (n : ℝ)) • (wignerMatrixMap' ω)

/--For any `(n : ℕ)` the map `wignerMatrixMap` is measurable from `WignerSpace n` to
  `Matrix (Fin n) (Fin n) ℝ`-/
@[fun_prop]
lemma wignerMatrixMapMeasurable (n : ℕ) : Measurable (wignerMatrixMap n) := by
  sorry


/--For any `(n : ℕ)` the map `wignerMatrixMapScaled` is measurable from `WignerSpace n` to
  `Matrix (Fin n) (Fin n) ℝ`-/
@[fun_prop]
lemma wignerMatrixMapScaledMeasurable (n : ℕ) : Measurable (wignerMatrixMapScaled n) := by
  sorry

/--For any `(n : ℕ)` the map `wignerMatrixMap` is `AEMeasurable` from `WignerSpace n` to
  `Matrix (Fin n) (Fin n) ℝ`-/
@[fun_prop]
lemma wignerMatrixMapAEMeasurable (n : ℕ) : AEMeasurable (wignerMatrixMap n) := by
  fun_prop

/--For any `(n : ℕ)` the map `wignerMatrixMap` is `AEMeasurable` from `WignerSpace n` to
  `Matrix (Fin n) (Fin n) ℝ`-/
@[fun_prop]
lemma wignerMatrixMapScaledAEMeasurable (n : ℕ) : AEMeasurable (wignerMatrixMapScaled n) := by
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

lemma wignerMatrixSymmetric (n : ℕ) ( i j : Fin n) {ω : WignerSpace n} :
  wignerMatrixMap n ω i j = wignerMatrixMap n ω j i := by
  rw[wignerMatrixMap]
  rw[wignerMatrixMap']
  simp
  sorry


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

@[fun_prop]
lemma wignerMatrixScaledPowMeasurable (n : ℕ) (k : ℕ) :
    Measurable (fun ω ↦ ((wignerMatrixMapScaled n ω)^k)) := by
  apply matrix_measurable_pow
  apply wignerMatrixMapScaledMeasurable

variable {ω : WignerSpace n}
variable {k : ℕ}
#check ((wignerMatrixMap n ω)^k).trace

noncomputable
def wignerMatrixTracePower (n : ℕ) (k : ℕ) : (WignerSpace n) → ℝ :=
  fun ω ↦ ((wignerMatrixMap n ω)^k).trace

noncomputable
def wignerMatrixScaledTracePower (n : ℕ) (k : ℕ) : (WignerSpace n) → ℝ :=
  fun ω ↦ ((wignerMatrixMapScaled n ω)^k).trace

/-- The map that sends a Wigner Matrix to the trace of its kth power is measurable.-/
@[fun_prop]
lemma wignerMatrixTracePowerMeasurable (n : ℕ) (k : ℕ) :
    Measurable (wignerMatrixTracePower n k) := by
  apply measurable_trace
  apply wignerMatrixPowMeasurable

  /-- The map that sends a Wigner Matrix to the trace of its kth power is measurable.-/
@[fun_prop]
lemma wignerMatrixScaledTracePowerMeasurable (n : ℕ) (k : ℕ) :
    Measurable (wignerMatrixScaledTracePower n k) := by
  apply measurable_trace
  apply wignerMatrixScaledPowMeasurable

/--The sequence of expectations of the trace of the kth power of an n × n Wigner matrix.-/
noncomputable
def wignerMatrixTracePowerSequence (k : ℕ) : ℕ → ℝ :=
  fun n ↦ (WignerMeasure μ ν n)[wignerMatrixTracePower n k]

/--The sequence of expectations of the trace of the kth power of an n × n Wigner matrix.-/
noncomputable
def wignerMatrixScaledTracePowerSequence (k : ℕ) : ℕ → ℝ :=
  fun n ↦ (WignerMeasure μ ν n)[(1 / (n : ℝ)) • wignerMatrixScaledTracePower n k]

/--For any odd k, the expectation of the scaled trace of the kth power of a Wigner matrix tends
to 0.-/
theorem wignerMatrixMomentOddExpectation (n : ℕ) (k : ℕ) (hk : Odd k) :
  Tendsto (wignerMatrixScaledTracePowerSequence μ ν k) atTop (𝓝 (0 : ℝ)) := by
  sorry

/--For any even k, the expectation of the scaled trace of the kth power of a Wigner matrix tends
to `catalan (k/2)`.-/
theorem wignerMatrixMomentEvenExpectationLimit (k : ℕ) (hk : Even k) :
  Tendsto (wignerMatrixScaledTracePowerSequence μ ν k) atTop (𝓝 (catalan (k/2) : ℝ)) := by
  sorry

/--For a fixed k, the ℝ-valued sequence of scaled variance of traces of the kth power of a Wigner
matrix.-/
noncomputable
def wignerMatrixScaledTracePowerSeqVar (k : ℕ) : ℕ → ℝ :=
  fun n ↦ variance ((1/ (n: ℝ)) • wignerMatrixScaledTracePower n k) (WignerMeasure μ ν n)

/--For any k, the variance of the scaled trace of the kth power of a Wigner matrix tends to 0.-/
theorem wignerMatrixMomentsVarianceLimit (k : ℕ) :
  Tendsto (wignerMatrixScaledTracePowerSeqVar μ ν k) atTop (𝓝 (0 : ℝ)) := by
  sorry

/-NOTE: We will need a separate statement that actually gives the rate of convergence. I'm not sure
what the best way to do this yet is, but I will add it later. This should be enough for now to prove
the semiricle law for matrix moments though.-/
