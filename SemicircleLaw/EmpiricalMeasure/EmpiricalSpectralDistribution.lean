import SemicircleLaw.EmpiricalMeasure.EigenvalueContinuity
import SemicircleLaw.EmpiricalMeasure.RandomProbabilityMeasure
import SemicircleLaw.Experiments.WignerMatrix
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Empirical spectral distribution of a random real symmetric (e.g. Wigner) matrix

For a random matrix `X : Ω → Matrix (Fin n) (Fin n) ℝ` all of whose realizations are real
symmetric, every `X w` has `n` real eigenvalues, which we order decreasingly
`λ₁(X w) ≥ λ₂(X w) ≥ ⋯ ≥ λₙ(X w)` (in Lean, `0`-based: `CourantFischer.eigenvaluesDesc`).
The empirical spectral distribution is `μ_X(B, w) := (1/n) ∑ⱼ δ_{λⱼ(X w)}(B)`.

A Wigner matrix is in particular such a random symmetric matrix (with measurable entries);
the empirical spectral distribution only uses the symmetry of the realizations, and its
measurability in `w` only uses the measurability of the entries, so we work in that generality.

Main result: `RandomSymmMatrix.esd_isRandomProbabilityMeasure` — the esd is a random
probability measure in the sense of `RandomMeasure.IsRandomProbabilityMeasure`.
-/

open MeasureTheory CourantFischer EigenvalueContinuity
open scoped ENNReal

namespace RandomMatrix

/-- The Dirac measure `δ_s` on a measurable space `(S, 𝒮)` satisfies `δ_s(B) = 𝟏_B(s)`. -/
theorem dirac_apply_eq_indicator {S : Type*} [MeasurableSpace S] (s : S) {B : Set S}
    (hB : MeasurableSet B) : Measure.dirac s B = B.indicator 1 s :=
  Measure.dirac_apply' s hB

/-- The Dirac measure is a probability measure. -/
example {S : Type*} [MeasurableSpace S] (s : S) : IsProbabilityMeasure (Measure.dirac s) :=
  inferInstance

/-- A random real symmetric `n × n` matrix on a sample space `Ω`: a map `w ↦ X w` such that every
realization `X w ∈ M_{n×n}(ℝ)` is symmetric. A Wigner matrix is an instance of this. -/
structure RandomSymmMatrix (Ω : Type*) (n : ℕ) where
  /-- The realization `X(w)` of the random matrix at the sample point `w`. -/
  toFun : Ω → Matrix (Fin n) (Fin n) ℝ
  /-- Every realization is real symmetric. -/
  isSymm : ∀ w, (toFun w).IsSymm

namespace RandomSymmMatrix

variable {Ω : Type*} {n : ℕ}

instance : CoeFun (RandomSymmMatrix Ω n) (fun _ => Ω → Matrix (Fin n) (Fin n) ℝ) :=
  ⟨RandomSymmMatrix.toFun⟩

/-- A real symmetric matrix is Hermitian. -/
theorem isHermitian (X : RandomSymmMatrix Ω n) (w : Ω) : (X w).IsHermitian := by
  simpa [Matrix.IsHermitian, Matrix.conjTranspose] using X.isSymm w

/-- The eigenvalues `λ₁(X w) ≥ ⋯ ≥ λₙ(X w)` of the realization `X w`, listed in decreasing
order (`j = 0, …, n-1` corresponds to `λ₁, …, λₙ`). -/
noncomputable def eigenvalue (X : RandomSymmMatrix Ω n) (w : Ω) (j : Fin n) : ℝ :=
  eigenvaluesDesc (X.isSymm w) j

/-- The eigenvalues are ordered decreasingly: `λ₁(X w) ≥ λ₂(X w) ≥ ⋯ ≥ λₙ(X w)`. -/
theorem eigenvalue_antitone (X : RandomSymmMatrix Ω n) (w : Ω) : Antitone (X.eigenvalue w) :=
  eigenvaluesDesc_antitone (X.isSymm w)

/-- The sorted eigenvalues do not depend on the chosen dimension witness. -/
private lemma eigenvalues_cast {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {T : E →ₗ[ℝ] E} (hT : T.IsSymmetric) {m m' : ℕ} (h : m = m')
    (hm : Module.finrank ℝ E = m) (hm' : Module.finrank ℝ E = m') (i : Fin m) :
    hT.eigenvalues hm' (Fin.cast h i) = hT.eigenvalues hm i := by
  subst h; rfl

/-- `eigenvaluesDesc` agrees with Mathlib's sorted eigenvalues `eigenvalues₀`. -/
lemma eigenvalue_eq_eigenvalues₀ (X : RandomSymmMatrix Ω n) (w : Ω) (j : Fin n) :
    X.eigenvalue w j = (X.isHermitian w).eigenvalues₀ (Fin.cast (Fintype.card_fin n).symm j) :=
  (eigenvalues_cast _ _ _ _ j).symm

/-- The `λⱼ(X w)` are exactly the `n` (real) eigenvalues of `X w`, counted with multiplicity:
the characteristic polynomial of `X w` has roots `λ₁(X w), …, λₙ(X w)`. -/
theorem charpoly_roots (X : RandomSymmMatrix Ω n) (w : Ω) :
    (X w).charpoly.roots = Multiset.map (fun j => X.eigenvalue w j) Finset.univ.val := by
  simp_rw [eigenvalue_eq_eigenvalues₀]
  rw [(X.isHermitian w).roots_charpoly_eq_eigenvalues₀, Fin.univ_val_map, Fin.univ_val_map]
  congr 1
  exact (List.ofFn_congr (Fintype.card_fin n) _).trans rfl

/-- The **empirical spectral distribution** of `X`:
`μ_X(·, w) := (1/n) ∑_{j=1}^n δ_{λⱼ(X w)}`, a (random) measure on `(ℝ, 𝓑(ℝ))`. -/
noncomputable def esd (X : RandomSymmMatrix Ω n) (w : Ω) : Measure ℝ :=
  (n : ℝ≥0∞)⁻¹ • ∑ j : Fin n, Measure.dirac (X.eigenvalue w j)

/-- Defining formula: `μ_X(B, w) = (1/n) ∑ⱼ δ_{λⱼ(X w)}(B) = (1/n) ∑ⱼ 𝟏_B(λⱼ(X w))`. -/
theorem esd_apply (X : RandomSymmMatrix Ω n) (w : Ω) (B : Set ℝ) :
    X.esd w B = (n : ℝ≥0∞)⁻¹ * ∑ j : Fin n, B.indicator 1 (X.eigenvalue w j) := by
  simp [esd, Measure.coe_finset_sum, Finset.sum_apply, Measure.dirac_apply]

/-- (i) For `n ≥ 1`, `μ_X(·, w)` is a probability measure for every `w`:
`μ_X(ℝ, w) = (1/n) · n = 1`. -/
instance isProbabilityMeasure_esd [NeZero n] (X : RandomSymmMatrix Ω n) (w : Ω) :
    IsProbabilityMeasure (X.esd w) := by
  constructor
  rw [esd_apply]
  simp only [Set.indicator_univ, Pi.one_apply, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  exact ENNReal.inv_mul_cancel (by simp [NeZero.ne n]) (by simp)

/-- `μ_X : 𝓑(ℝ) × Ω → [0,1]`: for `n ≥ 1` every value lies in `[0,1]`. -/
theorem esd_apply_le_one [NeZero n] (X : RandomSymmMatrix Ω n) (w : Ω) (B : Set ℝ) :
    X.esd w B ≤ 1 :=
  prob_le_one

/-- The empirical spectral distribution bundled as a map `Ω → ProbabilityMeasure ℝ`
(for `n ≥ 1`). -/
noncomputable def esdProb [NeZero n] (X : RandomSymmMatrix Ω n) (w : Ω) : ProbabilityMeasure ℝ :=
  ⟨X.esd w, inferInstance⟩

section Measurability

variable [MeasurableSpace Ω]

/-- The product σ-algebra on `M_{n×n}(ℝ)` (the Borel σ-algebra of the entrywise topology). -/
local instance matrixMeasurableSpace : MeasurableSpace (Matrix (Fin n) (Fin n) ℝ) :=
  MeasurableSpace.pi

local instance matrixBorelSpace : BorelSpace (Matrix (Fin n) (Fin n) ℝ) := Pi.borelSpace

/-- If all entries `w ↦ X w i j` are random variables, then each ordered eigenvalue
`w ↦ λⱼ(X w)` is a random variable: it is `λⱼ ∘ X` with `λⱼ` continuous on `Sym_n(ℝ)`. -/
theorem measurable_eigenvalue (X : RandomSymmMatrix Ω n)
    (hX : ∀ i k, Measurable (fun w => X w i k)) (j : Fin n) :
    Measurable (fun w => X.eigenvalue w j) := by
  have hXm : Measurable (X : Ω → Matrix (Fin n) (Fin n) ℝ) :=
    measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun k => hX i k
  have hS : Measurable (fun w => (⟨X w, X.isSymm w⟩ : SymMat n)) := hXm.subtype_mk
  have hc : Measurable (eigenvalueMap (n := n) j) := (continuous_eigenvalueMap j).measurable
  have h : (fun w => X.eigenvalue w j) = eigenvalueMap j ∘ (fun w => ⟨X w, X.isSymm w⟩) := by
    funext w; simp only [Function.comp_apply, eigenvalueMap, eigenvalue]
  rw [h]
  exact hc.comp hS

/-- (ii) For every Borel set `B`, `w ↦ μ_X(B, w) = (1/n) ∑ⱼ (𝟏_B ∘ λⱼ ∘ X)(w)` is measurable. -/
theorem measurable_esd_apply (X : RandomSymmMatrix Ω n)
    (hX : ∀ i k, Measurable (fun w => X w i k)) {B : Set ℝ} (hB : MeasurableSet B) :
    Measurable (fun w => X.esd w B) := by
  simp_rw [esd_apply]
  refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
  exact (measurable_one.indicator hB).comp (X.measurable_eigenvalue hX j)

/-- The esd as a map `μ_X : 𝓑(ℝ) × Ω → [0,1]` (curried), in the format of
`RandomMeasure.IsRandomProbabilityMeasure`. -/
noncomputable def esdUnit [NeZero n] (X : RandomSymmMatrix Ω n)
    (B : {B : Set ℝ // MeasurableSet B}) (w : Ω) : unitInterval :=
  ⟨(X.esd w B.1).toReal, ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using X.esd_apply_le_one w B.1)⟩

/-- **The esd `μ_X` is a random probability measure on `ℝ`.** For `n ≥ 1` and a random
symmetric matrix `X` (e.g. a Wigner matrix) whose entries are random variables on the probability
space `(Ω, 𝓕, ℙ)`:
(i) for every `w`, `B ↦ μ_X(B, w)` is a probability measure (namely `X.esd w`);
(ii) for every Borel set `B`, `w ↦ μ_X(B, w)` is measurable. -/
theorem esd_isRandomProbabilityMeasure [NeZero n] (X : RandomSymmMatrix Ω n)
    (hX : ∀ i k, Measurable (fun w => X w i k)) (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] :
    RandomMeasure.IsRandomProbabilityMeasure ℝ ℙ X.esdUnit where
  ae_isProbabilityMeasure := Filter.Eventually.of_forall fun w =>
    ⟨X.esd w, inferInstance, fun B => by simp [esdUnit, measure_ne_top]⟩
  measurable_apply := fun B =>
    ((X.measurable_esd_apply hX B.2).ennreal_toReal).subtype_mk

end Measurability

/-! ## Wigner matrices -/

section Wigner

open RandomMatrixTheory

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {X : (n : ℕ) → Ω → Matrix (Fin n) (Fin n) ℝ}

/-- The `n`-th member `𝐗ₙ` of a sequence of Wigner matrices, as a random symmetric matrix. -/
def ofWigner (hX : IsWignerMatrixSeq P X) (n : ℕ) : RandomSymmMatrix Ω n :=
  ⟨X n, (hX.isRandomMatrix_isSymm n).2⟩

/-- **The esd of a Wigner matrix is a random probability measure** (explicit form). For a
sequence of Wigner matrices `(𝐗ₙ)` and `n ≥ 1`:
(i) for every `w`, `μ_{𝐗ₙ}(·, w)` is a probability measure on `𝓑(ℝ)`;
(ii) for every Borel set `B`, `w ↦ μ_{𝐗ₙ}(B, w)` is measurable. -/
theorem wigner_esd_isProbabilityMeasure_and_measurable (hX : IsWignerMatrixSeq P X) (n : ℕ)
    [NeZero n] :
    (∀ w, IsProbabilityMeasure ((ofWigner hX n).esd w)) ∧
      ∀ B : Set ℝ, MeasurableSet B → Measurable (fun w => (ofWigner hX n).esd w B) :=
  ⟨fun _ => inferInstance, fun _ hB =>
    (ofWigner hX n).measurable_esd_apply (hX.isRandomMatrix_isSymm n).1 hB⟩

/-- **The esd of a Wigner matrix is a random probability measure**, in the sense of
`RandomMeasure.IsRandomProbabilityMeasure`. -/
theorem wigner_esd_isRandomProbabilityMeasure (hX : IsWignerMatrixSeq P X) (n : ℕ)
    [NeZero n] :
    RandomMeasure.IsRandomProbabilityMeasure ℝ P (ofWigner hX n).esdUnit :=
  (ofWigner hX n).esd_isRandomProbabilityMeasure (hX.isRandomMatrix_isSymm n).1 P

end Wigner

end RandomSymmMatrix

end RandomMatrix
