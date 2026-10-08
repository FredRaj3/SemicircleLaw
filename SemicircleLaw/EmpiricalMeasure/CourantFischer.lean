import Mathlib

/-!
# The Courant–Fischer min-max theorem

Throughout, `A` is a real symmetric `n × n` matrix, viewed as a linear operator on the
Euclidean space `ℝⁿ = EuclideanSpace ℝ (Fin n)`.  Eigenvalues are listed in *decreasing* order
`λ₀ ≥ λ₁ ≥ ⋯ ≥ λₙ₋₁` (indices are `0`-based, so `eigenvaluesDesc hA j` is the `(j+1)`-st
largest eigenvalue `λ_{j+1}(A)` of the informal statement).
-/

open Module

namespace CourantFischer

variable {n : ℕ}

/-- The real symmetric matrix `A`, viewed as a linear operator `x ↦ A x` on `ℝⁿ`. -/
noncomputable abbrev op (A : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  Matrix.toEuclideanLin A

/-- The **Rayleigh quotient** `R_A(x) = ⟪x, A x⟫ / ‖x‖²`. -/
noncomputable def rayleighQuotient (A : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  inner ℝ x (op A x) / ‖x‖ ^ 2

lemma isSymmetric_op {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) : (op A).IsSymmetric := by
  apply Matrix.isHermitian_iff_isSymmetric.1
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- The eigenvalues `λ₀(A) ≥ λ₁(A) ≥ ⋯ ≥ λₙ₋₁(A)` of a real symmetric matrix,
in decreasing order (real spectral theorem). -/
noncomputable def eigenvaluesDesc {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) : Fin n → ℝ :=
  (isSymmetric_op hA).eigenvalues finrank_euclideanSpace_fin

/-- An orthonormal eigenbasis `v₀, …, vₙ₋₁` with `A vᵢ = λᵢ(A) vᵢ`. -/
noncomputable def eigenbasis {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm) :
    OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) :=
  (isSymmetric_op hA).eigenvectorBasis finrank_euclideanSpace_fin

variable {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsSymm)

theorem eigenvaluesDesc_antitone : Antitone (eigenvaluesDesc hA) :=
  (isSymmetric_op hA).eigenvalues_antitone _

theorem op_eigenbasis (i : Fin n) :
    op A (eigenbasis hA i) = eigenvaluesDesc hA i • eigenbasis hA i := by
  have := (isSymmetric_op hA).apply_eigenvectorBasis finrank_euclideanSpace_fin i
  simp [eigenbasis, eigenvaluesDesc]

/-- `⟪x, A x⟫ = ∑ᵢ λᵢ cᵢ²`, where `cᵢ` are the coordinates of `x` in the eigenbasis. -/
lemma inner_op_eq_sum (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (op A x) =
      ∑ i, eigenvaluesDesc hA i * ((eigenbasis hA).repr x i) ^ 2 := by
  have h : ∀ i, (eigenbasis hA).repr (op A x) i =
      eigenvaluesDesc hA i * (eigenbasis hA).repr x i := fun i =>
    (isSymmetric_op hA).eigenvectorBasis_apply_self_apply _ x i
  rw [← (eigenbasis hA).repr.inner_map_map x (op A x), PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

/-- `‖x‖² = ∑ᵢ cᵢ²`. -/
lemma norm_sq_eq_sum (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ i, ((eigenbasis hA).repr x i) ^ 2 := by
  rw [← (eigenbasis hA).repr.norm_map, EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The span `W = span{v_j, …, v_{n-1}}` of the eigenvectors with index `≥ j`. -/
noncomputable def tailSpan (j : Fin n) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun k : {k : Fin n // j ≤ k} => eigenbasis hA k)

/-- The span `S₀ = span{v_0, …, v_j}` of the eigenvectors with index `≤ j`. -/
noncomputable def headSpan (j : Fin n) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) :=
  Submodule.span ℝ (Set.range fun k : {k : Fin n // k ≤ j} => eigenbasis hA k)

lemma finrank_tailSpan (j : Fin n) : finrank ℝ (tailSpan hA j) = n - j := by
  rw [tailSpan, finrank_span_eq_card (b := fun k : {k : Fin n // j ≤ k} => eigenbasis hA k)
    ((eigenbasis hA).orthonormal.linearIndependent.comp Subtype.val Subtype.val_injective),
    Fintype.card_subtype]
  have : (Finset.univ.filter (fun k : Fin n => j ≤ k)) = Finset.Ici j := by ext; simp
  rw [this, Fin.card_Ici]

lemma finrank_headSpan (j : Fin n) : finrank ℝ (headSpan hA j) = j + 1 := by
  rw [headSpan, finrank_span_eq_card (b := fun k : {k : Fin n // k ≤ j} => eigenbasis hA k)
    ((eigenbasis hA).orthonormal.linearIndependent.comp Subtype.val Subtype.val_injective),
    Fintype.card_subtype]
  have : (Finset.univ.filter (fun k : Fin n => k ≤ j)) = Finset.Iic j := by ext; simp
  rw [this, Fin.card_Iic]

lemma repr_eq_zero_of_mem_tailSpan {j : Fin n} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ tailSpan hA j) {i : Fin n} (hi : i < j) : (eigenbasis hA).repr x i = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    have hik : i ≠ k := fun h => absurd hk (by rw [← h]; exact not_le.2 hi)
    simp [hik]
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]

lemma repr_eq_zero_of_mem_headSpan {j : Fin n} {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ headSpan hA j) {i : Fin n} (hi : j < i) : (eigenbasis hA).repr x i = 0 := by
  rw [OrthonormalBasis.repr_apply_apply]
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨k, hk⟩, rfl⟩ := hy
    have hik : i ≠ k := fun h => absurd hk (by rw [← h]; exact not_le.2 hi)
    simp [hik]
  | zero => simp
  | add y z _ _ hy hz => rw [inner_add_right, hy, hz, add_zero]
  | smul a y _ hy => rw [inner_smul_right, hy, mul_zero]

/-- If the coordinates `cᵢ` of a unit vector `x` vanish for `i < j`, then `⟪x, A x⟫ ≤ λⱼ`. -/
lemma inner_op_le_of_repr_eq_zero {j : Fin n} {x : EuclideanSpace ℝ (Fin n)}
    (h0 : ∀ i < j, (eigenbasis hA).repr x i = 0) (hx1 : ‖x‖ = 1) :
    inner ℝ x (op A x) ≤ eigenvaluesDesc hA j := by
  have hsum := norm_sq_eq_sum hA x
  rw [hx1, one_pow] at hsum
  rw [inner_op_eq_sum hA, ← mul_one (eigenvaluesDesc hA j), hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases lt_or_ge i j with hij | hij
  · simp [h0 i hij]
  · exact mul_le_mul_of_nonneg_right (eigenvaluesDesc_antitone hA hij) (sq_nonneg _)

/-- If the coordinates `cᵢ` of a unit vector `x` vanish for `i > j`, then `λⱼ ≤ ⟪x, A x⟫`. -/
lemma le_inner_op_of_repr_eq_zero {j : Fin n} {x : EuclideanSpace ℝ (Fin n)}
    (h0 : ∀ i, j < i → (eigenbasis hA).repr x i = 0) (hx1 : ‖x‖ = 1) :
    eigenvaluesDesc hA j ≤ inner ℝ x (op A x) := by
  have hsum := norm_sq_eq_sum hA x
  rw [hx1, one_pow] at hsum
  rw [inner_op_eq_sum hA, ← mul_one (eigenvaluesDesc hA j), hsum, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rcases lt_or_ge j i with hij | hij
  · simp [h0 i hij]
  · exact mul_le_mul_of_nonneg_right (eigenvaluesDesc_antitone hA hij) (sq_nonneg _)

/-- Step (i:≥): every `(j+1)`-dimensional subspace contains a unit vector `x`
with `⟪x, A x⟫ ≤ λⱼ`. -/
theorem exists_unit_inner_le (j : Fin n) (S : Submodule ℝ (EuclideanSpace ℝ (Fin n)))
    (hS : finrank ℝ S = j + 1) :
    ∃ x ∈ S, ‖x‖ = 1 ∧ inner ℝ x (op A x) ≤ eigenvaluesDesc hA j := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (tailSpan hA j)
  have h2 : finrank ℝ ↥(S ⊔ tailSpan hA j) ≤ n :=
    (Submodule.finrank_le _).trans_eq finrank_euclideanSpace_fin
  have hne : S ⊓ tailSpan hA j ≠ ⊥ := by
    intro h
    rw [h, finrank_bot, hS, finrank_tailSpan] at h1
    have := j.isLt
    omega
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxW : ‖y‖⁻¹ • y ∈ tailSpan hA j := Submodule.smul_mem _ _ hy.2
  have hx1 : ‖‖y‖⁻¹ • y‖ = 1 := by simpa using norm_smul_inv_norm (𝕜 := ℝ) hy0
  exact ⟨‖y‖⁻¹ • y, S.smul_mem _ hy.1, hx1, inner_op_le_of_repr_eq_zero hA
    (fun i hi => repr_eq_zero_of_mem_tailSpan hA hxW hi) hx1⟩

/-- Step (i:≤): on `S₀ = span{v₀, …, vⱼ}`, every unit vector satisfies `λⱼ ≤ ⟪x, A x⟫`. -/
theorem le_inner_of_mem_headSpan (j : Fin n) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ headSpan hA j) (hx1 : ‖x‖ = 1) :
    eigenvaluesDesc hA j ≤ inner ℝ x (op A x) :=
  le_inner_op_of_repr_eq_zero hA (fun _ hi => repr_eq_zero_of_mem_headSpan hA hx hi) hx1

lemma inner_op_eigenbasis (j : Fin n) :
    inner ℝ (eigenbasis hA j) (op A (eigenbasis hA j)) = eigenvaluesDesc hA j := by
  rw [op_eigenbasis, inner_smul_right, real_inner_self_eq_norm_sq,
    (eigenbasis hA).norm_eq_one, one_pow, mul_one]

/-- **Courant–Fischer theorem.** For a real symmetric matrix `A` and each index `j`
(`0`-based), the `(j+1)`-st largest eigenvalue is
`λⱼ(A) = max_{dim S = j+1} min_{x ∈ S, ‖x‖ = 1} ⟪x, A x⟫`,
where both the maximum and the minimum are attained. -/
theorem courant_fischer (j : Fin n) :
    IsGreatest
      {m : ℝ | ∃ S : Submodule ℝ (EuclideanSpace ℝ (Fin n)), finrank ℝ S = j + 1 ∧
        IsLeast {r : ℝ | ∃ x ∈ S, ‖x‖ = 1 ∧ r = inner ℝ x (op A x)} m}
      (eigenvaluesDesc hA j) := by
  constructor
  · refine ⟨headSpan hA j, finrank_headSpan hA j, ⟨eigenbasis hA j,
      Submodule.subset_span ⟨⟨j, le_rfl⟩, rfl⟩, (eigenbasis hA).norm_eq_one j,
      (inner_op_eigenbasis hA j).symm⟩, ?_⟩
    rintro _ ⟨x, hx, hx1, rfl⟩
    exact le_inner_of_mem_headSpan hA j hx hx1
  · rintro m ⟨S, hS, hmin⟩
    obtain ⟨x, hxS, hx1, hle⟩ := exists_unit_inner_le hA j S hS
    exact (hmin.2 ⟨x, hxS, hx1, rfl⟩).trans hle

/-- On any subspace, the set of Rayleigh quotients of nonzero vectors coincides with the set of
values `⟪x, A x⟫` on unit vectors. -/
lemma rayleigh_set_eq (S : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    {r : ℝ | ∃ x ∈ S, x ≠ 0 ∧ r = rayleighQuotient A x} =
      {r : ℝ | ∃ x ∈ S, ‖x‖ = 1 ∧ r = inner ℝ x (op A x)} := by
  ext r
  constructor
  · rintro ⟨x, hxS, hx0, rfl⟩
    have hx1 : ‖‖x‖⁻¹ • x‖ = 1 := by simpa using norm_smul_inv_norm (𝕜 := ℝ) hx0
    refine ⟨‖x‖⁻¹ • x, S.smul_mem _ hxS, hx1, ?_⟩
    rw [map_smul, inner_smul_left, inner_smul_right, rayleighQuotient]
    simp only [conj_trivial]
    field_simp
  · rintro ⟨x, hxS, hx1, rfl⟩
    refine ⟨x, hxS, ?_, ?_⟩
    · rintro rfl
      simp at hx1
    · rw [rayleighQuotient, hx1, one_pow, div_one]

/-- **Courant–Fischer theorem, Rayleigh-quotient form.**
`λⱼ(A) = max_{dim S = j+1} min_{x ∈ S, x ≠ 0} R_A(x)`. -/
theorem courant_fischer_rayleigh (j : Fin n) :
    IsGreatest
      {m : ℝ | ∃ S : Submodule ℝ (EuclideanSpace ℝ (Fin n)), finrank ℝ S = j + 1 ∧
        IsLeast {r : ℝ | ∃ x ∈ S, x ≠ 0 ∧ r = rayleighQuotient A x} m}
      (eigenvaluesDesc hA j) := by
  simp_rw [rayleigh_set_eq]
  exact courant_fischer hA j

end CourantFischer
