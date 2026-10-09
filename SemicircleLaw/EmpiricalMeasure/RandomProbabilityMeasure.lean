import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.UnitInterval

/-!
# Random probability measures

Let `S` be a Polish space with its Borel σ-algebra `𝓑(S)` and let `(Ω, 𝓕, ℙ)` be a
probability space. A map `μ : 𝓑(S) × Ω → [0,1]` is a *random probability measure on `S`*
if

1. for `ℙ`-almost every `ω`, the map `B ↦ μ(B, ω)` on `𝓑(S)` is a probability measure;
2. for every `B ∈ 𝓑(S)`, the map `ω ↦ μ(B, ω)` is measurable.

Formalization choices:
* "`S` is Polish with Borel σ-algebra" is `[TopologicalSpace S] [PolishSpace S]
  [MeasurableSpace S] [BorelSpace S]`.
* `𝓑(S)` (the collection of Borel sets) is the subtype `{B : Set S // MeasurableSet B}`,
  and `[0,1]` is Mathlib's `unitInterval` (with its subspace Borel σ-algebra).
* "`B ↦ μ(B, ω)` is a probability measure" means that it agrees on every Borel set with
  some probability measure `ν` on `S`.
* The probability space `(Ω, 𝓕, ℙ)` is `[MeasurableSpace Ω] (ℙ : Measure Ω)
  [IsProbabilityMeasure ℙ]`; `𝓑(ℝ)` is the Borel σ-algebra instance on `ℝ`.
* The product σ-algebra `𝓑(S) ⊗ 𝓕` is Mathlib's default instance on `S × Ω`;
  `prod_le_iff_measurable_projections` records that it is the smallest σ-algebra making
  both projections measurable.
-/

open MeasureTheory

namespace RandomMeasure

/-- The product σ-algebra on `S × Ω` is the smallest σ-algebra for which the canonical
projections are measurable: it is contained in a σ-algebra `m` iff both projections are
measurable w.r.t. `m`. -/
theorem prod_le_iff_measurable_projections {S Ω : Type*} [MeasurableSpace S]
    [MeasurableSpace Ω] (m : MeasurableSpace (S × Ω)) :
    Prod.instMeasurableSpace ≤ m ↔
      Measurable[m] (Prod.fst : S × Ω → S) ∧ Measurable[m] (Prod.snd : S × Ω → Ω) := by
  rw [measurable_iff_comap_le, measurable_iff_comap_le, Prod.instMeasurableSpace,
    MeasurableSpace.prod]
  exact sup_le_iff

/-- The projections are measurable for the product σ-algebra. -/
theorem measurable_projections {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω] :
    Measurable (Prod.fst : S × Ω → S) ∧ Measurable (Prod.snd : S × Ω → Ω) :=
  ⟨measurable_fst, measurable_snd⟩

/-- `μ : 𝓑(S) × Ω → [0,1]` (curried) is a **random probability measure on `S`** with
respect to the probability measure `ℙ` on `Ω`. -/
structure IsRandomProbabilityMeasure (S : Type*) {Ω : Type*} [TopologicalSpace S]
    [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ]
    (μ : {B : Set S // MeasurableSet B} → Ω → unitInterval) : Prop where
  /-- (1) For `ℙ`-a.e. `ω`, `B ↦ μ(B, ω)` is a probability measure on `𝓑(S)`. -/
  ae_isProbabilityMeasure : ∀ᵐ ω ∂ℙ, ∃ ν : Measure S, IsProbabilityMeasure ν ∧
    ∀ B : {B : Set S // MeasurableSet B}, ν B.1 = ENNReal.ofReal (μ B ω : ℝ)
  /-- (2) For every Borel set `B`, `ω ↦ μ(B, ω)` is measurable. -/
  measurable_apply : ∀ B : {B : Set S // MeasurableSet B}, Measurable (fun ω => μ B ω)

/-- Bundled version: a random probability measure `ω ↦ μ_ω` on `S`. -/
structure RandomProbabilityMeasure (S : Type*) {Ω : Type*} [TopologicalSpace S]
    [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] where
  /-- The underlying map `μ : 𝓑(S) × Ω → [0,1]`. -/
  toFun : {B : Set S // MeasurableSet B} → Ω → unitInterval
  isRandomProbabilityMeasure : IsRandomProbabilityMeasure S ℙ toFun

/-- Sanity check: a fixed probability measure `ν` on `S` (constant in `ω`) is a random
probability measure. -/
theorem isRandomProbabilityMeasure_const {S Ω : Type*} [TopologicalSpace S]
    [PolishSpace S] [MeasurableSpace S] [BorelSpace S] [MeasurableSpace Ω]
    (ℙ : Measure Ω) [IsProbabilityMeasure ℙ] (ν : Measure S) [IsProbabilityMeasure ν] :
    IsRandomProbabilityMeasure S ℙ (fun B _ =>
      ⟨(ν B.1).toReal, ENNReal.toReal_nonneg,
        ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)⟩) where
  ae_isProbabilityMeasure := Filter.Eventually.of_forall fun _ =>
    ⟨ν, inferInstance, fun B => by simp [measure_ne_top]⟩
  measurable_apply := fun _ => measurable_const

end RandomMeasure

namespace RandomMeasure

/-- The case `S = ℝ`, with `ℝ` carrying its Borel σ-algebra `𝓑(ℝ)`: a random probability
measure on `ℝ` over the probability space `(Ω, 𝓕, ℙ)`. -/
abbrev RandomProbabilityMeasureReal {Ω : Type*} [MeasurableSpace Ω] (ℙ : Measure Ω)
    [IsProbabilityMeasure ℙ] :=
  RandomProbabilityMeasure ℝ ℙ

/-- The σ-algebra on `ℝ` used above is indeed the Borel σ-algebra `𝓑(ℝ)`. -/
theorem real_measurableSpace_eq_borel : (inferInstance : MeasurableSpace ℝ) = borel ℝ :=
  BorelSpace.measurable_eq

end RandomMeasure
