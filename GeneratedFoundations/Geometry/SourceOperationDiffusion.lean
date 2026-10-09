module

public import GeneratedFoundations.Geometry.SourceBlockPowerLimit
public import GeneratedFoundations.Geometry.SourceOperationWalk
public import GeneratedFoundations.Geometry.SourceWeakConvergence

/-!
# Weak diffusion limits of the original source-operation process

The finite product experiment, its representation means, and their scaled
powers determine the limiting Borel probability law. The law is constructed
from the actual process by compactness and coefficient uniqueness. Its
covariance-calibrated limit is independent of the original direction law.
The same coefficient uniqueness proves the convolution law, the zero-parameter
identity, and weak continuity in the nonnegative evolution parameter.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisDifferentiation
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceStepExpansion
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceBlockPowerLimit
open GeneratedFoundations.Geometry.SourceOperationWalk
open GeneratedFoundations.Geometry.SourceWeakConvergence

namespace GeneratedFoundations.Geometry.SourceOperationDiffusion

local instance (m : ℕ) : CompleteSpace (HilbertCarrier m) :=
  FiniteDimensional.complete ℂ (HilbertCarrier m)

local instance (m : ℕ) : NormedAddCommGroup (End m) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (m : ℕ) : NormedRing (End m) :=
  ContinuousLinearMap.toNormedRing

local instance (m : ℕ) : NormedSpace ℂ (End m) :=
  ContinuousLinearMap.toNormedSpace

local instance (m : ℕ) : NormedSpace ℝ (End m) :=
  ContinuousLinearMap.toNormedSpace

private theorem inner_real_identity {H I : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    (b : OrthonormalBasis I ℂ H) (i j : I) (r : ℝ) :
    inner ℂ (b i) ((r • (1 : H →L[ℂ] H)) (b j)) =
      (r : ℂ) * (if i = j then 1 else 0) := by
  simp only [_root_.smul_apply, one_apply_eq_self,
    RCLike.real_smul_eq_coe_smul (K := ℂ), inner_smul_right, b.inner_eq_ite]
  rfl

private theorem inner_scalar_product {H I : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : OrthonormalBasis I ℂ H) (i j : I) (s t : ℂ) :
    inner ℂ (b i) (((s • (1 : H →L[ℂ] H)) * (t • 1)) (b j)) =
      (s * t) * (if i = j then 1 else 0) := by
  simp only [smul_mul_smul_comm, mul_one, _root_.smul_apply,
    one_apply_eq_self, inner_smul_right, b.inner_eq_ite]

variable {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
  (h : CenteredIsotropic μ c)

include h

/-- The coefficients are expectations of the actual independent source
products, in every degree and with both matrix indices retained. -/
theorem walk_entry_tendsto (t : ℝ) (ht : 0 ≤ t) (a : Index) :
    Tendsto (fun ε : ℝ =>
      expectation (walkProbability μ ε (stepCount c t ε)) (entryTest a))
      (𝓝[≠] 0) (𝓝 (heatCoefficient t a)) := by
  rcases a with ⟨m, i, j⟩
  let L : End m →L[ℂ] ℂ := (innerSL ℂ (sourceBasis m i)).comp
    (ContinuousLinearMap.apply ℂ (HilbertCarrier m) (sourceBasis m j))
  have hlim := (L.continuous.tendsto
    (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) • (1 : End m))).comp
      (meanStep_power_tendsto h m t ht)
  have heq (ε : ℝ) :
      expectation (walkProbability μ ε (stepCount c t ε)) (entryTest ⟨m, i, j⟩) =
        L (meanStep μ m ε ^ stepCount c t ε) := by
    exact walkLaw_matrixEntry μ m ε (stepCount c t ε) i j
  have hvalue : L (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) • (1 : End m)) =
      heatCoefficient t ⟨m, i, j⟩ := by
    change inner ℂ (sourceBasis m i)
      ((Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) • (1 : End m))
        (sourceBasis m j)) = _
    simpa only [heatCoefficient] using!
      inner_real_identity (sourceBasis m) i j (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))))
  simpa only [Function.comp_def, heq, hvalue] using! hlim

/-- Existence and uniqueness of the law accompany weak convergence of the
whole actual walk family, rather than only a selected subsequence. -/
theorem operation_probability_limit (t : ℝ) (ht : 0 ≤ t) :
    ∃ ρ : ProbabilityMeasure SU2,
      HasEntryIntegrals ρ (heatCoefficient t) ∧
        Tendsto (fun ε : ℝ => walkProbability μ ε (stepCount c t ε)) (𝓝[≠] 0) (𝓝 ρ) ∧
        ∀ σ : ProbabilityMeasure SU2, HasEntryIntegrals σ (heatCoefficient t) → σ = ρ :=
  heat_probability_limit (𝓝[≠] (0 : ℝ))
    (fun ε => walkProbability μ ε (stepCount c t ε)) t (walk_entry_tendsto h t ht)

/-- This probability law is selected from the proved actual-process limit. -/
def heatLaw (t : ℝ) (ht : 0 ≤ t) : ProbabilityMeasure SU2 :=
  (operation_probability_limit h t ht).choose

theorem heatLaw_entries (t : ℝ) (ht : 0 ≤ t) :
    HasEntryIntegrals (heatLaw h t ht) (heatCoefficient t) :=
  (operation_probability_limit h t ht).choose_spec.1

theorem operation_walk_tendsto_heat (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun ε : ℝ => walkProbability μ ε (stepCount c t ε))
      (𝓝[≠] 0) (𝓝 (heatLaw h t ht)) :=
  (operation_probability_limit h t ht).choose_spec.2.1

/-- The statement also applies directly to the finite Cartesian experiment,
with its independent product measure and actual ordered source product. -/
theorem independent_source_products_tendsto_heat (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (β := ProbabilityMeasure SU2) (fun ε : ℝ =>
      (⟨(sampleLaw μ (stepCount c t ε)).map
        (sampleProduct ε (stepCount c t ε)), inferInstance⟩ : ProbabilityMeasure SU2))
      (𝓝[≠] 0) (𝓝 (heatLaw h t ht)) := by
  have heq (ε : ℝ) :
      (⟨(sampleLaw μ (stepCount c t ε)).map
        (sampleProduct ε (stepCount c t ε)), inferInstance⟩ : ProbabilityMeasure SU2) =
      walkProbability μ ε (stepCount c t ε) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact sampleProduct_pushforward μ ε (stepCount c t ε)
  simpa only [heq] using operation_walk_tendsto_heat h t ht

/-- Covariance normalization removes the dependence on the original fixed
direction law. The two laws need not share higher moments or support. -/
theorem heatLaw_independent {ν : Measure Direction} [IsProbabilityMeasure ν]
    {d : ℝ} (k : CenteredIsotropic ν d) (t : ℝ) (ht : 0 ≤ t) :
    heatLaw h t ht = heatLaw k t ht :=
  hasEntryIntegrals_unique (heatLaw_entries h t ht) (heatLaw_entries k t ht)

theorem heatLaw_groupMean (t : ℝ) (ht : 0 ≤ t) (m : ℕ) :
    groupMean (heatLaw h t ht : Measure SU2) m =
      (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ) • (1 : End m) := by
  apply groupMean_eq_scalar
  intro i j
  exact heatLaw_entries h t ht ⟨m, i, j⟩

/-- The zero-parameter law is the identity operation. -/
theorem heatLaw_zero : (heatLaw h 0 le_rfl : Measure SU2) = Measure.dirac 1 := by
  let ρ : ProbabilityMeasure SU2 := ⟨Measure.dirac 1, inferInstance⟩
  have hρ : HasEntryIntegrals ρ (heatCoefficient 0) := by
    rintro ⟨m, i, j⟩
    change (∫ U, matrixEntry m i j U ∂Measure.dirac (1 : SU2)) = _
    rw [integral_dirac]
    simp only [matrixEntry, matrixCoefficient_apply, unitaryAction_one_apply,
      heatCoefficient, neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one,
      one_mul]
    exact (sourceBasis m).inner_eq_ite i j
  exact congrArg (fun ν : ProbabilityMeasure SU2 => (ν : Measure SU2))
    (hasEntryIntegrals_unique (heatLaw_entries h 0 le_rfl) hρ)

/-- The evolution law follows from convolution of the actual source
representations and uniqueness of all matrix-coefficient integrals. -/
theorem heatLaw_add (s t : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (heatLaw h s hs : Measure SU2) ∗ₘ (heatLaw h t ht : Measure SU2) =
      (heatLaw h (s + t) (add_nonneg hs ht) : Measure SU2) := by
  let ρ : ProbabilityMeasure SU2 :=
    ⟨(heatLaw h s hs : Measure SU2) ∗ₘ (heatLaw h t ht : Measure SU2), inferInstance⟩
  have hρ : HasEntryIntegrals ρ (heatCoefficient (s + t)) := by
    rintro ⟨m, i, j⟩
    change (∫ U, matrixEntry m i j U ∂
      ((heatLaw h s hs : Measure SU2) ∗ₘ (heatLaw h t ht : Measure SU2))) = _
    rw [groupMean_matrixEntry, groupMean_mconv, heatLaw_groupMean h,
      heatLaw_groupMean h]
    have he : (Real.exp (-s * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ) *
        (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ) =
        (Real.exp (-(s + t) * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.exp_add]
      congr 2
      ring
    simpa only [he, heatCoefficient] using!
      inner_scalar_product (sourceBasis m) i j
        (Real.exp (-s * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ)
        (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ)
  exact congrArg (fun ν : ProbabilityMeasure SU2 => (ν : Measure SU2))
    (hasEntryIntegrals_unique hρ (heatLaw_entries h (s + t) (add_nonneg hs ht)))

/-- Continuity holds in the weak topology on the full probability law. -/
theorem heatLaw_continuous : Continuous (fun t : ℝ≥0 => heatLaw h t t.property) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply tendsto_of_entry_limits (values := heatCoefficient t)
  · intro a
    have hc : Continuous (fun s : ℝ≥0 => heatCoefficient s a) := by
      unfold heatCoefficient
      fun_prop
    have heq (s : ℝ≥0) : expectation (heatLaw h s s.property) (entryTest a) =
        heatCoefficient s a := heatLaw_entries h s s.property a
    simpa only [heq] using hc.tendsto t
  · exact heatLaw_entries h t t.property

end GeneratedFoundations.Geometry.SourceOperationDiffusion
