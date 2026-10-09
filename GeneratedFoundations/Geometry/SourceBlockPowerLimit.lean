module

public import GeneratedFoundations.Geometry.SourceStepExpansion
public import GeneratedFoundations.Operations.ContractivePowerLimit
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Diffusive powers of the actual source Fourier matrices

Each mean step is a contraction because it averages the original unitary
source operations. The finite-variance expansion is compared with a scalar
exponential, and the contraction estimate controls all subsequent powers.
The integer step count retains the original factor eight. Limits are taken
through nonzero step sizes; the evolution parameter may equal zero.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceStepExpansion
open GeneratedFoundations.Operations.ContractivePowerLimit

namespace GeneratedFoundations.Geometry.SourceBlockPowerLimit

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

local instance (m : ℕ) : NormedAlgebra ℂ (End m) :=
  ContinuousLinearMap.toNormedAlgebra

local instance (m : ℕ) : NormedAlgebra ℝ (End m) :=
  NormedAlgebra.restrictScalars ℝ ℂ (End m)

local instance (m : ℕ) : Nontrivial (HilbertCarrier m) :=
  Module.nontrivial_of_finrank_eq_succ (R := ℂ) (hilbertCarrier_finrank m)

private theorem one_sub_complex_smul {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (r : ℝ) :
    (1 : H →L[ℂ] H) - (r : ℂ) • 1 = (1 - r) • (1 : H →L[ℂ] H) := by
  rw [sub_smul, one_smul, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem stepMatrix_norm_le_one (m : ℕ) (ξ : Direction) (ε : ℝ) :
    ‖stepMatrix m ξ ε‖ ≤ 1 :=
  (unitaryAction m (SourceDirectionalStep.step ξ ε)).toLinearIsometry.norm_toContinuousLinearMap_le

theorem meanStep_norm_le_one (μ : Measure Direction) [IsProbabilityMeasure μ]
    (m : ℕ) (ε : ℝ) : ‖meanStep μ m ε‖ ≤ 1 := by
  simpa [meanStep, measureReal_def] using
    norm_integral_le_of_norm_le_const
      (μ := μ) (Eventually.of_forall (fun ξ => stepMatrix_norm_le_one m ξ ε))

/-- The decay rate is inherited from the source half-angle Casimir. -/
def decay (c : ℝ) (m : ℕ) : ℝ := c * (m : ℝ) * ((m : ℝ) + 2) / 8

theorem decay_nonneg {c : ℝ} (hc : 0 ≤ c) (m : ℕ) : 0 ≤ decay c m := by
  unfold decay
  positivity

theorem square_tendsto_nhdsNE :
    Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [zero_pow (by decide : 2 ≠ 0)] using
      ((continuous_pow 2).tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact pow_ne_zero 2 hε

/-- A scalar first derivative suffices for the comparison error. -/
theorem scalar_comparison_error_tendsto (a : ℝ) :
    Tendsto (fun ε : ℝ =>
      (ε ^ 2)⁻¹ * (1 - a * ε ^ 2 - Real.exp (-a * ε ^ 2)))
      (𝓝[≠] 0) (𝓝 0) := by
  have hd : HasDerivAt (fun x : ℝ => 1 - a * x - Real.exp (-a * x)) 0 0 := by
    simpa using! ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((hasDerivAt_id (0 : ℝ)).const_mul a)).sub
        (((hasDerivAt_id (0 : ℝ)).const_mul (-a)).exp)
  have hs : Tendsto (fun x : ℝ => x⁻¹ * (1 - a * x - Real.exp (-a * x)))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [zero_add, mul_zero, Real.exp_zero, sub_self, sub_zero, smul_eq_mul]
      using hd.tendsto_slope_zero
  exact hs.comp square_tendsto_nhdsNE

private theorem comparison_error_from_expansion {E : Type*} [NormedRing E]
    [NormedAlgebra ℝ E] (M R : ℝ → E) (a : ℝ)
    (hexpansion : ∀ ε : ℝ, M ε = (1 - a * ε ^ 2) • (1 : E) + R ε)
    (hrem : Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ • R ε) (𝓝[≠] 0) (𝓝 0)) :
    Tendsto (fun ε : ℝ => ‖M ε - comparison (E := E) a ε‖ / ε ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  have heq (ε : ℝ) :
      M ε - comparison (E := E) a ε =
        R ε + (1 - a * ε ^ 2 - Real.exp (-a * ε ^ 2)) • (1 : E) := by
    rw [hexpansion]
    simp only [comparison, sub_smul, one_smul]
    abel
  have hs := (scalar_comparison_error_tendsto a).smul_const (1 : E)
  have ht : Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ •
      (M ε - comparison (E := E) a ε)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [heq, smul_add, smul_smul, zero_smul, add_zero] using hrem.add hs
  have hn (ε : ℝ) : ‖(ε ^ 2)⁻¹ • (M ε - comparison (E := E) a ε)‖ =
      ‖M ε - comparison (E := E) a ε‖ / ε ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg ε)),
      div_eq_mul_inv, mul_comm]
  simpa only [hn, norm_zero] using ht.norm

variable {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
  (h : CenteredIsotropic μ c)

include h

theorem meanStep_expansion_real (m : ℕ) (ε : ℝ) :
    meanStep μ m ε = (1 - decay c m * ε ^ 2) • (1 : End m) +
      averagedRemainder μ m ε := by
  have hs : c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 = decay c m * ε ^ 2 := by
    unfold decay
    ring
  rw [meanStep_expansion h, hs]
  exact congrArg (fun A : End m => A + averagedRemainder μ m ε)
    (one_sub_complex_smul (H := HilbertCarrier m) (decay c m * ε ^ 2))

theorem meanStep_comparison_error_tendsto (m : ℕ) :
    Tendsto (fun ε : ℝ => ‖meanStep μ m ε - comparison (E := End m) (decay c m) ε‖ /
      ε ^ 2) (𝓝[≠] 0) (𝓝 0) :=
  comparison_error_from_expansion (E := End m) (meanStep μ m)
    (averagedRemainder μ m) (decay c m) (meanStep_expansion_real h m)
    ((averagedRemainder_scaled_tendsto_zero h m).mono_left nhdsWithin_le_nhds)

omit h in
/-- The source operation count, with its original covariance calibration. -/
def stepCount (c t ε : ℝ) : ℕ := steps (8 * t / c) ε

omit h in
theorem stepCount_eq_floor (c t ε : ℝ) :
    stepCount c t ε = ⌊8 * t / (c * ε ^ 2)⌋₊ := by
  simp only [stepCount, steps, div_div]

/-- Every actual homogeneous source block has the round heat multiplier. -/
theorem meanStep_power_tendsto (m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun ε : ℝ => meanStep μ m ε ^ stepCount c t ε)
      (𝓝[≠] 0) (𝓝 (Real.exp (-t * ((m : ℝ) * ((m : ℝ) + 2))) • (1 : End m))) := by
  have hc : c ≠ 0 := ne_of_gt h.positive_covariance
  have hscale : -(decay c m) * (8 * t / c) = -t * ((m : ℝ) * ((m : ℝ) + 2)) := by
    unfold decay
    field_simp [hc]
  simpa only [stepCount, hscale] using! power_tendsto
    (M := meanStep μ m) (a := decay c m) (K := 8 * t / c)
    (decay_nonneg h.positive_covariance.le m)
    (div_nonneg (mul_nonneg (by norm_num) ht) h.positive_covariance.le)
    (meanStep_norm_le_one μ m) (meanStep_comparison_error_tendsto h m)

end GeneratedFoundations.Geometry.SourceBlockPowerLimit
