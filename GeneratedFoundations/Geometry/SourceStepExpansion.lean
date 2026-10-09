module

public import GeneratedFoundations.Geometry.SourceDirectionalRepresentation
public import GeneratedFoundations.Geometry.SourceDirectionalMoments
public import GeneratedFoundations.Operations.UnitaryQuadraticRemainder
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The finite-variance expansion of an actual source step

The averaged operator is the representation of the original group-valued
step. Its exponential formula is obtained from that source representation,
not supplied as a new model. A single fixed direction law is used for every
step size. Unitarity gives a quadratic dominating function, and dominated
convergence therefore requires only the stated second moments.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory
open scoped Topology BigOperators
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceDirectionalRepresentation
open GeneratedFoundations.Operations.UnitaryQuadraticRemainder

namespace GeneratedFoundations.Geometry.SourceStepExpansion

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

local instance (m : ℕ) : NormedAlgebra ℚ (End m) :=
  NormedAlgebra.restrictScalars ℚ ℝ (End m)

private theorem exp_complex_smul_eq_curve {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • A) = curve A t := by
  rw [curve, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

private theorem curve_remainder_expansion {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) (t : ℝ) :
    curve A t = 1 + t • A + (t ^ 2 / 2) • (A * A) + remainder A t := by
  unfold remainder
  simp only [pow_two]
  abel

private theorem integral_real_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : Measure Direction) (a : ℝ) (f : Direction → E) :
    (∫ ξ, a • f ξ ∂ν) = a • ∫ ξ, f ξ ∂ν :=
  integral_smul a f

private theorem integrable_quadratic_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ν : Measure Direction) [IsFiniteMeasure ν]
    (e : E) (f g r : Direction → E) (a b : ℝ)
    (hf : Integrable f ν) (hg : Integrable g ν) (hr : Integrable r ν) :
    Integrable (fun ξ => e + a • f ξ + b • g ξ + r ξ) ν :=
  (((integrable_const e).fun_add (hf.fun_smul a)).fun_add
    (hg.fun_smul b)).fun_add hr

private theorem integral_quadratic_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (ν : Measure Direction)
    [IsProbabilityMeasure ν] (e : E) (f g r : Direction → E) (a b : ℝ)
    (hf : Integrable f ν) (hg : Integrable g ν) (hr : Integrable r ν) :
    (∫ ξ, e + a • f ξ + b • g ξ + r ξ ∂ν) =
      e + a • (∫ ξ, f ξ ∂ν) + b • (∫ ξ, g ξ ∂ν) + ∫ ξ, r ξ ∂ν := by
  have he : Integrable (fun _ : Direction => e) ν := integrable_const e
  have hl : Integrable (fun ξ => a • f ξ) ν := hf.fun_smul a
  have hq : Integrable (fun ξ => b • g ξ) ν := hg.fun_smul b
  rw [integral_add ((he.fun_add hl).fun_add hq) hr,
    integral_add (he.fun_add hl) hq, integral_add he hl]
  simp only [integral_smul, integral_const, probReal_univ, one_smul]

private theorem quadratic_scalar_simplification {E : Type*} [AddCommGroup E]
    [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (e r : E) (ε c : ℝ) (m : ℕ) :
    e + ε • (0 : E) + (ε ^ 2 / 2) •
        ((-((c : ℂ) * (m : ℂ) * ((m : ℂ) + 2)) / 4) • e) + r =
      e - (((c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 : ℝ) : ℂ) • e) + r := by
  have hs : ((ε ^ 2 / 2 : ℝ) : ℂ) *
      (-((c : ℂ) * (m : ℂ) * ((m : ℂ) + 2)) / 4) =
      -((c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 : ℝ) : ℂ) := by
    push_cast
    ring
  calc
    _ = e + ((((ε ^ 2 / 2 : ℝ) : ℂ) *
        (-((c : ℂ) * (m : ℂ) * ((m : ℂ) + 2)) / 4)) • e) + r := by
      rw [smul_zero, add_zero, RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
      rfl
    _ = e + (-((c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 : ℝ) : ℂ)) • e + r :=
      congrArg (fun z : ℂ => e + z • e + r) hs
    _ = _ := by rw [neg_smul, sub_eq_add_neg]

def stepMatrix (m : ℕ) (ξ : Direction) (ε : ℝ) : End m :=
  (unitaryAction m (SourceDirectionalStep.step ξ ε)).toLinearIsometry.toContinuousLinearMap

theorem stepMatrix_eq_curve (m : ℕ) (ξ : Direction) (ε : ℝ) :
    stepMatrix m ξ ε = curve (generator m ξ) ε := by
  rw [stepMatrix, unitaryAction_step_eq_exp_clm]
  exact exp_complex_smul_eq_curve (H := HilbertCarrier m) (generator m ξ) ε

def stepRemainder (m : ℕ) (ε : ℝ) (ξ : Direction) : End m :=
  remainder (generator m ξ) ε

theorem stepRemainder_continuous (m : ℕ) (ε : ℝ) : Continuous (stepRemainder m ε) := by
  unfold stepRemainder remainder curve
  exact (((NormedSpace.exp_continuous.comp ((generator_continuous m).const_smul ε)).sub
    continuous_const).sub ((generator_continuous m).const_smul ε)).sub
      (((generator_continuous m).pow 2).const_smul (ε ^ 2 / 2))

theorem stepRemainder_bound (m : ℕ) (ε : ℝ) (ξ : Direction) :
    ‖stepRemainder m ε ξ‖ ≤ ε ^ 2 * (normSquareBound m * sizeSq ξ) :=
  (norm_remainder_le (generator m ξ) (generator_star m ξ) ε).trans
    (mul_le_mul_of_nonneg_left (norm_generator_sq_le m ξ) (sq_nonneg ε))

/-- The bound holds also at zero, where the normalized expression is zero. -/
theorem normalized_remainder_bound (m : ℕ) (ε : ℝ) (ξ : Direction) :
    ‖(ε ^ 2)⁻¹ • stepRemainder m ε ξ‖ ≤ normSquareBound m * sizeSq ξ :=
  (norm_scaled_remainder_le (generator m ξ) (generator_star m ξ) ε).trans
    (norm_generator_sq_le m ξ)

theorem normalized_remainder_tendsto (m : ℕ) (ξ : Direction) :
    Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ • stepRemainder m ε ξ) (𝓝 0) (𝓝 0) :=
  remainder_scaled_tendsto_zero (generator m ξ)

def averagedRemainder (μ : Measure Direction) (m : ℕ) (ε : ℝ) : End m :=
  ∫ ξ : Direction, stepRemainder m ε ξ ∂μ

def meanStep (μ : Measure Direction) (m : ℕ) (ε : ℝ) : End m :=
  ∫ ξ : Direction, stepMatrix m ξ ε ∂μ

variable {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
  (h : CenteredIsotropic μ c)

include h

omit [IsProbabilityMeasure μ] in
theorem stepRemainder_integrable (m : ℕ) (ε : ℝ) : Integrable (stepRemainder m ε) μ := by
  apply (((sizeSq_integrable h).const_mul (normSquareBound m)).const_mul (ε ^ 2)).mono'
    (stepRemainder_continuous m ε).aestronglyMeasurable
  exact Eventually.of_forall (stepRemainder_bound m ε)

omit [IsProbabilityMeasure μ] in
/-- The same quadratic dominating function controls the limit at every
direction. No third or exponential moment occurs in this statement. -/
theorem averagedRemainder_scaled_tendsto_zero (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ • averagedRemainder μ m ε) (𝓝 0) (𝓝 0) := by
  have ht := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := fun ε ξ => (ε ^ 2)⁻¹ • stepRemainder m ε ξ)
    (f := fun _ : Direction => (0 : End m))
    (fun ξ => normSquareBound m * sizeSq ξ)
    (Eventually.of_forall (fun ε =>
      ((stepRemainder_continuous m ε).const_smul (ε ^ 2)⁻¹).aestronglyMeasurable))
    (Eventually.of_forall (fun ε => Eventually.of_forall (normalized_remainder_bound m ε)))
    ((sizeSq_integrable h).const_mul (normSquareBound m))
    (Eventually.of_forall (normalized_remainder_tendsto m))
  have heq (ε : ℝ) :
      (∫ ξ : Direction, (ε ^ 2)⁻¹ • stepRemainder m ε ξ ∂μ) =
        (ε ^ 2)⁻¹ • averagedRemainder μ m ε :=
    integral_real_smul (E := End m) μ (ε ^ 2)⁻¹ (stepRemainder m ε)
  simpa only [integral_zero] using! ht.congr' (Eventually.of_forall heq)

omit h in
theorem stepMatrix_expansion (m : ℕ) (ξ : Direction) (ε : ℝ) :
    stepMatrix m ξ ε = 1 + ε • generator m ξ +
      (ε ^ 2 / 2) • (generator m ξ * generator m ξ) + stepRemainder m ε ξ := by
  rw [stepMatrix_eq_curve]
  exact curve_remainder_expansion (H := HilbertCarrier m) (generator m ξ) ε

theorem stepMatrix_integrable (m : ℕ) (ε : ℝ) :
    Integrable (fun ξ : Direction => stepMatrix m ξ ε) μ := by
  simp_rw [stepMatrix_expansion]
  exact integrable_quadratic_sum (E := End m) μ 1 (generator m)
    (fun ξ => generator m ξ * generator m ξ) (stepRemainder m ε)
    ε (ε ^ 2 / 2) (generator_integrable h m) (generator_square_integrable h m)
    (stepRemainder_integrable h m ε)

theorem meanStep_integral_expansion (m : ℕ) (ε : ℝ) :
    meanStep μ m ε = 1 + ε • (∫ ξ : Direction, generator m ξ ∂μ) +
      (ε ^ 2 / 2) • (∫ ξ : Direction, generator m ξ * generator m ξ ∂μ) +
        averagedRemainder μ m ε := by
  unfold meanStep
  simp_rw [stepMatrix_expansion]
  exact integral_quadratic_sum (E := End m) μ 1 (generator m)
    (fun ξ => generator m ξ * generator m ξ) (stepRemainder m ε)
    ε (ε ^ 2 / 2) (generator_integrable h m) (generator_square_integrable h m)
    (stepRemainder_integrable h m ε)

/-- The coefficient comes from the covariance and the source Casimir with
its original half-angle scale. -/
theorem meanStep_expansion (m : ℕ) (ε : ℝ) :
    meanStep μ m ε =
      1 - (((c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 : ℝ) : ℂ) • (1 : End m)) +
        averagedRemainder μ m ε := by
  rw [meanStep_integral_expansion h, integral_generator h, integral_generator_square h]
  exact quadratic_scalar_simplification (E := End m)
    1 (averagedRemainder μ m ε) ε c m

theorem meanStep_second_order_tendsto (m : ℕ) :
    Tendsto (fun ε : ℝ => (ε ^ 2)⁻¹ •
      (meanStep μ m ε - 1 +
        (((c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 : ℝ) : ℂ) • (1 : End m))))
      (𝓝 0) (𝓝 0) := by
  have hrem (ε : ℝ) : meanStep μ m ε - 1 +
      (((c * ε ^ 2 * (m : ℝ) * ((m : ℝ) + 2) / 8 : ℝ) : ℂ) • (1 : End m)) =
      averagedRemainder μ m ε := by
    rw [meanStep_expansion h]
    abel
  simpa only [hrem] using averagedRemainder_scaled_tendsto_zero h m

end GeneratedFoundations.Geometry.SourceStepExpansion
