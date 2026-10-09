module

public import GeneratedFoundations.Geometry.SourceFiniteRotations
public import GeneratedFoundations.Geometry.SourceDirectionalMoments
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Instances

/-!
# The uniform finite-control source law

A source direction and an independent uniform label among the 24 generated
rotations define one trial. Their product-law pushforward is the equal average
of the rotated laws. This law is independent of the later step size.

Finite coordinate second moments and a positive total second moment suffice
for the construction. The finite rotation identities give zero mean and
isotropic covariance for the averaged law. Its covariance is one third of
the unchanged total second moment.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceFiniteRotations

namespace GeneratedFoundations.Geometry.SourceFiniteControlLaw

/-- Every one of the 24 control labels receives the same mass. -/
def labelLaw : Measure Control :=
  (24 : ℝ≥0∞)⁻¹ • ∑ r : Control, Measure.dirac r

instance labelLaw_isProbability : IsProbabilityMeasure labelLaw where
  measure_univ := by
    norm_num [labelLaw, Measure.smul_apply, Measure.finsetSum_apply, card_control]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

theorem labelLaw_singleton (r : Control) : labelLaw {r} = (24 : ℝ≥0∞)⁻¹ := by
  classical
  simp [labelLaw, Measure.smul_apply, Measure.finsetSum_apply]

/-- The label and the original direction are independent in one trial. -/
def oneSampleLaw (μ : Measure Direction) : Measure (Control × Direction) := labelLaw.prod μ

instance oneSampleLaw_isProbability (μ : Measure Direction) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (oneSampleLaw μ) := by
  unfold oneSampleLaw
  infer_instance

def rotatedDirection (p : Control × Direction) : Direction := rotate p.1 p.2

theorem rotatedDirection_measurable : Measurable rotatedDirection :=
  measurable_from_prod_countable_right fun r => (continuous_rotate r).measurable

/-- This is a fixed source law, with no dependence on the step parameter. -/
def averagedLaw (μ : Measure Direction) : Measure Direction :=
  (24 : ℝ≥0∞)⁻¹ • ∑ r : Control, μ.map (rotate r)

instance averagedLaw_isProbability (μ : Measure Direction) [IsProbabilityMeasure μ] :
    IsProbabilityMeasure (averagedLaw μ) where
  measure_univ := by
    norm_num [averagedLaw, Measure.smul_apply, Measure.finsetSum_apply, card_control]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- The equal measure average is the pushforward of the independent
direction and uniform control label. -/
theorem oneSample_pushforward (μ : Measure Direction) [IsProbabilityMeasure μ] :
    (oneSampleLaw μ).map rotatedDirection = averagedLaw μ := by
  have hp : (∑ r : Control, Measure.dirac r).prod μ =
      ∑ r : Control, (Measure.dirac r).prod μ := by
    simpa only [Measure.sum_fintype] using
      (Measure.prod_sum_left (fun r : Control => Measure.dirac r) μ)
  rw [oneSampleLaw, labelLaw, Measure.prod_smul_left, hp,
    Measure.map_smul _ rotatedDirection_measurable.aemeasurable,
    Measure.map_finset_sum' rotatedDirection_measurable.aemeasurable]
  change (24 : ℝ≥0∞)⁻¹ • (∑ r : Control, ((Measure.dirac r).prod μ).map rotatedDirection) =
    (24 : ℝ≥0∞)⁻¹ • (∑ r : Control, μ.map (rotate r))
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [Measure.dirac_prod, Measure.map_map rotatedDirection_measurable measurable_prodMk_left]
  rfl

variable (μ : Measure Direction) [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem integrable_averagedLaw {f : Direction → ℝ} (hf : Continuous f)
    (hi : ∀ r : Control, Integrable (fun ξ => f (rotate r ξ)) μ) :
    Integrable f (averagedLaw μ) := by
  apply Integrable.smul_measure (c := (24 : ℝ≥0∞)⁻¹) _ (by norm_num)
  apply integrable_finsetSum_measure.mpr
  intro r hr
  exact (integrable_map_measure hf.aestronglyMeasurable
    (continuous_rotate r).measurable.aemeasurable).mpr (hi r)

omit [IsProbabilityMeasure μ] in
/-- Integration over the constructed law equals the uniform rotation average. -/
theorem integral_averagedLaw {f : Direction → ℝ} (hf : Continuous f)
    (hi : ∀ r : Control, Integrable (fun ξ => f (rotate r ξ)) μ) :
    (∫ ξ, f ξ ∂averagedLaw μ) =
      (1 / 24 : ℝ) * ∑ r : Control, ∫ ξ, f (rotate r ξ) ∂μ := by
  have him (r : Control) : Integrable f (μ.map (rotate r)) :=
    (integrable_map_measure hf.aestronglyMeasurable
      (continuous_rotate r).measurable.aemeasurable).mpr (hi r)
  rw [averagedLaw, integral_smul_measure,
    integral_finsetSum_measure (fun r _ => him r)]
  simp_rw [integral_map (continuous_rotate _).measurable.aemeasurable hf.aestronglyMeasurable]
  norm_num [ENNReal.toReal_inv, smul_eq_mul]

variable {μ}

omit [IsProbabilityMeasure μ] in
theorem raw_sizeSq_integrable
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ) : Integrable sizeSq μ := by
  apply integrable_finsetSum Finset.univ
  intro a ha
  exact (h2 a).integrable_sq

omit [IsProbabilityMeasure μ] in
theorem coordinate_memLp_of_integrable_sizeSq (hi : Integrable sizeSq μ) (a : Fin 3) :
    MemLp (fun ξ : Direction => ξ a) 2 μ := by
  apply (memLp_two_iff_integrable_sq (continuous_apply a).aestronglyMeasurable).mpr
  apply hi.mono' ((continuous_apply a).pow 2).aestronglyMeasurable
  filter_upwards [] with ξ
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact Finset.single_le_sum (fun b _ => sq_nonneg (ξ b)) (Finset.mem_univ a)

omit [IsProbabilityMeasure μ] in
/-- The coordinate formulation is equivalent to a finite total second moment. -/
theorem finite_second_moment_iff :
    (∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ) ↔ Integrable sizeSq μ :=
  ⟨raw_sizeSq_integrable, coordinate_memLp_of_integrable_sizeSq⟩

theorem averaged_coordinate_memLp
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ) (a : Fin 3) :
    MemLp (fun ξ : Direction => ξ a) 2 (averagedLaw μ) := by
  apply (memLp_two_iff_integrable_sq (continuous_apply a).aestronglyMeasurable).mpr
  exact integrable_averagedLaw μ (by fun_prop)
    (fun r => (coordinate_memLp h2 r a).integrable_sq)

theorem averaged_mean_zero
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ) (a : Fin 3) :
    (∫ ξ : Direction, ξ a ∂averagedLaw μ) = 0 := by
  have hi (r : Control) : Integrable (fun ξ : Direction => rotate r ξ a) μ :=
    (coordinate_memLp h2 r a).integrable (by norm_num)
  rw [integral_averagedLaw μ (by fun_prop) hi,
    ← integral_finsetSum Finset.univ (fun r _ => hi r)]
  simp only [sum_rotate, integral_zero, mul_zero]

def covariance (μ : Measure Direction) : ℝ := (∫ ξ : Direction, sizeSq ξ ∂μ) / 3

theorem averaged_covariance
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ) (a b : Fin 3) :
    (∫ ξ : Direction, ξ a * ξ b ∂averagedLaw μ) = if a = b then covariance μ else 0 := by
  have hi (r : Control) :
      Integrable (fun ξ : Direction => rotate r ξ a * rotate r ξ b) μ :=
    (coordinate_memLp h2 r a).integrable_mul (coordinate_memLp h2 r b)
  rw [integral_averagedLaw μ (by fun_prop) hi,
    ← integral_finsetSum Finset.univ (fun r _ => hi r)]
  by_cases hab : a = b
  · simp only [sum_rotate_mul, ite_eq_left hab, integral_const_mul, covariance]
    ring
  · simp only [sum_rotate_mul, ite_eq_right hab, integral_zero, mul_zero]

omit [IsProbabilityMeasure μ] in
/-- Averaging changes the angular law, but preserves its total second moment. -/
theorem integral_sizeSq_averagedLaw
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ) :
    (∫ ξ : Direction, sizeSq ξ ∂averagedLaw μ) = ∫ ξ : Direction, sizeSq ξ ∂μ := by
  have hi (r : Control) : Integrable (fun ξ => sizeSq (rotate r ξ)) μ := by
    simpa only [sizeSq_rotate] using raw_sizeSq_integrable h2
  rw [integral_averagedLaw μ (by unfold sizeSq; fun_prop) hi]
  simp only [sizeSq_rotate, Finset.sum_const, Finset.card_univ, card_control,
    nsmul_eq_mul, Nat.cast_ofNat]
  ring

/-- Finite control averaging supplies the diffusion moment conditions,
including for fixed nonzero deterministic directions. -/
theorem centeredIsotropic
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ)
    (hpos : 0 < ∫ ξ : Direction, sizeSq ξ ∂μ) :
    CenteredIsotropic (averagedLaw μ) (covariance μ) where
  positive_covariance := div_pos hpos (by norm_num)
  finite_second_moment := averaged_coordinate_memLp h2
  mean_zero := averaged_mean_zero h2
  covariance := averaged_covariance h2

end GeneratedFoundations.Geometry.SourceFiniteControlLaw
