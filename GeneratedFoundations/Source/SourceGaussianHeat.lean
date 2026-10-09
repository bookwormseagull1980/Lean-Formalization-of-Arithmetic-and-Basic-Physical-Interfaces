module

public import GeneratedFoundations.Source.OrientedTraceCoordinate
public import GeneratedFoundations.Source.SourceAngularFlow
public import GeneratedFoundations.Probability.GeneratedTangentLaw
public import GeneratedFoundations.Spectral.GaussianHeatKernel
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Gaussian averaging of the original change action

The average is a Bochner integral of the actual original-group action on the
whole Haar Hilbert space. Its Fourier coefficients are computed from the
compositional law on the original trace line. They identify this integral
with Gaussian convolution and, on the reflecting subspace, with the existing
Neumann heat operator.

The source parameter and the interval heat parameter differ by `(L / π)^2`.
This factor comes from the previously constructed spectral coordinate. At
zero the measure is the canonical continuous Dirac extension; the input law
is only constrained at positive parameters.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter InnerProductSpace
open scoped Topology NNReal

namespace GeneratedFoundations.Source.SourceGaussianHeat

open TraceLieGeometry CarrierOrientation GeneratedSpectralCircle SourceAngularFlow
open GeneratedFoundations.Probability GeneratedFoundations.Spectral
open GeneratedFoundations.Operations

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable (L : ℝ) [hL : Fact (0 < L)] (o : OrientationOnCarrier d)

/-- An original trace vector acts through its actual oriented integral curve. -/
def orbit (X : TraceLieSpace d h) (f : HaarCircleL2 L) : HaarCircleL2 L :=
  actualSourceAction d h L o
    (orientedFlow d h o (OrientedTraceCoordinate.coordinate d h o X)) f

/-- The coordinate expression is the exponential of the original tangent vector. -/
theorem orientedFlow_coordinate_eq_exponential (X : TraceLieSpace d h) :
    orientedFlow d h o (OrientedTraceCoordinate.coordinate d h o X) =
      OriginalLieFlow.lieExponential d X.tangent := by
  have hX := congrArg TraceLieSpace.tangent (OrientedTraceCoordinate.unit_decomposition d h o X)
  change OrientedTraceCoordinate.coordinate d h o X • (carrierUnit d h o).tangent =
    X.tangent at hX
  rw [← hX, OriginalLieFlow.lieExponential_smul]
  rfl

theorem orbit_eq_original_exponential (X : TraceLieSpace d h) (f : HaarCircleL2 L) :
    orbit d h L o X f = actualSourceAction d h L o
      (OriginalLieFlow.lieExponential d X.tangent) f := by
  rw [orbit, orientedFlow_coordinate_eq_exponential]

theorem orbit_continuous (f : HaarCircleL2 L) :
    Continuous (fun X : TraceLieSpace d h => orbit d h L o X f) :=
  (originalFlow_stronglyContinuous d h L o f).comp
    (OrientedTraceCoordinate.coordinate d h o).continuous

theorem orbit_norm (X : TraceLieSpace d h) (f : HaarCircleL2 L) :
    ‖orbit d h L o X f‖ = ‖f‖ := actualSourceAction_norm d h L o _ f

theorem orbit_integrable (ν : Measure (TraceLieSpace d h)) [IsFiniteMeasure ν]
    (f : HaarCircleL2 L) : Integrable (fun X => orbit d h L o X f) ν :=
  Integrable.of_bound (orbit_continuous d h L o f).aestronglyMeasurable ‖f‖
    (ae_of_all _ fun X => (orbit_norm d h L o X f).le)

theorem orbit_coefficient (X : TraceLieSpace d h) (f : HaarCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 n) (orbit d h L o X f) =
      AngularFlow.phase (OrientedTraceCoordinate.coordinate d h o X) n *
        inner ℂ (fourierLp 2 n) f := by
  have heq := congrArg (fun T : HaarCircleL2 L →L[ℂ] HaarCircleL2 L => T f)
    (actualSourceAction_orientedFlow d h L o
      (OrientedTraceCoordinate.coordinate d h o X))
  change orbit d h L o X f =
    AngularFlow.flow L (OrientedTraceCoordinate.coordinate d h o X) f at heq
  rw [heq, AngularFlow.flow_coefficient]

/-- The definition integrates the actual action, without prescribing multipliers. -/
def average (ν : Measure (TraceLieSpace d h)) (f : HaarCircleL2 L) : HaarCircleL2 L :=
  ∫ X, orbit d h L o X f ∂ν

theorem average_add (ν : Measure (TraceLieSpace d h)) [IsFiniteMeasure ν]
    (f g : HaarCircleL2 L) :
    average d h L o ν (f + g) = average d h L o ν f + average d h L o ν g := by
  simp only [average, orbit, map_add]
  exact integral_add (orbit_integrable d h L o ν f) (orbit_integrable d h L o ν g)

theorem average_smul (ν : Measure (TraceLieSpace d h)) (c : ℂ) (f : HaarCircleL2 L) :
    average d h L o ν (c • f) = c • average d h L o ν f := by
  simp only [average, orbit, map_smul, integral_smul]

theorem average_norm_le (ν : Measure (TraceLieSpace d h)) [IsProbabilityMeasure ν]
    (f : HaarCircleL2 L) : ‖average d h L o ν f‖ ≤ ‖f‖ := by
  have hn := norm_integral_le_of_norm_le_const
    (μ := ν) (ae_of_all ν fun X => (orbit_norm d h L o X f).le)
  simpa only [average, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using hn

/-- The integral is a contraction on the full Hilbert space. -/
def averageOperator (ν : Measure (TraceLieSpace d h)) [IsProbabilityMeasure ν] :
    HaarCircleL2 L →L[ℂ] HaarCircleL2 L :=
  ({ toFun := average d h L o ν
     map_add' := average_add d h L o ν
     map_smul' := fun c f => average_smul d h L o ν c f } :
       HaarCircleL2 L →ₗ[ℂ] HaarCircleL2 L).mkContinuous 1 (by
    intro f
    change ‖average d h L o ν f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using average_norm_le d h L o ν f)

theorem average_coefficient (ν : Measure (TraceLieSpace d h)) [IsFiniteMeasure ν]
    (f : HaarCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 n) (average d h L o ν f) =
      (∫ X, AngularFlow.phase (OrientedTraceCoordinate.coordinate d h o X) n ∂ν) *
        inner ℂ (fourierLp 2 n) f := by
  rw [average, ← integral_inner (orbit_integrable d h L o ν f)]
  simp_rw [orbit_coefficient]
  exact integral_mul_const _ _

theorem gaussian_phase_integral (v : ℝ≥0) (n : ℤ) :
    (∫ r : ℝ, AngularFlow.phase r n ∂gaussianReal 0 v) =
      (Real.exp (-(v : ℝ) * (n : ℝ) ^ 2 / 2) : ℂ) := by
  calc
    _ = charFun (gaussianReal 0 v) (n : ℝ) := by
      unfold charFun
      apply integral_congr_ae
      filter_upwards [] with r
      unfold AngularFlow.phase
      change Complex.exp (Complex.I * (((n : ℝ) * r : ℝ) : ℂ)) =
        Complex.exp ((((n : ℝ) * r : ℝ) : ℂ) * Complex.I)
      rw [mul_comm]
    _ = _ := by
      rw [charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      push_cast
      ring

variable {μ : ℝ → Measure (TraceLieSpace d h)} (hμ : HilbertCompositionalAxioms μ)

include hμ in
/-- Equality of actual integrals along the source flow, before taking coefficients. -/
theorem average_eq_gaussian_integral {τ : ℝ} (hτ : 0 < τ) (f : HaarCircleL2 L) :
    average d h L o (μ τ) f =
      ∫ r : ℝ, actualSourceAction d h L o (orientedFlow d h o r) f
        ∂gaussianReal 0 (NNReal.mk τ hτ.le) := by
  rw [← hμ.coordinate_law (OrientedTraceCoordinate.coordinate d h o) hτ]
  exact ((OrientedTraceCoordinate.coordinate d h o).toHomeomorph.measurableEmbedding.integral_map
    (fun r : ℝ => actualSourceAction d h L o (orientedFlow d h o r) f)).symm

include hμ in
theorem source_phase_integral {τ : ℝ} (hτ : 0 < τ) (n : ℤ) :
    (∫ X, AngularFlow.phase (OrientedTraceCoordinate.coordinate d h o X) n ∂μ τ) =
      (Real.exp (-τ * (n : ℝ) ^ 2 / 2) : ℂ) := by
  calc
    _ = ∫ r : ℝ, AngularFlow.phase r n
        ∂Measure.map (OrientedTraceCoordinate.coordinate d h o) (μ τ) :=
      ((OrientedTraceCoordinate.coordinate d h o).toHomeomorph.measurableEmbedding.integral_map
        (fun r : ℝ => AngularFlow.phase r n)).symm
    _ = _ := by
      rw [hμ.coordinate_law (OrientedTraceCoordinate.coordinate d h o) hτ]
      exact gaussian_phase_integral (NNReal.mk τ hτ.le) n

include hμ in
theorem source_average_coefficient {τ : ℝ} (hτ : 0 < τ)
    (f : HaarCircleL2 L) (n : ℤ) :
    inner ℂ (fourierLp 2 n) (average d h L o (μ τ) f) =
      (Real.exp (-τ * (n : ℝ) ^ 2 / 2) : ℂ) * inner ℂ (fourierLp 2 n) f := by
  let : IsProbabilityMeasure (μ τ) := hμ.probability τ hτ
  rw [average_coefficient, source_phase_integral d h o hμ hτ]

/-- The original trace coordinate has displacement `(L / π) r` on the spectral circle. -/
def spatialWidth (τ : ℝ) : ℝ := L / Real.pi * Real.sqrt τ

theorem spatialWidth_pos {τ : ℝ} (hτ : 0 < τ) : 0 < spatialWidth L τ :=
  mul_pos (div_pos hL.out Real.pi_pos) (Real.sqrt_pos.mpr hτ)

theorem multiplier_calibration {τ : ℝ} (hτ : 0 ≤ τ) (n : ℤ) :
    -2 * Real.pi ^ 2 * (spatialWidth L τ / (2 * L)) ^ 2 * (n : ℝ) ^ 2 =
      -τ * (n : ℝ) ^ 2 / 2 := by
  have hquot : spatialWidth L τ / (2 * L) = Real.sqrt τ / (2 * Real.pi) := by
    unfold spatialWidth
    field_simp [hL.out.ne', Real.pi_ne_zero]
  rw [hquot, div_pow, Real.sq_sqrt hτ, mul_pow]
  field_simp [Real.pi_ne_zero]

include hμ in
/-- The same actual source integral is the Gaussian convolution on every L2 input. -/
theorem source_average_eq_convolution {τ : ℝ} (hτ : 0 < τ) (f : HaarCircleL2 L) :
    average d h L o (μ τ) f =
      GaussianHeatConvolution.convolution (2 * L) (spatialWidth L τ) f := by
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro n
  simp only [coe_fourierBasis, source_average_coefficient d h L o hμ hτ,
    ← GaussianHeatConvolution.fourierCoeff_eq_inner,
    GaussianHeatConvolution.convolution_fourierCoeff_gaussian (2 * L)
      (spatialWidth_pos L hτ), multiplier_calibration L hτ.le]

/-- Neumann's spatial heat parameter induced by the original source parameter. -/
def heatParameter (τ : ℝ≥0) : ℝ≥0 :=
  ⟨(L / Real.pi) ^ 2 * (τ : ℝ), mul_nonneg (sq_nonneg _) τ.property⟩

omit hL in
@[simp] theorem heatParameter_coe (τ : ℝ≥0) :
    (heatParameter L τ : ℝ) = (L / Real.pi) ^ 2 * (τ : ℝ) := rfl

omit hL in
@[simp] theorem heatParameter_zero : heatParameter L 0 = 0 := by
  apply NNReal.eq
  simp only [heatParameter_coe, NNReal.coe_zero, mul_zero]

omit hL in
theorem heatParameter_add (s t : ℝ≥0) :
    heatParameter L (s + t) = heatParameter L s + heatParameter L t := by
  apply NNReal.eq
  simp only [heatParameter_coe, NNReal.coe_add, mul_add]

/-- The source parameter corresponding to a specified spatial heat parameter. -/
def sourceParameter (s : ℝ≥0) : ℝ≥0 :=
  ⟨(Real.pi / L) ^ 2 * (s : ℝ), mul_nonneg (sq_nonneg _) s.property⟩

omit hL in
@[simp] theorem sourceParameter_coe (s : ℝ≥0) :
    (sourceParameter L s : ℝ) = (Real.pi / L) ^ 2 * (s : ℝ) := rfl

theorem sourceParameter_pos {s : ℝ≥0} (hs : 0 < s) : 0 < sourceParameter L s :=
  mul_pos (sq_pos_of_pos (div_pos Real.pi_pos hL.out)) hs

@[simp] theorem heatParameter_sourceParameter (s : ℝ≥0) :
    heatParameter L (sourceParameter L s) = s := by
  apply NNReal.eq
  simp only [heatParameter_coe, sourceParameter_coe]
  field_simp [hL.out.ne', Real.pi_ne_zero]

@[simp] theorem sourceParameter_heatParameter (τ : ℝ≥0) :
    sourceParameter L (heatParameter L τ) = τ := by
  apply NNReal.eq
  simp only [heatParameter_coe, sourceParameter_coe]
  field_simp [hL.out.ne', Real.pi_ne_zero]

omit hL in
theorem variance_spatialWidth (τ : ℝ≥0) :
    GaussianHeatKernel.variance (spatialWidth L τ) = heatParameter L τ := by
  apply NNReal.eq
  change (L / Real.pi * Real.sqrt (τ : ℝ)) ^ 2 = (L / Real.pi) ^ 2 * (τ : ℝ)
  rw [mul_pow]
  exact congrArg (fun r : ℝ => (L / Real.pi) ^ 2 * r) (Real.sq_sqrt τ.property)

include hμ in
theorem source_average_reflecting {τ : ℝ≥0} (hτ : 0 < τ)
    (f : ComplexIntervalL2 0 L) :
    average d h L o (μ (τ : ℝ)) (reflectingHaarIsometry L f) =
      reflectingHaarIsometry L (NeumannHeatSemigroup.heat L (heatParameter L τ) f) := by
  calc
    _ = GaussianHeatConvolution.convolution (2 * L) (spatialWidth L τ)
        (reflectingHaarIsometry L f) :=
      source_average_eq_convolution d h L o hμ hτ _
    _ = reflectingHaarIsometry L
        (NeumannHeatSemigroup.heat L (GaussianHeatKernel.variance (spatialWidth L τ)) f) :=
      GaussianHeatKernel.convolution_reflecting_eq_heat L (spatialWidth_pos L hτ) f
    _ = _ := congrArg
      (fun s : ℝ≥0 => reflectingHaarIsometry L (NeumannHeatSemigroup.heat L s f))
      (variance_spatialWidth L τ)

/-- The continuous extension supplies the zero-parameter law. -/
def extendedLaw (τ : ℝ≥0) : ProbabilityMeasure (TraceLieSpace d h) :=
  hμ.extension (OrientedTraceCoordinate.coordinate d h o) τ

theorem extendedLaw_zero : (extendedLaw d h o hμ 0 : Measure (TraceLieSpace d h)) =
    Measure.dirac 0 := hμ.extension_zero (OrientedTraceCoordinate.coordinate d h o)

theorem extendedLaw_pos {τ : ℝ≥0} (hτ : 0 < τ) :
    (extendedLaw d h o hμ τ : Measure (TraceLieSpace d h)) = μ (τ : ℝ) :=
  hμ.extension_eq (OrientedTraceCoordinate.coordinate d h o) hτ

theorem extended_average_zero (f : HaarCircleL2 L) :
    average d h L o (extendedLaw d h o hμ 0) f = f := by
  rw [extendedLaw_zero]
  simp only [average, integral_dirac, orbit, map_zero, orientedFlow_zero,
    actualSourceAction_one]

/-- The reflecting identity includes zero without constraining the original `μ 0`. -/
theorem extended_average_reflecting (τ : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    average d h L o (extendedLaw d h o hμ τ) (reflectingHaarIsometry L f) =
      reflectingHaarIsometry L (NeumannHeatSemigroup.heat L (heatParameter L τ) f) := by
  by_cases hτ : τ = 0
  · simp only [hτ, extended_average_zero, heatParameter_zero, NeumannHeatSemigroup.heat_zero]
  · rw [extendedLaw_pos d h o hμ (pos_iff_ne_zero.mpr hτ)]
    exact source_average_reflecting d h L o hμ (pos_iff_ne_zero.mpr hτ) f

theorem extended_average_at_spatial_parameter (s : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    average d h L o (extendedLaw d h o hμ (sourceParameter L s))
      (reflectingHaarIsometry L f) =
      reflectingHaarIsometry L (NeumannHeatSemigroup.heat L s f) := by
  simpa only [heatParameter_sourceParameter] using
    extended_average_reflecting d h L o hμ (sourceParameter L s) f

include hμ in
theorem source_average_at_spatial_parameter {s : ℝ≥0} (hs : 0 < s)
    (f : ComplexIntervalL2 0 L) :
    average d h L o (μ (sourceParameter L s : ℝ)) (reflectingHaarIsometry L f) =
      reflectingHaarIsometry L (NeumannHeatSemigroup.heat L s f) := by
  simpa only [heatParameter_sourceParameter] using
    source_average_reflecting d h L o hμ (sourceParameter_pos L hs) f

theorem extended_average_add_reflecting (s t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    average d h L o (extendedLaw d h o hμ (s + t)) (reflectingHaarIsometry L f) =
      average d h L o (extendedLaw d h o hμ s)
        (average d h L o (extendedLaw d h o hμ t) (reflectingHaarIsometry L f)) := by
  simp only [extended_average_reflecting, heatParameter_add, NeumannHeatSemigroup.heat_add]

include hμ in
theorem source_average_orientation_independent {τ : ℝ} (hτ : 0 < τ)
    (p : OrientationOnCarrier d) (f : HaarCircleL2 L) :
    average d h L o (μ τ) f = average d h L p (μ τ) f := by
  rw [source_average_eq_convolution d h L o hμ hτ,
    source_average_eq_convolution d h L p hμ hτ]

end GeneratedFoundations.Source.SourceGaussianHeat
