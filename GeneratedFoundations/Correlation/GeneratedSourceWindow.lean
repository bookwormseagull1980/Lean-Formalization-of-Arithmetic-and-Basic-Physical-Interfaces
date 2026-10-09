module

public import GeneratedFoundations.Probability.GeneratedTangentLaw
public import GeneratedFoundations.Correlation.Endpoints

/-!
# The correlation window of the original generated source

The data `d`, `h`, `μ`, and `hμ` jointly express minimal unbiased
compositional change on the original trace Lie line. A real isometric
coordinate, which an orientation can select, and a positive width `b`
index its realizations. The coordinate law has variance `b²` at the
profile scale, while the square of the normalized overlap amplitude has
variance `b² / 4`. Both densities are derived from this same law.

At each positive width, the correlation construction determines the
overlap, both endpoints and the retained length. These endpoints feed the
internally constructed reflecting spectral closure and downstream
arithmetic and physical interfaces; no endpoint, boundary operator or
physical carrier is supplied to the results here. The final existence
statement obtains a coordinate from the original minimal action which
works for every positive width. The construction selects no absolute
positive scale.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open GeneratedFoundations.Probability
open GeneratedFoundations.Source
open GeneratedFoundations.Source.TraceLieGeometry
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Correlation.Endpoints

namespace GeneratedFoundations.Correlation.GeneratedSourceWindow

/-- The squared overlap amplitude has one quarter of the profile variance. -/
def amplitudeVariance (b : ℝ) : ℝ≥0 := ⟨b ^ 2 / 4, by positivity⟩

@[simp] theorem amplitudeVariance_coe (b : ℝ) :
    (amplitudeVariance b : ℝ) = b ^ 2 / 4 := rfl

/-- This calculation concerns the actual normalized function used in the overlap. -/
theorem state_sq_eq_gaussianPDFReal {b : ℝ} (hb : 0 < b) (y : ℝ) :
    state b 0 y ^ 2 = gaussianPDFReal 0 (amplitudeVariance b) y := by
  have hm := normalizationMass_pos hb
  have hmass : normalizationMass b = Real.sqrt (2 * Real.pi * (b ^ 2 / 4)) := by
    rw [normalizationMass_eq]
    congr 1
    field_simp [hb.ne']
    ring
  have hexp : rawState b 0 y ^ 2 = Real.exp (-y ^ 2 / (2 * (b ^ 2 / 4))) := by
    simp only [rawState, sub_zero]
    rw [pow_two, ← Real.exp_add]
    congr 1
    field_simp [hb.ne']
    ring
  change (rawState b 0 y / Real.sqrt (normalizationMass b)) ^ 2 = _
  rw [div_pow, Real.sq_sqrt hm.le, hexp, hmass]
  simp only [gaussianPDFReal, amplitudeVariance_coe, sub_zero]
  ring

/-- The amplitude is generated at its stated parameter within the same family. -/
theorem state_squared_measure {ν : ℝ → Measure ℝ}
    (hν : CompositionalGaussianAxioms ν) {b : ℝ} (hb : 0 < b) :
    volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2)) = ν (b ^ 2 / 4) := by
  rw [hν.law_eq_withDensity (t := b ^ 2 / 4) (by positivity)]
  congr 1
  funext y
  rw [state_sq_eq_gaussianPDFReal hb]
  rfl

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable {μ : ℝ → Measure (TraceLieSpace d h)} (hμ : HilbertCompositionalAxioms μ)

include hμ

/-- The profile density is the coordinate image of the actual trace-line law. -/
theorem coordinate_profile_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2)).map e =
      volume.withDensity (fun y => ENNReal.ofReal (changeKernel b y)) :=
  sourceLaw_eq_profileDensity (hμ.coordinate_axioms e) hb

/-- The same coordinate and family also supply the squared overlap amplitude. -/
theorem coordinate_state_squared_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2 / 4)).map e =
      volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2)) :=
  (state_squared_measure (hμ.coordinate_axioms e) hb).symm

/-- The comparison identifies the original measure, not merely its moments. -/
theorem source_profile_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    μ (b ^ 2) =
      (volume.withDensity (fun y => ENNReal.ofReal (changeKernel b y))).map e.symm := by
  rw [← coordinate_profile_density d h hμ e hb, isometry_map_symm_map]

theorem source_state_squared_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    μ (b ^ 2 / 4) =
      (volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2))).map e.symm := by
  rw [← coordinate_state_squared_density d h hμ e hb, isometry_map_symm_map]

/-- Both densities are independent of the isometric coordinate, including its sign. -/
theorem coordinate_densities_independent
    (e f : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ) {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2)).map e = (μ (b ^ 2)).map f ∧
      (μ (b ^ 2 / 4)).map e = (μ (b ^ 2 / 4)).map f := by
  constructor
  · rw [coordinate_profile_density d h hμ e hb, coordinate_profile_density d h hμ f hb]
  · rw [coordinate_state_squared_density d h hμ e hb,
      coordinate_state_squared_density d h hμ f hb]

/-- At each positive width, the same root law determines both densities,
the overlap and the endpoints of the generated window. -/
theorem same_source_window (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    (μ (b ^ 2)).map e =
        volume.withDensity (fun y => ENNReal.ofReal (changeKernel b y)) ∧
      (μ (b ^ 2 / 4)).map e =
        volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2)) ∧
      (∀ x z : ℝ, overlap b x z = profile b (x - z)) ∧
      uvEndpoint b = Real.sqrt 2 * b ∧
      irEndpoint b = Real.sqrt (2 * Real.pi) * b ∧
      windowLength b = b * (Real.sqrt (2 * Real.pi) - Real.sqrt 2) ∧
      0 < windowLength b :=
  ⟨coordinate_profile_density d h hμ e hb,
    coordinate_state_squared_density d h hμ e hb,
    overlap_eq_profile hb, uvEndpoint_eq hb, irEndpoint_eq hb,
    windowLength_eq hb, windowLength_pos hb⟩

/-- A coordinate obtained from the original action realizes the same root
law at every positive width; a separate coordinate is not required at each scale. -/
theorem source_window_coordinate_exists :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
      (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v),
      ∀ (b : ℝ), 0 < b →
        (μ (b ^ 2)).map (phaseIsometry d h e χ hχ haction) =
            volume.withDensity (fun y => ENNReal.ofReal (changeKernel b y)) ∧
        (μ (b ^ 2 / 4)).map (phaseIsometry d h e χ hχ haction) =
            volume.withDensity (fun y => ENNReal.ofReal (state b 0 y ^ 2)) := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  refine ⟨e, χ, hχ, haction, ?_⟩
  intro b hb
  exact ⟨coordinate_profile_density d h hμ (phaseIsometry d h e χ hχ haction) hb,
    coordinate_state_squared_density d h hμ (phaseIsometry d h e χ hχ haction) hb⟩

end GeneratedFoundations.Correlation.GeneratedSourceWindow
