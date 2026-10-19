module

public import GeneratedFoundations.Correlation.GeneratedSourceWindow
public import GeneratedFoundations.Operations.HermiteSource

/-!
# The oscillator ground density of the original compositional law

The state overlap, correlation profile and oscillator ground state use three
different times of the same measure family.  This shared module supplies the
ground-state comparison before either branch is chosen.  In particular its
width normalization is not an identification of Hermite and Neumann
generators.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Source GeneratedFoundations.Probability
open GeneratedFoundations.Source.TraceLieGeometry
open GeneratedFoundations.Operations.HermiteSource

namespace GeneratedFoundations.Correlation.GeneratedSourceGround

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable {mu : ℝ → Measure (TraceLieSpace d h)} (hmu : HilbertCompositionalAxioms mu)

include hmu

theorem coordinate_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    (mu (b ^ 2 / 2)).map e =
      volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2)) :=
  (groundProfile_squared_measure (hmu.coordinate_axioms e) hb).symm

theorem original_density (e : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {b : ℝ} (hb : 0 < b) :
    mu (b ^ 2 / 2) =
      (volume.withDensity (fun y => ENNReal.ofReal (groundProfile b y ^ 2))).map e.symm := by
  rw [← coordinate_density d h hmu e hb, isometry_map_symm_map]

theorem coordinate_independent
    (e f : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ) {b : ℝ} (hb : 0 < b) :
    (mu (b ^ 2 / 2)).map e = (mu (b ^ 2 / 2)).map f := by
  rw [coordinate_density d h hmu e hb, coordinate_density d h hmu f hb]

end GeneratedFoundations.Correlation.GeneratedSourceGround
