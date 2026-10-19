module

public import GeneratedFoundations.Source.CanonicalRealization
public import GeneratedFoundations.Source.OrientedTraceCoordinate
public import GeneratedFoundations.Correlation.GeneratedSourceGround

/-!
# The common source before the arithmetic and physical branches

The carrier, law and orientation below are the very same canonical objects
used by both branches.  This entry records the whole source chain through the
state correlation and its natural window.  It imports neither branch.

`generated` has no arguments.  Positive observation times and competing laws
occur only inside its conclusions; they do not supply a second source.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Probability
open GeneratedFoundations.Correlation
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Correlation.Endpoints

namespace GeneratedFoundations.Source.CommonSource

abbrev Carrier := CanonicalRoot.generated.change.Carrier

abbrev Line := TraceLieGeometry.TraceLieSpace
  CanonicalRoot.generated.change CanonicalRoot.generated.minimal

def coordinate : Line ≃ₗᵢ[ℝ] ℝ :=
  OrientedTraceCoordinate.coordinate CanonicalRoot.generated.change
    CanonicalRoot.generated.minimal CanonicalRealization.orientation

theorem same_source_window :
    (CanonicalRoot.generated.law (CanonicalRealization.width ^ 2)).map coordinate =
        volume.withDensity (fun y =>
          ENNReal.ofReal (changeKernel CanonicalRealization.width y)) ∧
      (CanonicalRoot.generated.law (CanonicalRealization.width ^ 2 / 4)).map coordinate =
        volume.withDensity (fun y =>
          ENNReal.ofReal (state CanonicalRealization.width 0 y ^ 2)) ∧
      (∀ x z : ℝ, overlap CanonicalRealization.width x z =
        profile CanonicalRealization.width (x - z)) ∧
      uvEndpoint CanonicalRealization.width = Real.sqrt 2 * CanonicalRealization.width ∧
      irEndpoint CanonicalRealization.width =
        Real.sqrt (2 * Real.pi) * CanonicalRealization.width ∧
      windowLength CanonicalRealization.width =
        CanonicalRealization.width * (Real.sqrt (2 * Real.pi) - Real.sqrt 2) ∧
      0 < windowLength CanonicalRealization.width :=
  GeneratedSourceWindow.same_source_window CanonicalRoot.generated.change
    CanonicalRoot.generated.minimal CanonicalRoot.generated.compositional
    coordinate CanonicalRealization.width_pos

structure Conclusions : Prop where
  minimal : MinimalCarrier.IsMinimal CanonicalRoot.generated.change
  compositional : HilbertCompositionalAxioms CanonicalRoot.generated.law
  unique_law : ∀ (nu : ℝ → Measure Line), HilbertCompositionalAxioms nu →
    ∀ t : ℝ, 0 < t → CanonicalRoot.generated.law t = nu t
  normalized_width : CanonicalRealization.width = 1
  profile_density :
    (CanonicalRoot.generated.law (CanonicalRealization.width ^ 2)).map coordinate =
      volume.withDensity (fun y =>
        ENNReal.ofReal (changeKernel CanonicalRealization.width y))
  state_density :
    (CanonicalRoot.generated.law (CanonicalRealization.width ^ 2 / 4)).map coordinate =
      volume.withDensity (fun y =>
        ENNReal.ofReal (state CanonicalRealization.width 0 y ^ 2))
  ground_density :
    (CanonicalRoot.generated.law (CanonicalRealization.width ^ 2 / 2)).map coordinate =
      volume.withDensity (fun y => ENNReal.ofReal
        (Operations.HermiteSource.groundProfile CanonicalRealization.width y ^ 2))
  state_correlation : ∀ x z : ℝ,
    overlap CanonicalRealization.width x z = profile CanonicalRealization.width (x - z)
  natural_endpoints :
    uvEndpoint CanonicalRealization.width = Real.sqrt 2 ∧
      irEndpoint CanonicalRealization.width = Real.sqrt (2 * Real.pi) ∧
      windowLength CanonicalRealization.width = Real.sqrt (2 * Real.pi) - Real.sqrt 2
  positive_window : 0 < windowLength CanonicalRealization.width

theorem generated : Conclusions where
  minimal := CanonicalRoot.generated.minimal
  compositional := CanonicalRoot.generated.compositional
  unique_law := CanonicalRoot.law_unique CanonicalRoot.canonical
  normalized_width := CanonicalRealization.width_eq_one
  profile_density := same_source_window.1
  state_density := same_source_window.2.1
  ground_density := GeneratedSourceGround.coordinate_density CanonicalRoot.generated.change
    CanonicalRoot.generated.minimal CanonicalRoot.generated.compositional coordinate
    CanonicalRealization.width_pos
  state_correlation := same_source_window.2.2.1
  natural_endpoints := CanonicalRealization.endpoints
  positive_window := CanonicalRealization.windowLength_pos

end GeneratedFoundations.Source.CommonSource
