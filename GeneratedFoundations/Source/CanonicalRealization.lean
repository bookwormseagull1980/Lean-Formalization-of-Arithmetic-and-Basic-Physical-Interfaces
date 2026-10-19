module

public import GeneratedFoundations.Correlation.GeneratedSourceWindow
public import GeneratedFoundations.Source.CanonicalRoot
public import GeneratedFoundations.Source.CarrierOrientation

/-!
# The zero-input realization of the canonical root

The normalized compositional law already distinguishes its unit-variance
parameter.  Since a Gaussian profile of positive width `b` is the same source
law at parameter `b^2`, the corresponding root width is `1`; it is not an
additional scale convention.  The canonical representative has carrier `C`
and its original circle action is complex multiplication, so its complex
orientation supplies the presentation orientation without a caller choice.

The abstract minimal datum is reflection symmetric.  Consequently no theorem
below claims an orientation fixed by every automorphism of the unoriented
datum.  Instead the canonical representative supplies one orientation and the
existing reversal theorems identify the other presentation as its conjugate.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open GeneratedFoundations.Probability
open GeneratedFoundations.Correlation
open GeneratedFoundations.Correlation.Endpoints
open GeneratedFoundations.Source.CarrierOrientation
open scoped ComplexConjugate

namespace GeneratedFoundations.Source.CanonicalRealization

/-- The parameter singled out by unit covariance in the root axioms. -/
def varianceParameter : ℝ := 1

/-- The positive Gaussian width whose square is the unit-variance parameter. -/
def width : ℝ := 1

@[simp] theorem varianceParameter_eq_one : varianceParameter = 1 := rfl

@[simp] theorem width_eq_one : width = 1 := rfl

theorem width_pos : 0 < width := by
  norm_num [width]

@[simp] theorem width_sq : width ^ 2 = varianceParameter := by
  norm_num [width, varianceParameter]

/-- Unit covariance fixes the positive profile width uniquely. -/
theorem width_unique {b : ℝ} (hb : 0 < b)
    (hparameter : b ^ 2 = varianceParameter) : b = width := by
  rw [varianceParameter_eq_one] at hparameter
  rw [width_eq_one]
  nlinarith

/-- The canonical carrier is definitionally the complex plane; its identity
coordinate is therefore produced by the canonical root itself. -/
def carrierCoordinate :
    CanonicalRoot.generated.change.Carrier ≃ₗᵢ[ℝ] ℂ :=
  LinearIsometryEquiv.refl ℝ ℂ

/-- The orientation carried by the canonical complex rotation presentation. -/
def orientation : OrientationOnCarrier CanonicalRoot.generated.change :=
  coordinateOrientation CanonicalRoot.generated.change carrierCoordinate

/-- The selected quarter turn is the infinitesimal generator of the original
canonical circle action, rather than an independently supplied sign. -/
theorem quarterTurn_eq_generator :
    carrierQuarterTurn CanonicalRoot.generated.change
        CanonicalRoot.generated.minimal orientation =
      PlaneGenerator.generator carrierCoordinate := by
  exact carrierQuarterTurn_coordinate CanonicalRoot.generated.change
    CanonicalRoot.generated.minimal carrierCoordinate

/-- Every carrier orientation is either the canonical presentation or its
reflection.  Thus there is no unaccounted third realization. -/
theorem orientation_cases
    (o : OrientationOnCarrier CanonicalRoot.generated.change) :
    o = orientation ∨ o = -orientation :=
  carrier_orientation_cases CanonicalRoot.generated.change
    CanonicalRoot.generated.minimal o orientation

/-- Reversal conjugates the canonical Hermitian structure exactly. -/
theorem sourceHermitian_reverse (v w : CanonicalRoot.generated.change.Carrier) :
    ComplexStructure.sourceHermitian
        (carrierQuarterTurn CanonicalRoot.generated.change
          CanonicalRoot.generated.minimal (-orientation)) v w =
      conj (ComplexStructure.sourceHermitian
        (carrierQuarterTurn CanonicalRoot.generated.change
          CanonicalRoot.generated.minimal orientation) v w) := by
  exact carrier_sourceHermitian_reverse CanonicalRoot.generated.change
    CanonicalRoot.generated.minimal orientation v w

/-- The root law used by the canonical profile is exactly its distinguished
unit-variance law. -/
theorem law_at_width :
    CanonicalRoot.generated.law (width ^ 2) =
      CanonicalRoot.generated.law varianceParameter := by
  rw [width_sq]

/-- The natural endpoints contain no remaining positive scale parameter once
the unit-covariance realization is selected. -/
theorem endpoints :
    uvEndpoint width = Real.sqrt 2 ∧
      irEndpoint width = Real.sqrt (2 * Real.pi) ∧
      windowLength width = Real.sqrt (2 * Real.pi) - Real.sqrt 2 := by
  constructor
  · simpa [width] using uvEndpoint_eq width_pos
  constructor
  · simpa [width] using irEndpoint_eq width_pos
  · simpa [width] using windowLength_eq width_pos

theorem windowLength_pos : 0 < windowLength width :=
  Endpoints.windowLength_pos width_pos

end GeneratedFoundations.Source.CanonicalRealization
