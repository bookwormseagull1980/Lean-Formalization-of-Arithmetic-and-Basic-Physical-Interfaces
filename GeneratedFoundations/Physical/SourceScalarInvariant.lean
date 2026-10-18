module

public import GeneratedFoundations.Physical.SourceScalarGaugeCovariance
public import GeneratedFoundations.Physical.SourceVacuumTransport

/-!
# The intrinsic scalar amplitude of the source doublet

The reversal-real connector has one determinant, and that determinant is the
sum of the two source-mode norm squares.  The source gauge action preserves it
because both frame matrices have determinant one.  Together with the scalar
commutant classification, this identifies the quadratic amplitude carried by
the elementary source doublet without adding a second scalar datum.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceScalarInvariant

open ReversalRealConnector SourceScalarConnector
open SourceScalarGaugeCovariance

/-- Quadratic amplitude of the two generated scalar coordinates. -/
def scalarIntensity (H : Spinor) : ℝ :=
  Complex.normSq (H 0) + Complex.normSq (H 1)

theorem scalarIntensity_nonneg (H : Spinor) : 0 ≤ scalarIntensity H := by
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem scalarIntensity_eq_zero_iff (H : Spinor) :
    scalarIntensity H = 0 ↔ H = 0 := by
  constructor
  · intro h
    change Complex.normSq (H 0) + Complex.normSq (H 1) = 0 at h
    have h0 : Complex.normSq (H 0) = 0 := by
      nlinarith [Complex.normSq_nonneg (H 0), Complex.normSq_nonneg (H 1)]
    have h1 : Complex.normSq (H 1) = 0 := by
      nlinarith [Complex.normSq_nonneg (H 0), Complex.normSq_nonneg (H 1)]
    funext i
    fin_cases i
    · simpa using (Complex.normSq_eq_zero.mp h0)
    · simpa using (Complex.normSq_eq_zero.mp h1)
  · rintro rfl
    simp [scalarIntensity]

/-- The determinant of the reversal-real connector is the scalar intensity. -/
theorem det_connectorOfDoublet (H : Spinor) :
    Matrix.det (connectorOfDoublet H) = (scalarIntensity H : ℂ) := by
  apply Complex.ext <;>
    simp [connectorOfDoublet, Matrix.det_fin_two, scalarIntensity,
      Complex.normSq_apply] <;>
    ring

theorem det_gaugeMatrix (gL : Operations.SourceSpinCornerGroup.SU2)
    (z : Circle) (M : Operations.SourceSpinCorner.Mat2) :
    Matrix.det (gaugeMatrix gL z M) = Matrix.det M := by
  have hL : Matrix.det (gL : Operations.SourceSpinCorner.Mat2) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp gL.property).2
  have hRinv : Matrix.det
      (((SourcePhaseLift.stabilizerFrame z)⁻¹ : Operations.SourceSpinCornerGroup.SU2) :
        Operations.SourceSpinCorner.Mat2) = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp
      ((SourcePhaseLift.stabilizerFrame z)⁻¹).property).2
  rw [gaugeMatrix, Matrix.det_mul, Matrix.det_mul, hL, one_mul, hRinv, mul_one]

/-- The quadratic scalar amplitude is invariant under the complete source
gauge action; colour is absent because the connector shares its colour block. -/
theorem scalarIntensity_gauge_invariant
    (g : GlobalGaugeKernel.GaugeGroup) (H : Spinor) :
    scalarIntensity (SourceScalarGaugeCovariance.scalarAction g H) =
      scalarIntensity H := by
  have hm := congrArg Matrix.det
    (gaugeMatrix_doubletLift g.2.1 g.2.2 H)
  rw [det_gaugeMatrix, det_connectorOfDoublet, det_connectorOfDoublet] at hm
  apply Complex.ofReal_injective
  simpa [SourceScalarGaugeCovariance.scalarAction] using hm.symm

/-- The scalar amplitude, its connector determinant and its gauge invariance
are consequences of the existing source doublet and source action. -/
structure Conclusions : Prop where
  determinant : ∀ H : Spinor,
    Matrix.det (connectorOfDoublet H) = (scalarIntensity H : ℂ)
  definite : ∀ H : Spinor, scalarIntensity H = 0 ↔ H = 0
  gauge_invariant : ∀ (g : GlobalGaugeKernel.GaugeGroup) (H : Spinor),
    scalarIntensity (SourceScalarGaugeCovariance.scalarAction g H) =
      scalarIntensity H

theorem sourceScalarInvariantConclusions : Conclusions where
  determinant := det_connectorOfDoublet
  definite := scalarIntensity_eq_zero_iff
  gauge_invariant := scalarIntensity_gauge_invariant

end GeneratedFoundations.Physical.SourceScalarInvariant
