module

public import GeneratedFoundations.Arithmetic.HistoryGaugeJets
public import GeneratedFoundations.Arithmetic.HistoryEvenResponse

/-!
# Adjoint transport on the original arithmetic source fibre

The adjoint field acts on the same complete history--phase carrier as the
connection. Its transformed derivative is the full product derivative.
The common covariant derivative and trace pairing then transform exactly.
History responses and source connectors retain their independent factors;
commutation does not remove their joint two-insertion trace.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Kronecker Matrix

namespace GeneratedFoundations.Arithmetic.HistoryAdjointTransport

open HistoryGaugeJets
open Geometry.ConnectionJetAlgebra (inverseDerivative)

def covariantJet (N : ℕ) (A X dX : Operator N) : Operator N := dX + (A * X - X * A)

def transformFieldJet (N : ℕ) (q : GaugeTwoJet N) (μ : CoordinateIndex N)
    (X dX : Operator N) : Operator N :=
  inverseDerivative (algebraicGaugeJet N q) μ * X * ↑(frameUnits N q.value) +
    ↑(frameUnits N q.value)⁻¹ * dX * ↑(frameUnits N q.value) +
    ↑(frameUnits N q.value)⁻¹ * X * q.first μ

theorem covariantJet_transform (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N)
    (μ : CoordinateIndex N) (X dX : Operator N) :
    covariantJet N (transformConnectionJet N q A |>.value μ)
      (conjugate N q.value X) (transformFieldJet N q μ X dX) =
      conjugate N q.value (covariantJet N (A.value μ) X dX) := by
  have huv : (↑(frameUnits N q.value) : Operator N) *
      ↑(frameUnits N q.value)⁻¹ = 1 := Units.mul_inv _
  have hvu : (↑(frameUnits N q.value)⁻¹ : Operator N) *
      ↑(frameUnits N q.value) = 1 := Units.inv_mul _
  have huv_assoc (Y : Operator N) : (↑(frameUnits N q.value) : Operator N) *
      (↑(frameUnits N q.value)⁻¹ * Y) = Y := by rw [← mul_assoc, huv, one_mul]
  have hvu_assoc (Y : Operator N) : (↑(frameUnits N q.value)⁻¹ : Operator N) *
      (↑(frameUnits N q.value) * Y) = Y := by rw [← mul_assoc, hvu, one_mul]
  simp only [covariantJet, transformConnectionJet, Geometry.ConnectionJetAlgebra.transform,
    conjugate, Geometry.ConnectionJetAlgebra.conjugate, transformFieldJet, inverseDerivative,
    algebraicGaugeJet]
  noncomm_ring [huv, hvu, huv_assoc, hvu_assoc]

theorem kinetic_gauge_invariant (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N)
    (μ : CoordinateIndex N) (X dX : Operator N) :
    quadratic N (covariantJet N (transformConnectionJet N q A |>.value μ)
      (conjugate N q.value X) (transformFieldJet N q μ X dX)) =
      quadratic N (covariantJet N (A.value μ) X dX) := by
  rw [covariantJet_transform, quadratic_conjugate]

/-- The complete covariant square retains both current terms. -/
theorem kinetic_expansion (N : ℕ) (A X dX : Operator N) :
    quadratic N (covariantJet N A X dX) =
      quadratic N dX + quadratic N (A * X - X * A) +
        (LinearMap.trace ℂ (HistoryCliffordAction.Space N)
          (dX.adjoint * (A * X - X * A) +
            (A * X - X * A).adjoint * dX)).re := by
  simp only [covariantJet, quadratic, Geometry.HilbertTraceQuadratic.energy,
    ← LinearMap.star_eq_adjoint, add_mul, mul_add, map_add, Complex.add_re]
  ring

def kineticDensity (N : ℕ) (A : ConnectionJet N) (X : CoordinateIndex N → Operator N)
    (dX : CoordinateIndex N → CoordinateIndex N → Operator N) : ℝ :=
  ∑ μ, ∑ r, quadratic N (covariantJet N (A.value μ) (X r) (dX μ r))

theorem kineticDensity_gauge_invariant (N : ℕ) (q : GaugeTwoJet N)
    (A : ConnectionJet N) (X : CoordinateIndex N → Operator N)
    (dX : CoordinateIndex N → CoordinateIndex N → Operator N) :
    kineticDensity N (transformConnectionJet N q A)
      (fun r => conjugate N q.value (X r))
      (fun μ r => transformFieldJet N q μ (X r) (dX μ r)) = kineticDensity N A X dX := by
  unfold kineticDensity
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro r _
  exact kinetic_gauge_invariant N q A μ (X r) (dX μ r)

open HistoryCliffordAction (HistoryLabel historyLift)
open HistoryComplexConnector (connector)

theorem history_connector_commute (N : ℕ)
    (H : Matrix (HistoryLabel N) (HistoryLabel N) ℂ)
    (M : Operations.SourceSpinCorner.Mat2) :
    historyLift N H * connector N M = connector N M * historyLift N H := by
  simp [historyLift, connector, ← Matrix.mul_kronecker_mul]

theorem single_history_trace_zero (N : ℕ)
    (H : Matrix (HistoryLabel N) (HistoryLabel N) ℂ) (hH : Matrix.trace H = 0)
    (M : Operations.SourceSpinCorner.Mat2) :
    Matrix.trace (historyLift N H * (connector N M)ᴴ * connector N M) = 0 := by
  simp [historyLift, connector, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, hH]

theorem mixed_history_trace (N : ℕ)
    (H : Matrix (HistoryLabel N) (HistoryLabel N) ℂ)
    (M : Operations.SourceSpinCorner.Mat2) :
    Matrix.trace ((historyLift N H)ᴴ * historyLift N H *
      (connector N M)ᴴ * connector N M) =
      Matrix.trace (Hᴴ * H) *
        Matrix.trace ((Operations.SourceCliffordComplex.connector M)ᴴ *
          Operations.SourceCliffordComplex.connector M) := by
  simp [historyLift, connector, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]

structure Conclusions : Prop where
  original_covariance : ∀ N q A μ X dX,
    covariantJet N (transformConnectionJet N q A |>.value μ)
      (conjugate N q.value X) (transformFieldJet N q μ X dX) =
      conjugate N q.value (covariantJet N (A.value μ) X dX)
  invariant_pairing : ∀ N q A μ X dX,
    quadratic N (covariantJet N (transformConnectionJet N q A |>.value μ)
      (conjugate N q.value X) (transformFieldJet N q μ X dX)) =
      quadratic N (covariantJet N (A.value μ) X dX)
  independent_factor_commutation : ∀ N H M,
    historyLift N H * connector N M = connector N M * historyLift N H
  complete_mixed_trace : ∀ N H M,
    Matrix.trace ((historyLift N H)ᴴ * historyLift N H *
      (connector N M)ᴴ * connector N M) =
      Matrix.trace (Hᴴ * H) *
        Matrix.trace ((Operations.SourceCliffordComplex.connector M)ᴴ *
          Operations.SourceCliffordComplex.connector M)

theorem generated : Conclusions where
  original_covariance := covariantJet_transform
  invariant_pairing := kinetic_gauge_invariant
  independent_factor_commutation := history_connector_commute
  complete_mixed_trace := mixed_history_trace

end GeneratedFoundations.Arithmetic.HistoryAdjointTransport
