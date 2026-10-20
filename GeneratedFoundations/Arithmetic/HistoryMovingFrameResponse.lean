module

public import GeneratedFoundations.Arithmetic.HistoryCoupledAction

/-!
# Moving frames on the complete arithmetic state carrier

A connection-value norm is not invariant under a local change of frame.
The frame and its derivative must be transported at the same time as the
connection. Here both act on the complete generated history--phase/source
space. The inhomogeneous terms cancel in the covariant frame derivative.

The trace response is the sum of the existing covariant state responses
over an entire orthonormal basis. Its coefficient is therefore fixed by
the already calculated defining response. No physical colour dimension
or additional coupling is used. A frame jet is a local presentation of
the generated group action; it is not an additional datum at the root.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryMovingFrameResponse

open HistoryCliffordAction (Space)
open HistoryElementaryConnector (Frame)
open HistoryEffectiveFrames (stateResponse)
open HistoryGaugeJets

structure FrameJet (N : ℕ) where
  value : Frame
  derivative : CoordinateIndex N → Operator N

def sourceFrame (N : ℕ) : FrameJet N := ⟨1, fun _ => 0⟩

/-- The full inverse product rule, with the same gauge jet as the connection. -/
def transformFrameJet (N : ℕ) (q : GaugeTwoJet N) (U : FrameJet N) : FrameJet N where
  value := q.value⁻¹ * U.value
  derivative μ := stateResponse N q.value⁻¹ * U.derivative μ -
    stateResponse N q.value⁻¹ * q.first μ * stateResponse N q.value⁻¹ *
      stateResponse N U.value

/-- Every column is an actual state jet; the column vector is not truncated. -/
def column (N : ℕ) (U : FrameJet N) (x : Space N) : MatterJet N where
  value := stateResponse N U.value x
  derivative μ := U.derivative μ x

theorem column_transform (N : ℕ) (q : GaugeTwoJet N) (U : FrameJet N) (x : Space N) :
    column N (transformFrameJet N q U) x =
      transformMatterJet N q.value q.first (column N U x) := by
  cases U
  simp only [column, transformFrameJet, transformMatterJet, map_mul,
    LinearMap.sub_apply, Module.End.mul_apply]

def covariantFrameDerivative (N : ℕ) (A : ConnectionJet N) (U : FrameJet N)
    (μ : CoordinateIndex N) : Operator N :=
  U.derivative μ + A.value μ * stateResponse N U.value

theorem covariantFrameDerivative_apply (N : ℕ) (A : ConnectionJet N) (U : FrameJet N)
    (μ : CoordinateIndex N) (x : Space N) :
    covariantFrameDerivative N A U μ x = covariantComponent N A.value (column N U x) μ :=
  rfl

/-- Covariance is derived before a norm is taken, including both affine terms. -/
theorem covariantFrameDerivative_transform (N : ℕ) (q : GaugeTwoJet N)
    (A : ConnectionJet N) (U : FrameJet N) (μ : CoordinateIndex N) :
    covariantFrameDerivative N (transformConnectionJet N q A) (transformFrameJet N q U) μ =
      stateResponse N q.value⁻¹ * covariantFrameDerivative N A U μ := by
  apply LinearMap.ext
  intro x
  change covariantComponent N (transformConnection N q.value q.first A.value)
      (column N (transformFrameJet N q U) x) μ =
    stateResponse N q.value⁻¹ (covariantComponent N A.value (column N U x) μ)
  rw [column_transform, covariantComponent_transform]

theorem quadratic_left_invariant (N : ℕ) (g : Frame) (X : Operator N) :
    quadratic N (stateResponse N g * X) = quadratic N X := by
  simp only [quadratic, Geometry.HilbertTraceQuadratic.energy_basis
    (stdOrthonormalBasis ℂ (Space N)), Module.End.mul_apply,
    HistoryEffectiveFrames.stateResponse_norm]

def frameResponseDensity (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) : ℝ :=
  ∑ μ, quadratic N (covariantFrameDerivative N A U μ)

theorem frameResponseDensity_nonneg (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) :
    0 ≤ frameResponseDensity N A U :=
  Finset.sum_nonneg fun _ _ => quadratic_nonneg N _

theorem frameResponseDensity_zero_iff (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) :
    frameResponseDensity N A U = 0 ↔ ∀ μ, covariantFrameDerivative N A U μ = 0 := by
  rw [frameResponseDensity,
    Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => quadratic_nonneg N _)]
  simp only [Finset.mem_univ, forall_true_left, quadratic_eq_zero_iff]

theorem frameResponseDensity_gauge (N : ℕ) (q : GaugeTwoJet N)
    (A : ConnectionJet N) (U : FrameJet N) :
    frameResponseDensity N (transformConnectionJet N q A) (transformFrameJet N q U) =
      frameResponseDensity N A U := by
  simp only [frameResponseDensity, covariantFrameDerivative_transform,
    quadratic_left_invariant]

def connectionDensity (N : ℕ) (A : ConnectionJet N) : ℝ :=
  ∑ μ, quadratic N (A.value μ)

theorem frameResponseDensity_sourceFrame (N : ℕ) (A : ConnectionJet N) :
    frameResponseDensity N A (sourceFrame N) = connectionDensity N A := by
  simp [frameResponseDensity, covariantFrameDerivative, sourceFrame, connectionDensity]

/-- The trace is exactly the complete sum of covariant column energies. -/
theorem frameResponseDensity_columns (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) :
    frameResponseDensity N A U =
      2 * ∑ i, HistoryCoupledAction.kinetic N A
        (column N U (stdOrthonormalBasis ℂ (Space N) i)) := by
  simp only [frameResponseDensity, quadratic,
    Geometry.HilbertTraceQuadratic.energy_basis (stdOrthonormalBasis ℂ (Space N)),
    covariantFrameDerivative_apply, HistoryCoupledAction.kinetic,
    Geometry.HilbertPolynomialVariation.energy]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_div]
  ring

theorem state_columns (N : ℕ) (U : FrameJet N) :
    (∑ i, HistoryDefiningDynamics.action N
      (column N U (stdOrthonormalBasis ℂ (Space N) i)).value) =
      HistoryDefiningResponse.coefficient N / 2 * Module.finrank ℂ (Space N) := by
  simp [column, HistoryDefiningDynamics.action, HistoryEffectiveFrames.stateResponse_norm,
    OrthonormalBasis.norm_eq_one, mul_comm]

/-- The curvature is counted once. Each retained state column contributes
its existing kinetic and defining terms. -/
def action (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) : ℝ :=
  HistoryCurvatureVariation.action N A +
    ∑ i, (HistoryCoupledAction.kinetic N A
      (column N U (stdOrthonormalBasis ℂ (Space N) i)) +
      HistoryDefiningDynamics.action N
        (column N U (stdOrthonormalBasis ℂ (Space N) i)).value)

theorem action_eq (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) :
    action N A U = HistoryCurvatureVariation.action N A +
      frameResponseDensity N A U / 2 +
      HistoryDefiningResponse.coefficient N / 2 * Module.finrank ℂ (Space N) := by
  have h := frameResponseDensity_columns N A U
  rw [action, Finset.sum_add_distrib, state_columns]
  linarith

/-- This identity connects the frame functional with the original coupled
functional; it does not define a second unrelated response. -/
theorem action_coupled_columns (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) :
    action N A U + ((Module.finrank ℂ (Space N) : ℝ) - 1) *
        HistoryCurvatureVariation.action N A =
      ∑ i, HistoryCoupledAction.action N A
        (column N U (stdOrthonormalBasis ℂ (Space N) i)) := by
  simp only [HistoryCoupledAction.action, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, action]
  ring

theorem action_nonneg (N : ℕ) (A : ConnectionJet N) (U : FrameJet N) :
    0 ≤ action N A U := by
  rw [action_eq]
  exact add_nonneg
    (add_nonneg (div_nonneg (curvatureDensity_nonneg N A) (by norm_num))
      (div_nonneg (frameResponseDensity_nonneg N A U) (by norm_num)))
    (mul_nonneg (le_of_lt (div_pos (HistoryDefiningResponse.coefficient_pos N)
      (by norm_num))) (Nat.cast_nonneg _))

theorem action_gauge (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N) (U : FrameJet N) :
    action N (transformConnectionJet N q A) (transformFrameJet N q U) = action N A U := by
  simp only [action_eq, HistoryCurvatureVariation.action, curvatureDensity_transform,
    frameResponseDensity_gauge]

theorem action_sourceFrame (N : ℕ) (A : ConnectionJet N) :
    action N A (sourceFrame N) = HistoryCurvatureVariation.action N A +
      connectionDensity N A / 2 +
      HistoryDefiningResponse.coefficient N / 2 * Module.finrank ℂ (Space N) := by
  rw [action_eq, frameResponseDensity_sourceFrame]

theorem action_sourceOrbit (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N) :
    action N (transformConnectionJet N q A) (transformFrameJet N q (sourceFrame N)) =
      HistoryCurvatureVariation.action N A + connectionDensity N A / 2 +
        HistoryDefiningResponse.coefficient N / 2 * Module.finrank ℂ (Space N) := by
  rw [action_gauge, action_sourceFrame]

/-- Uniqueness on the source orbit is a comparison theorem for formulas
with the same invariance and source restriction. -/
theorem sourceOrbit_unique (N : ℕ) (F : ConnectionJet N → FrameJet N → ℝ)
    (hinvariant : ∀ q A U,
      F (transformConnectionJet N q A) (transformFrameJet N q U) = F A U)
    (hsource : ∀ A, F A (sourceFrame N) = action N A (sourceFrame N))
    (q : GaugeTwoJet N) (A : ConnectionJet N) :
    F (transformConnectionJet N q A) (transformFrameJet N q (sourceFrame N)) =
      action N (transformConnectionJet N q A) (transformFrameJet N q (sourceFrame N)) := by
  rw [hinvariant, hsource, action_gauge]

structure Conclusions : Prop where
  derivative_covariance : ∀ N q A U μ,
    covariantFrameDerivative N (transformConnectionJet N q A) (transformFrameJet N q U) μ =
      stateResponse N q.value⁻¹ * covariantFrameDerivative N A U μ
  complete_columns : ∀ N A U,
    frameResponseDensity N A U = 2 * ∑ i, HistoryCoupledAction.kinetic N A
      (column N U (stdOrthonormalBasis ℂ (Space N) i))
  actual_action : ∀ N A U,
    action N A U = HistoryCurvatureVariation.action N A + frameResponseDensity N A U / 2 +
      HistoryDefiningResponse.coefficient N / 2 * Module.finrank ℂ (Space N)
  positive_action : ∀ N A U, 0 ≤ action N A U
  frame_covariance : ∀ N q A U,
    action N (transformConnectionJet N q A) (transformFrameJet N q U) = action N A U
  source_restriction : ∀ N A,
    action N A (sourceFrame N) = HistoryCurvatureVariation.action N A +
      connectionDensity N A / 2 +
      HistoryDefiningResponse.coefficient N / 2 * Module.finrank ℂ (Space N)

theorem generated : Conclusions where
  derivative_covariance := covariantFrameDerivative_transform
  complete_columns := frameResponseDensity_columns
  actual_action := action_eq
  positive_action := action_nonneg
  frame_covariance := action_gauge
  source_restriction := action_sourceFrame

end GeneratedFoundations.Arithmetic.HistoryMovingFrameResponse
