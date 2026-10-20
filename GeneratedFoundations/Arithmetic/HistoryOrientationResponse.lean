module

public import GeneratedFoundations.Arithmetic.HistoryMovingFrameResponse
public import GeneratedFoundations.Arithmetic.HistoryAdjointCasimir

/-!
# Orientation reversal of the complete arithmetic connection response

Complex conjugation is transported through the faithful action of the full
history-operation matrix algebra. Both the value and the derivative of a
connection are transformed. Its nonlinear curvature, positive trace norm
and canonical source-frame action are then compared on the actual carrier.
No restriction to a colour corner or to diagonal observations is made.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryOrientationResponse

open HistoryCliffordAction (Algebra Space action)
open HistoryGaugeJets

def conjugateOperator (N : ℕ) : Operator N →+* Operator N :=
  (action N).toRingEquiv.toRingHom.comp
    ((starRingEnd ℂ).mapMatrix.comp (action N).symm.toRingEquiv.toRingHom)

theorem conjugateOperator_apply (N : ℕ) (X : Operator N) :
    conjugateOperator N X = action N (((action N).symm X).map (starRingEnd ℂ)) := rfl

theorem conjugateOperator_involutive (N : ℕ) :
    Function.Involutive (conjugateOperator N) := by
  intro X
  rw [conjugateOperator_apply, conjugateOperator_apply,
    AlgEquiv.symm_apply_apply]
  have hm : (((action N).symm X).map (starRingEnd ℂ)).map (starRingEnd ℂ) =
      (action N).symm X := by
    ext i j
    simp
  rw [hm, AlgEquiv.apply_symm_apply]

theorem conjugateOperator_adjoint (N : ℕ) (X : Operator N) :
    (conjugateOperator N X).adjoint = conjugateOperator N X.adjoint := by
  rw [conjugateOperator_apply, HistoryCliffordAction.action_adjoint,
    conjugateOperator_apply]
  have ha : (action N).symm X.adjoint = ((action N).symm X).conjTranspose := by
    apply (action N).injective
    rw [AlgEquiv.apply_symm_apply, ← HistoryCliffordAction.action_adjoint,
      AlgEquiv.apply_symm_apply]
  rw [ha]
  congr 1

theorem trace_conjugate (N : ℕ) (X : Operator N) :
    LinearMap.trace ℂ (Space N) (conjugateOperator N X) =
      star (LinearMap.trace ℂ (Space N) X) := by
  rw [conjugateOperator_apply, HistoryAdjointCasimir.trace_action]
  have hx : LinearMap.trace ℂ (Space N) X = Matrix.trace ((action N).symm X) := by
    simpa only [AlgEquiv.apply_symm_apply] using
      HistoryAdjointCasimir.trace_action N ((action N).symm X)
  rw [hx]
  simp [Matrix.trace]

theorem quadratic_conjugate (N : ℕ) (X : Operator N) :
    quadratic N (conjugateOperator N X) = quadratic N X := by
  unfold quadratic Geometry.HilbertTraceQuadratic.energy
  rw [conjugateOperator_adjoint, ← map_mul, trace_conjugate]
  simp

def conjugateConnection (N : ℕ) (A : ConnectionJet N) : ConnectionJet N where
  value μ := conjugateOperator N (A.value μ)
  derivative μ ν := conjugateOperator N (A.derivative μ ν)

theorem conjugateConnection_involutive (N : ℕ) :
    Function.Involutive (conjugateConnection N) := by
  intro A
  cases A
  simp only [conjugateConnection]
  congr 1
  · funext μ
    exact conjugateOperator_involutive N _
  · funext μ ν
    exact conjugateOperator_involutive N _

theorem curvature_conjugate (N : ℕ) (A : ConnectionJet N) (μ ν : CoordinateIndex N) :
    curvature (conjugateConnection N A) μ ν = conjugateOperator N (curvature A μ ν) := by
  simp only [curvature, Geometry.ConnectionJetAlgebra.curvature,
    conjugateConnection, map_add, map_sub, map_mul]

theorem curvatureDensity_conjugate (N : ℕ) (A : ConnectionJet N) :
    curvatureDensity N (conjugateConnection N A) = curvatureDensity N A := by
  simp only [curvatureDensity, curvature_conjugate, quadratic_conjugate]

theorem connectionDensity_conjugate (N : ℕ) (A : ConnectionJet N) :
    HistoryMovingFrameResponse.connectionDensity N (conjugateConnection N A) =
      HistoryMovingFrameResponse.connectionDensity N A := by
  simp only [HistoryMovingFrameResponse.connectionDensity,
    conjugateConnection, quadratic_conjugate]

/-- The actual nonlinear curvature and the complete connection-value trace
are both retained. The defining-state contribution is already invariant. -/
theorem sourceAction_conjugate (N : ℕ) (A : ConnectionJet N) :
    HistoryMovingFrameResponse.action N (conjugateConnection N A)
        (HistoryMovingFrameResponse.sourceFrame N) =
      HistoryMovingFrameResponse.action N A (HistoryMovingFrameResponse.sourceFrame N) := by
  simp only [HistoryMovingFrameResponse.action_sourceFrame,
    HistoryCurvatureVariation.action, curvatureDensity_conjugate,
    connectionDensity_conjugate]

structure Conclusions : Prop where
  reversal_involution : ∀ N, Function.Involutive (conjugateConnection N)
  actual_curvature : ∀ N A μ ν,
    curvature (conjugateConnection N A) μ ν = conjugateOperator N (curvature A μ ν)
  full_curvature_density : ∀ N A,
    curvatureDensity N (conjugateConnection N A) = curvatureDensity N A
  full_connection_density : ∀ N A,
    HistoryMovingFrameResponse.connectionDensity N (conjugateConnection N A) =
      HistoryMovingFrameResponse.connectionDensity N A
  canonical_action : ∀ N A,
    HistoryMovingFrameResponse.action N (conjugateConnection N A)
        (HistoryMovingFrameResponse.sourceFrame N) =
      HistoryMovingFrameResponse.action N A (HistoryMovingFrameResponse.sourceFrame N)

theorem generated : Conclusions where
  reversal_involution := conjugateConnection_involutive
  actual_curvature := curvature_conjugate
  full_curvature_density := curvatureDensity_conjugate
  full_connection_density := connectionDensity_conjugate
  canonical_action := sourceAction_conjugate

end GeneratedFoundations.Arithmetic.HistoryOrientationResponse
