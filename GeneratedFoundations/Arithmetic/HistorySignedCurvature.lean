module

public import GeneratedFoundations.Arithmetic.HistoryGaugeJets
public import GeneratedFoundations.Arithmetic.HistoryCentralPhase

/-!
# Curvature contracted with actual arithmetic central signs

The coordinate signature is the prime-occupation character of the retained
history root. It is computed on the existing coordinate set, not copied
from a four-dimensional Lorentz signature. Its signed contraction is gauge
invariant; unlike the positive trace density it need not be nonnegative.
The more general contraction below also records exactly which covariance
identity remains valid for arbitrary coordinate weights.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistorySignedCurvature

open HistoryGaugeJets

def coordinateSign {N : ℕ} (μ : CoordinateIndex N) : ℝ := HistoryCentralPhase.weight μ

theorem coordinateSign_sq {N : ℕ} (μ : CoordinateIndex N) : coordinateSign μ ^ 2 = 1 := by
  rcases HistoryCentralPhase.weight_cases μ with h | h <;> simp [coordinateSign, h]

def contraction (N : ℕ) (g : CoordinateIndex N → ℝ)
    (F : CoordinateIndex N → CoordinateIndex N → Operator N) : ℝ :=
  ∑ μ, ∑ ν, g μ * g ν * quadratic N (F μ ν)

def transformCurvature (N : ℕ) (q : HistoryElementaryConnector.Frame)
    (F : CoordinateIndex N → CoordinateIndex N → Operator N) :=
  fun μ ν => conjugate N q (F μ ν)

theorem contraction_invariant (N : ℕ) (g : CoordinateIndex N → ℝ)
    (q : HistoryElementaryConnector.Frame)
    (F : CoordinateIndex N → CoordinateIndex N → Operator N) :
    contraction N g (transformCurvature N q F) = contraction N g F := by
  simp [contraction, transformCurvature, quadratic_conjugate]

def density (N : ℕ) (A : ConnectionJet N) : ℝ :=
  contraction N coordinateSign (curvature A)

theorem density_local_covariance (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N) :
    density N (transformConnectionJet N q A) = density N A := by
  simp [density, contraction, curvature_transform, quadratic_conjugate]

theorem unit_contraction (N : ℕ) (A : ConnectionJet N) :
    contraction N (fun _ => 1) (curvature A) = curvatureDensity N A := by
  simp [contraction, curvatureDensity]

structure Conclusions : Prop where
  generated_signs : ∀ N (μ : CoordinateIndex N), coordinateSign μ ^ 2 = 1
  full_contraction_covariance : ∀ N g q F,
    contraction N g (transformCurvature N q F) = contraction N g F
  local_covariance : ∀ N q A, density N (transformConnectionJet N q A) = density N A

theorem generated : Conclusions where
  generated_signs := fun _ μ => coordinateSign_sq μ
  full_contraction_covariance := contraction_invariant
  local_covariance := density_local_covariance

end GeneratedFoundations.Arithmetic.HistorySignedCurvature
