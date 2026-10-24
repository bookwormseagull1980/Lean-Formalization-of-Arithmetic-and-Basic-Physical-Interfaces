module

public import GeneratedFoundations.Physical.SourceRadialMassIntertwiner
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite source moments and joint curvature response

The radial moment recurrence is the finite Gaussian contraction recurrence
for N/q. The joint-Hessian identities concern the partial Legendre response
with source exp(h*N-J*Q). They distinguish the collective stationary response
from the fixed-source coefficient semigroup. Analytic integration and the
infinite-dimensional source representation are separate results.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceCurvatureSusceptibility

/-- Radial moments of the normalized intensity from Gaussian contractions. -/
def intensityMoment (M : ℝ) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k, (1 + 2 * (j : ℝ) / M)

theorem intensityMoment_two (M : ℝ) :
    intensityMoment M 2 = 1 + 2 / M := by
  norm_num [intensityMoment, Finset.prod_range_succ]

theorem intensityMoment_three (M : ℝ) :
    intensityMoment M 3 = (1 + 2 / M) * (1 + 4 / M) := by
  norm_num [intensityMoment, Finset.prod_range_succ]

theorem intensityMoment_four (M : ℝ) :
    intensityMoment M 4 = (1 + 2 / M) * (1 + 4 / M) * (1 + 6 / M) := by
  norm_num [intensityMoment, Finset.prod_range_succ]

/-- The centered cubic moment survives in every finite positive dimension. -/
theorem centered_third {M : ℝ} (hM : M ≠ 0) :
    intensityMoment M 3 - 3 * intensityMoment M 2 + 2 = 8 / M ^ 2 := by
  rw [intensityMoment_three, intensityMoment_two]
  field_simp [hM]
  ring

/-- After variance normalization the fourth moment retains the finite-source
correction 12/M; the radial score is not a new Gaussian coordinate. -/
theorem normalized_fourth {M : ℝ} (hM : M ≠ 0) :
    (M / 2) ^ 2 * (intensityMoment M 4 - 4 * intensityMoment M 3 +
      6 * intensityMoment M 2 - 3) = 3 + 12 / M := by
  rw [intensityMoment_four, intensityMoment_three, intensityMoment_two]
  field_simp [hM]
  ring

theorem generated_normalized_fourth :
    (120 / 2 : ℝ) ^ 2 * (intensityMoment 120 4 - 4 * intensityMoment 120 3 +
      6 * intensityMoment 120 2 - 3) = 31 / 10 := by
  rw [normalized_fourth (by norm_num)]
  norm_num

/-- O'(q), in the original intensity coordinate. -/
def meanDerivative (lam alpha q : ℝ) : ℝ := lam + 2 * alpha * q

/-- Source variance is inherited from the already generated 120 coefficients. -/
def sourceVariance (q : ℝ) : ℝ := SourceRadialMassIntertwiner.scoreVariance q

def radialMassSquared (q restoring : ℝ) : ℝ := sourceVariance q * restoring

def radialOverlapSquared (q omega : ℝ) : ℝ := sourceVariance q * omega ^ 2

def staticSusceptibility (residual omega restoring : ℝ) : ℝ :=
  residual + omega ^ 2 / restoring

theorem sourceVariance_pos {q : ℝ} (hq : q ≠ 0) : 0 < sourceVariance q := by
  unfold sourceVariance SourceRadialMassIntertwiner.scoreVariance
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hq))
    SourceRadialMassIntertwiner.coefficientCount_pos

/-- Exact Schur complement of the joint Hessian. Its negative J curvature
gives the positive static susceptibility after the intensity is relaxed. -/
theorem joint_hessian_square {restoring : ℝ} (hF : restoring ≠ 0)
    (omega residual dn J : ℝ) :
    restoring * dn ^ 2 + 2 * omega * dn * J - residual * J ^ 2 =
      restoring * (dn + omega / restoring * J) ^ 2 -
        staticSusceptibility residual omega restoring * J ^ 2 := by
  unfold staticSusceptibility
  field_simp [hF]
  ring

theorem stationary_tangent {restoring : ℝ} (hF : restoring ≠ 0) (omega : ℝ) :
    restoring * (-omega / restoring) + omega = 0 := by
  field_simp [hF]
  ring

/-- The collective term expressed in the normalized radial mass coordinate. -/
theorem susceptibility_mass_identity {q restoring : ℝ}
    (hq : q ≠ 0) (hF : restoring ≠ 0) (omega residual : ℝ) :
    staticSusceptibility residual omega restoring = residual +
      radialOverlapSquared q omega / radialMassSquared q restoring := by
  have hv := ne_of_gt (sourceVariance_pos hq)
  unfold staticSusceptibility radialOverlapSquared radialMassSquared
  field_simp [hv, hF]

theorem staticSusceptibility_pos {residual restoring omega : ℝ}
    (hres : 0 < residual) (hF : 0 < restoring) :
    0 < staticSusceptibility residual omega restoring := by
  exact add_pos_of_pos_of_nonneg hres (div_nonneg (sq_nonneg omega) hF.le)

end GeneratedFoundations.Physical.SourceCurvatureSusceptibility
