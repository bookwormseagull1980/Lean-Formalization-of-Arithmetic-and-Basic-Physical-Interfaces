module

public import GeneratedFoundations.Arithmetic.HistoryAdjointComparison

/-!
# Finite arithmetic intensity contractions and relaxed curvature response

The contraction recurrence uses the computed arithmetic coefficient count,
not the physical colour multiplicity. These are exact finite contraction
identities; they do not identify the radial score with a Gaussian coordinate
or replace the native weighted arithmetic source by a new probability law.
The partial Legendre Schur identity retains its negative source curvature.
For the generated comparison equilibrium, the restoring coefficient is
proved positive by the actual comparison response.
-/

@[expose] public section
noncomputable section
open scoped BigOperators
namespace GeneratedFoundations.Arithmetic.HistoryIntensitySusceptibility

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

theorem actual_normalized_fourth (N : ℕ) :
    ((HistoryGaussianCovariance.componentCount N : ℝ) / 2) ^ 2 *
      (intensityMoment (HistoryGaussianCovariance.componentCount N) 4 -
        4 * intensityMoment (HistoryGaussianCovariance.componentCount N) 3 +
        6 * intensityMoment (HistoryGaussianCovariance.componentCount N) 2 - 3) =
      3 + 12 / HistoryGaussianCovariance.componentCount N := by
  apply normalized_fourth
  exact_mod_cast (HistoryGaussianCovariance.componentCount_pos N).ne'

/-- O'(q), in the original intensity coordinate. -/
def meanDerivative (lam alpha q : ℝ) : ℝ := lam + 2 * alpha * q

/-- The finite coefficient count is that of the actual arithmetic carrier. -/
def sourceVariance (N : ℕ) (q : ℝ) : ℝ :=
  2 * q ^ 2 / HistoryGaussianCovariance.componentCount N

def radialMassSquared (N : ℕ) (q restoring : ℝ) : ℝ := sourceVariance N q * restoring

def radialOverlapSquared (N : ℕ) (q omega : ℝ) : ℝ := sourceVariance N q * omega ^ 2

def staticSusceptibility (residual omega restoring : ℝ) : ℝ :=
  residual + omega ^ 2 / restoring

theorem sourceVariance_pos (N : ℕ) {q : ℝ} (hq : q ≠ 0) : 0 < sourceVariance N q := by
  unfold sourceVariance
  exact div_pos (mul_pos (by norm_num) (sq_pos_of_ne_zero hq))
    (Nat.cast_pos.mpr (HistoryGaussianCovariance.componentCount_pos N))

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
theorem susceptibility_mass_identity (N : ℕ) {q restoring : ℝ}
    (hq : q ≠ 0) (hF : restoring ≠ 0) (omega residual : ℝ) :
    staticSusceptibility residual omega restoring = residual +
      radialOverlapSquared N q omega / radialMassSquared N q restoring := by
  have hv := ne_of_gt (sourceVariance_pos N hq)
  unfold staticSusceptibility radialOverlapSquared radialMassSquared
  field_simp [hv, hF]

theorem staticSusceptibility_pos {residual restoring omega : ℝ}
    (hres : 0 < residual) (hF : 0 < restoring) :
    0 < staticSusceptibility residual omega restoring := by
  exact add_pos_of_pos_of_nonneg hres (div_nonneg (sq_nonneg omega) hF.le)


def generatedRestoring (N : ℕ) : ℝ :=
  HistoryAdjointComparison.curvature N (HistoryAdjointComparison.amplitude N)

theorem generatedRestoring_pos (N : ℕ) : 0 < generatedRestoring N :=
  HistoryAdjointComparison.curvature_pos N
    (HistoryAdjointComparison.amplitude_spec N).1.le

def generatedSusceptibility (N : ℕ) (residual omega : ℝ) : ℝ :=
  staticSusceptibility residual omega (generatedRestoring N)

theorem generatedSusceptibility_nonneg (N : ℕ) {residual : ℝ}
    (hres : 0 ≤ residual) (omega : ℝ) :
    0 ≤ generatedSusceptibility N residual omega :=
  add_nonneg hres (div_nonneg (sq_nonneg _) (generatedRestoring_pos N).le)

theorem generated_joint_hessian (N : ℕ) (omega residual dn J : ℝ) :
    generatedRestoring N * dn ^ 2 + 2 * omega * dn * J - residual * J ^ 2 =
      generatedRestoring N * (dn + omega / generatedRestoring N * J) ^ 2 -
        generatedSusceptibility N residual omega * J ^ 2 :=
  joint_hessian_square (generatedRestoring_pos N).ne' omega residual dn J

structure Conclusions : Prop where
  actual_variance : ∀ N q, sourceVariance N q =
    2 * q ^ 2 / HistoryGaussianCovariance.componentCount N
  positive_restoring : ∀ N, 0 < generatedRestoring N
  full_schur : ∀ N omega residual dn J,
    generatedRestoring N * dn ^ 2 + 2 * omega * dn * J - residual * J ^ 2 =
      generatedRestoring N * (dn + omega / generatedRestoring N * J) ^ 2 -
        generatedSusceptibility N residual omega * J ^ 2

theorem generated : Conclusions where
  actual_variance := fun _ _ => rfl
  positive_restoring := generatedRestoring_pos
  full_schur := generated_joint_hessian

end GeneratedFoundations.Arithmetic.HistoryIntensitySusceptibility
