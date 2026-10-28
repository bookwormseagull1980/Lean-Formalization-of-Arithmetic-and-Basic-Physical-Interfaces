module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianState
public import GeneratedFoundations.Operations.FinitePrecisionTilt

/-!
# The common heat-vertex variation of the history Gaussian field

The quadratic source is the original kinetic action after its Gaussian
field filter. Coupling this one observable changes each actual precision
by its own filtered kinetic vertex. This fixes the complete finite partition
function, rather than choosing a scalar comparison from its curvature at zero.
Both real quadratures of every original complex mode are retained.

The earlier externally weighted precision comparison remains a valid
labelwise comparison. Its finite-coupling curvature is distinguished here
from the curvature of the common joint-field variation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianVariation

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionJointHessian (Index)
open HistoryHaarSectionGaussianState (Space RealIndex realPrecision heatVertex heatScore)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def vertexRatio (N : ℕ) (i : Index N) (u : ℝ) : ℝ :=
  heatVertex N i u / precision N i u

theorem kineticPrecision_nonneg (N : ℕ) (i : Index N) (u : ℝ) :
    0 ≤ kineticPrecision N i u := add_nonneg (sq_nonneg u) (kinetic_nonneg N i)

theorem heatVertex_nonneg (N : ℕ) (i : Index N) (u : ℝ) :
    0 ≤ heatVertex N i u :=
  mul_nonneg (Real.exp_pos _).le (kineticPrecision_nonneg N i u)

theorem vertexRatio_nonneg (N : ℕ) (i : Index N) (u : ℝ) : 0 ≤ vertexRatio N i u :=
  div_nonneg (heatVertex_nonneg N i u) (precision_pos N i u).le

theorem vertexRatio_eq (N : ℕ) (i : Index N) (u : ℝ) :
    vertexRatio N i u = Real.exp (-kineticPrecision N i u / 2) * kineticFraction N i u := by
  unfold vertexRatio heatVertex kineticFraction
  ring

theorem vertexRatio_le (N : ℕ) (i : Index N) (u : ℝ) :
    vertexRatio N i u ≤ kineticFraction N i u := by
  rw [vertexRatio_eq]
  exact mul_le_of_le_one_left (kineticFraction_nonneg N i u)
    (Real.exp_le_one_iff.mpr (by linarith [kineticPrecision_nonneg N i u]))

def realVertex (N : ℕ) (B u : ℝ) (i : RealIndex N B u) : ℝ := heatVertex N i.val.1 u

def variedPrecision (N : ℕ) (B u z : ℝ) (i : RealIndex N B u) : ℝ :=
  realPrecision N B u i + z * realVertex N B u i

theorem variedPrecision_pos (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z)
    (i : RealIndex N B u) : 0 < variedPrecision N B u z i :=
  add_pos_of_pos_of_nonneg (HistoryHaarSectionGaussianState.realPrecision_pos N B u i)
    (mul_nonneg hz (heatVertex_nonneg N i.val.1 u))

def variedLaw (N : ℕ) (B u z : ℝ) : Measure (Space N B u) :=
  Operations.FinitePrecisionGaussian.law (variedPrecision N B u z)

def variedAction (N : ℕ) (B u z : ℝ) (x : Space N B u) : ℝ :=
  Operations.FinitePrecisionGaussian.score (variedPrecision N B u z) x

/-- The precision family is exactly the original action plus the one common
observable, not an independently selected family with the same Hessian. -/
theorem variedAction_eq (N : ℕ) (B u z : ℝ) (x : Space N B u) :
    variedAction N B u z x = HistoryHaarSectionGaussianState.quadraticAction N B u x +
      z * heatScore N B u x := by
  unfold variedAction HistoryHaarSectionGaussianState.quadraticAction heatScore
    Operations.FinitePrecisionGaussian.score
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold Operations.GaussianPrecisionMoments.score variedPrecision realVertex
  ring

theorem variedLaw_existsUnique (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      Operations.FinitePrecisionGaussian.precisionMatrix (variedPrecision N B u z) *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1 :=
  Operations.FinitePrecisionGaussian.law_existsUnique (variedPrecision_pos N B u hz)

def partition (N : ℕ) (B u z : ℝ) : ℝ :=
  ∫ x, Real.exp (-z * heatScore N B u x) ∂HistoryHaarSectionGaussianState.law N B u

def logPartition (N : ℕ) (B u z : ℝ) : ℝ :=
  -∑ i ∈ HistoryHaarSectionCovariance.frequencySupport N B u,
    Real.log (1 + z * vertexRatio N i u)

def comparison (N : ℕ) (B u z : ℝ) : ℝ :=
  ∑ i ∈ HistoryHaarSectionCovariance.frequencySupport N B u, cost (vertexRatio N i u) z

def force (N : ℕ) (B u z : ℝ) : ℝ :=
  ∑ i ∈ HistoryHaarSectionCovariance.frequencySupport N B u,
    Operations.ScalarPrecisionComparison.force (vertexRatio N i u) z

def curvature (N : ℕ) (B u z : ℝ) : ℝ :=
  ∑ i ∈ HistoryHaarSectionCovariance.frequencySupport N B u,
    Operations.ScalarPrecisionComparison.curvature (vertexRatio N i u) z

theorem partition_eq (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    partition N B u z = Real.exp (logPartition N B u z) := by
  have h := Operations.FinitePrecisionTilt.partition_eq_exp
    (HistoryHaarSectionGaussianState.realPrecision_pos N B u) (variedPrecision_pos N B u hz)
  change partition N B u z = Real.exp _ at h
  rw [h]
  congr 1
  rw [Operations.FinitePrecisionTilt.logPartition, HistoryHaarSectionGaussianState.sum_realIndex]
  unfold logPartition
  rw [← Finset.sum_attach (HistoryHaarSectionCovariance.frequencySupport N B u)
    (fun i => Real.log (1 + z * vertexRatio N i u))]
  have hs : (∑ i : HistoryHaarSectionCovariance.WindowIndex N B u,
      ∑ q : Fin 2, Real.log (1 + z *
        (realVertex N B u (HistoryHaarSectionGaussianState.slot N B u i q) /
          realPrecision N B u (HistoryHaarSectionGaussianState.slot N B u i q)))) =
        2 * ∑ i : HistoryHaarSectionCovariance.WindowIndex N B u,
          Real.log (1 + z * vertexRatio N i.val u) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_two]
    simp only [realVertex, realPrecision, HistoryHaarSectionGaussianState.slot, vertexRatio]
    ring
  rw [hs]
  rw [Finset.univ_eq_attach]
  ring

theorem log_partition (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    Real.log (partition N B u z) = logPartition N B u z := by
  rw [partition_eq N B u hz, Real.log_exp]

/-- The finite comparison follows from the actual complete partition. -/
theorem comparison_eq_partition (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    comparison N B u z = z * (∫ x, heatScore N B u x
      ∂HistoryHaarSectionGaussianState.law N B u) + Real.log (partition N B u z) := by
  rw [HistoryHaarSectionGaussianState.heatScore_mean, log_partition N B u hz]
  unfold comparison cost vertexRatio logPartition
  simp only [vertexRatio]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  ring

theorem relative_pos (N : ℕ) (i : Index N) (u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    0 < 1 + z * vertexRatio N i u :=
  add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hz (vertexRatio_nonneg N i u))

theorem comparison_hasDerivAt (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (comparison N B u) (force N B u z) z := by
  unfold comparison force
  exact HasDerivAt.fun_sum (fun i _ => cost_hasDerivAt _ _ (relative_pos N i u hz).ne')

theorem force_hasDerivAt (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (force N B u) (curvature N B u z) z := by
  unfold force curvature
  exact HasDerivAt.fun_sum (fun i _ =>
    Operations.ScalarPrecisionComparison.force_hasDerivAt _ _ (relative_pos N i u hz).ne')

theorem mode_curvature_eq (N : ℕ) (i : Index N) (u z : ℝ) :
    Operations.ScalarPrecisionComparison.curvature (vertexRatio N i u) z =
      kernel N i u / (1 + z * vertexRatio N i u) ^ 2 := by
  have hw : Real.exp (-kineticPrecision N i u / 2) ^ 2 = weight N i u := by
    rw [pow_two, ← Real.exp_add]
    change Real.exp _ = Real.exp _
    congr 1
    ring
  rw [Operations.ScalarPrecisionComparison.curvature, vertexRatio_eq, mul_pow, hw]
  simp only [kernel, weight, kineticFraction, kineticPrecision, precision, div_pow]
  ring

theorem curvature_zero (N : ℕ) (B u : ℝ) :
    curvature N B u 0 = ∑ i ∈ HistoryHaarSectionCovariance.frequencySupport N B u,
      kernel N i u := by
  unfold curvature
  apply Finset.sum_congr rfl
  intro i _
  simp only [mode_curvature_eq, zero_mul, add_zero, one_pow, div_one]

/-- The curvature at every positive coupling is the variance of the same
complete observable in the unique varied Gaussian state. -/
theorem varied_score_variance (N : ℕ) (B u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    Var[heatScore N B u; variedLaw N B u z] = curvature N B u z := by
  have h := Operations.FinitePrecisionGaussian.score_variance
    (variedPrecision_pos N B u hz) (realVertex N B u)
  change Var[heatScore N B u; variedLaw N B u z] = _ at h
  rw [h, HistoryHaarSectionGaussianState.sum_realIndex]
  unfold curvature
  rw [← Finset.sum_attach (HistoryHaarSectionCovariance.frequencySupport N B u)
    (fun i => Operations.ScalarPrecisionComparison.curvature (vertexRatio N i u) z)]
  rw [Finset.univ_eq_attach]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp only [realVertex, realPrecision, HistoryHaarSectionGaussianState.slot,
    variedPrecision, Operations.ScalarPrecisionComparison.curvature, vertexRatio]
  have hp := (precision_pos N i.val u).ne'
  have hz' : precision N i.val u + z * heatVertex N i.val u ≠ 0 :=
    (add_pos_of_pos_of_nonneg (precision_pos N i.val u)
      (mul_nonneg hz (heatVertex_nonneg N i.val u))).ne'
  field_simp [hp, hz']
  ring

/-- At positive coupling the complete-state response differs from the
externally weighted label comparison, despite agreement at zero. -/
theorem old_curvature_le (N : ℕ) (i : Index N) (u : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    weight N i u * Operations.ScalarPrecisionComparison.curvature (kineticFraction N i u) z ≤
      Operations.ScalarPrecisionComparison.curvature (vertexRatio N i u) z := by
  rw [mode_curvature_eq]
  have hk : 0 ≤ kernel N i u := by
    unfold kernel
    positivity
  have hd := relative_pos N i u hz
  have hle : 1 + z * vertexRatio N i u ≤ 1 + z * kineticFraction N i u :=
    add_le_add_right (mul_le_mul_of_nonneg_left (vertexRatio_le N i u) hz) 1
  have heq : weight N i u *
      Operations.ScalarPrecisionComparison.curvature (kineticFraction N i u) z =
      kernel N i u / (1 + z * kineticFraction N i u) ^ 2 := by
    unfold Operations.ScalarPrecisionComparison.curvature kernel weight kineticFraction
      kineticPrecision precision
    ring
  rw [heq]
  exact div_le_div_of_nonneg_left hk (sq_pos_of_pos hd)
    (pow_le_pow_left₀ hd.le hle 2)

theorem old_curvature_lt (N : ℕ) (i : Index N) (u : ℝ) {z : ℝ}
    (hz : 0 < z) (hk : 0 < kineticPrecision N i u) :
    weight N i u * Operations.ScalarPrecisionComparison.curvature (kineticFraction N i u) z <
      Operations.ScalarPrecisionComparison.curvature (vertexRatio N i u) z := by
  have hr : 0 < kineticFraction N i u := div_pos hk (precision_pos N i u)
  have ht : vertexRatio N i u < kineticFraction N i u := by
    rw [vertexRatio_eq]
    exact mul_lt_of_lt_one_left hr (Real.exp_lt_one_iff.mpr (by linarith))
  have hn : 0 < kernel N i u := by
    rw [show kernel N i u = (vertexRatio N i u) ^ 2 by
      simpa only [Operations.ScalarPrecisionComparison.curvature_zero, zero_mul,
        add_zero, one_pow, div_one] using (mode_curvature_eq N i u 0).symm]
    exact sq_pos_of_pos (by
      rw [vertexRatio_eq]
      exact mul_pos (Real.exp_pos _) hr)
  have hd := relative_pos N i u hz.le
  have hden : (1 + z * vertexRatio N i u) ^ 2 <
      (1 + z * kineticFraction N i u) ^ 2 := by
    nlinarith [mul_lt_mul_of_pos_left ht hz]
  have heq : weight N i u *
      Operations.ScalarPrecisionComparison.curvature (kineticFraction N i u) z =
      kernel N i u / (1 + z * kineticFraction N i u) ^ 2 := by
    unfold Operations.ScalarPrecisionComparison.curvature kernel weight kineticFraction
      kineticPrecision precision
    ring
  rw [heq, mode_curvature_eq]
  exact div_lt_div_of_pos_left hn (sq_pos_of_pos hd) hden

structure Conclusions : Prop where
  original_common_action : ∀ N B u z (x : Space N B u),
    variedAction N B u z x = HistoryHaarSectionGaussianState.quadraticAction N B u x +
      z * heatScore N B u x
  unique_varied_gaussian : ∀ N B u z, 0 ≤ z →
    ∃! ν : Measure (Space N B u), IsGaussian ν ∧ (∫ x, x ∂ν) = 0 ∧
      Operations.FinitePrecisionGaussian.precisionMatrix (variedPrecision N B u z) *
        Operations.FinitePrecisionGaussian.coordinateCovariance ν = 1
  complete_partition : ∀ N B u z, 0 ≤ z →
    partition N B u z = Real.exp (logPartition N B u z)
  partition_origin : ∀ N B u z, 0 ≤ z →
    comparison N B u z = z * (∫ x, heatScore N B u x
      ∂HistoryHaarSectionGaussianState.law N B u) + Real.log (partition N B u z)
  complete_curvature : ∀ N B u, curvature N B u 0 =
    ∑ i ∈ HistoryHaarSectionCovariance.frequencySupport N B u, kernel N i u
  same_state_fluctuation : ∀ N B u z, 0 ≤ z →
    Var[heatScore N B u; variedLaw N B u z] = curvature N B u z
  finite_coupling_comparison : ∀ N i u z, 0 ≤ z →
    weight N i u * Operations.ScalarPrecisionComparison.curvature (kineticFraction N i u) z ≤
      Operations.ScalarPrecisionComparison.curvature (vertexRatio N i u) z

theorem generated : Conclusions where
  original_common_action := variedAction_eq
  unique_varied_gaussian := fun N B u _ hz => variedLaw_existsUnique N B u hz
  complete_partition := fun N B u _ hz => partition_eq N B u hz
  partition_origin := fun N B u _ hz => comparison_eq_partition N B u hz
  complete_curvature := curvature_zero
  same_state_fluctuation := fun N B u _ hz => varied_score_variance N B u hz
  finite_coupling_comparison := fun N i u _ hz => old_curvature_le N i u hz

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianVariation
