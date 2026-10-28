module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionCapacityThreshold
public import GeneratedFoundations.Operations.GaussianPrecisionMoments

/-!
# Gaussian fluctuations and restoration at the actual section equilibrium

Every original spectral row and its frequency interval are retained. The
precision Gaussian at amplitude `z` has precision `p + z*q`, where `p` is
the original joint-Hessian precision and `q` its own kinetic coefficient.
The response is twice the loss of the quadratic-score mean; its derivative
is twice that score's variance. Averaging here is over the unchanged
Gaussian window, so the resulting quantity is a weighted conditional
variance, not the variance of an uncentered mixture of different rows.

These identities apply to the existing Gaussian precision comparison. They
do not replace the original nonlinear action by a Gaussian path integral.
The window, variation amplitude and coordinate scale remain distinct.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionRestoration

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionSourceBalance HistoryHaarSectionEquilibrium
open HistoryHaarSectionJointHessian (Index)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def scoreMean (N : ℕ) (i : Index N) (u z : ℝ) : ℝ :=
  ∫ x : ℝ, Operations.GaussianPrecisionMoments.score (kineticPrecision N i u) x
    ∂Operations.GaussianPrecisionKL.law (precision N i u + z * kineticPrecision N i u)

def scoreVariance (N : ℕ) (i : Index N) (u z : ℝ) : ℝ :=
  ProbabilityTheory.variance
    (Operations.GaussianPrecisionMoments.score (kineticPrecision N i u))
    (Operations.GaussianPrecisionKL.law (precision N i u + z * kineticPrecision N i u))

theorem scoreMean_eq (N : ℕ) (i : Index N) (u : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    scoreMean N i u z = kineticPrecision N i u /
      (2 * (precision N i u + z * kineticPrecision N i u)) :=
  Operations.GaussianPrecisionMoments.score_mean (perturbedPrecision_pos N i u hz) _

theorem scoreVariance_eq (N : ℕ) (i : Index N) (u : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    scoreVariance N i u z = kineticPrecision N i u ^ 2 /
      (2 * (precision N i u + z * kineticPrecision N i u) ^ 2) :=
  Operations.GaussianPrecisionMoments.score_variance (perturbedPrecision_pos N i u hz) _

theorem force_eq_mean_loss (N : ℕ) (i : Index N) (u : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    force (kineticFraction N i u) z = 2 * (scoreMean N i u 0 - scoreMean N i u z) := by
  rw [scoreMean_eq N i u (by norm_num), scoreMean_eq N i u hz]
  simp only [zero_mul, add_zero, force, kineticFraction]
  have hp := (precision_pos N i u).ne'
  have hq := (perturbedPrecision_pos N i u hz).ne'
  field_simp

theorem curvature_eq_variance (N : ℕ) (i : Index N) (u : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    curvature (kineticFraction N i u) z = 2 * scoreVariance N i u z := by
  rw [scoreVariance_eq N i u hz]
  unfold curvature kineticFraction
  have hp := (precision_pos N i u).ne'
  have hq := (perturbedPrecision_pos N i u hz).ne'
  field_simp

def branchCurvature (N : ℕ) (B : ℝ) (i : Index N) (z : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
    weight N i u * curvature (kineticFraction N i u) z

def completeCurvature (N : ℕ) (B z : ℝ) : ℝ :=
  ∑ i ∈ support N B, branchCurvature N B i z

theorem curvature_continuous (N : ℕ) (i : Index N)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    Continuous (fun u => weight N i u * curvature (kineticFraction N i u) z) := by
  apply (weight_continuous N i).mul
  unfold curvature
  exact ((kineticFraction_continuous N i).pow 2).div
    ((continuous_const.add (continuous_const.mul (kineticFraction_continuous N i))).pow 2)
    (fun u => pow_ne_zero 2 (ne_of_gt (lt_trans (by norm_num)
      (positive_precision_lower (kineticFraction_nonneg N i u)
        (kineticFraction_le_one N i u) hz))))

theorem branchForce_hasDerivAt (N : ℕ) (B : ℝ) (i : Index N)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    HasDerivAt (branchForce N B i) (branchCurvature N B i z) z :=
  positive_forceIntegral_hasDerivAt _ _ _ _ (kineticFraction_continuous N i)
    (weight_continuous N i) (kineticFraction_nonneg N i) (kineticFraction_le_one N i)
    (fun u => (weight_pos N i u).le) (weight_le_one N i) hz

theorem completeForce_hasDerivAt (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    HasDerivAt (completeForce N B) (completeCurvature N B z) z := by
  classical
  exact HasDerivAt.fun_sum (fun i _ => branchForce_hasDerivAt N B i hz)

theorem sourcePotential_secondDeriv (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    HasDerivAt (fun v => deriv (sourcePotential N B) v) (completeCurvature N B z) z := by
  apply ((completeForce_hasDerivAt N B hz).sub_const 1).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with v hv
  exact (sourcePotential_hasDerivAt N B hv).deriv

theorem completeForce_eq_mean_loss (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    completeForce N B z = 2 * ∑ i ∈ support N B,
      ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
        weight N i u * (scoreMean N i u 0 - scoreMean N i u z) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [branchForce, forceIntegral, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [force_eq_mean_loss N i u hz]
  ring

theorem completeCurvature_eq_variance (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    completeCurvature N B z = 2 * ∑ i ∈ support N B,
      ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
        weight N i u * scoreVariance N i u z := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [branchCurvature, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  dsimp only
  rw [curvature_eq_variance N i u hz]
  ring

theorem completeCurvature_eq_average (N : ℕ) {B z : ℝ}
    (hB : 0 < B) (hz : -(1 / 2 : ℝ) < z) :
    completeCurvature N B z = 2 * HistoryHaarSectionProbability.mass N B *
      HistoryHaarSectionProbability.average N B (fun i u => scoreVariance N i u z) := by
  rw [completeCurvature_eq_variance N B hz, HistoryHaarSectionProbability.average]
  field_simp [(HistoryHaarSectionProbability.mass_pos_of_pos N hB).ne']

private theorem curvature_lower {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : 0 ≤ z) : r ^ 2 / (1 + z) ^ 2 ≤ curvature r z := by
  have hp : 0 < 1 + z * r := by positivity
  have he : 0 < 1 + z := by positivity
  apply div_le_div_of_nonneg_left (sq_nonneg r) (sq_pos_of_pos hp)
  nlinarith [mul_nonneg hz hr, mul_le_mul_of_nonneg_left hr1 hz]

/-- The lower comparison retains the exact trace. It proves positivity at
every finite nonnegative amplitude; it is not a uniform positive gap as
the amplitude tends to infinity. -/
theorem completeCurvature_lower (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    responseTrace N B / (1 + z) ^ 2 ≤ completeCurvature N B z := by
  rw [responseTrace, Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  rw [branchIntegral, ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_mono (Real.sqrt_nonneg _)
    (((kernel_continuous N i).div_const _).intervalIntegrable _ _)
    ((curvature_continuous N i (by linarith : -(1 / 2 : ℝ) < z)).intervalIntegrable _ _)
  intro u
  dsimp only
  rw [kernel_eq_comparison_curvature, curvature_zero]
  calc
    _ = weight N i u * (kineticFraction N i u ^ 2 / (1 + z) ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (curvature_lower (kineticFraction_nonneg N i u) (kineticFraction_le_one N i u) hz)
      (weight_pos N i u).le

theorem completeCurvature_pos (N : ℕ) {B z : ℝ} (hB : 0 < B) (hz : 0 ≤ z) :
    0 < completeCurvature N B z :=
  lt_of_lt_of_le (div_pos (responseTrace_pos N B
    (HistoryHaarSectionProbability.support_nonempty_of_pos N hB))
    (sq_pos_of_pos (by linarith))) (completeCurvature_lower N B hz)

def equilibriumCurvature (N : ℕ) : ℝ := completeCurvature N 5 (equilibrium N)

theorem equilibriumCurvature_pos (N : ℕ) : 0 < equilibriumCurvature N :=
  completeCurvature_pos N (by norm_num) (equilibrium_pos N).le

theorem responseTrace_five_lower (N : ℕ) :
    64 * Real.exp (-4) ≤ responseTrace N 5 := by
  have hf : HistoryHaarSectionContent.fieldResponse N 5 ≤ responseTrace N 5 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => branchIntegral_nonneg N 5 i)
  rw [fieldResponse_five] at hf
  have hd : (4 : ℝ) ≤ HistoryAdjointCasimir.dimension N :=
    by exact_mod_cast HistoryAdjointCasimir.dimension_ge_four N
  have hs : (16 : ℝ) ≤ (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 := by nlinarith
  have hp := HistoryHaarSectionShells.fieldIntegral_nonneg (5 : ℝ) 4
  have hm := mul_nonneg (sub_nonneg.mpr hs) hp
  nlinarith [fieldIntegral_five_lower]

/-- Uniformity here is in the actual history stage, at the selected window
and its own equilibrium. It does not assert a bound at all amplitudes or
after an unrelated probability or vertex normalization. -/
theorem equilibriumCurvature_uniform_lower (N : ℕ) :
    Real.exp (-4) ≤ equilibriumCurvature N := by
  have hpos := equilibrium_pos N
  have hupper := equilibrium_lt_seven N
  have hd : (1 + equilibrium N) ^ 2 ≤ 64 := by
    nlinarith [mul_nonneg (show 0 ≤ 7 - equilibrium N by linarith)
      (show 0 ≤ 9 + equilibrium N by linarith)]
  have he := Real.exp_pos (-4 : ℝ)
  have hl : Real.exp (-4) ≤ responseTrace N 5 / (1 + equilibrium N) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos (show 0 < 1 + equilibrium N by linarith))).mpr
    have := mul_le_mul_of_nonneg_left hd he.le
    linarith [responseTrace_five_lower N]
  exact hl.trans (completeCurvature_lower N 5 hpos.le)

theorem equilibrium_secondDeriv (N : ℕ) :
    HasDerivAt (fun z => deriv (sourcePotential N 5) z)
      (equilibriumCurvature N) (equilibrium N) :=
  sourcePotential_secondDeriv N 5 (by linarith [equilibrium_pos N])

/-- The selected window, its actual equilibrium and the variance identity
are evaluated together, without introducing a radial normalization. -/
theorem equilibrium_fluctuation_restoration (N : ℕ) :
    deriv (fun z => deriv (sourcePotential N 5) z) (equilibrium N) =
      2 * HistoryHaarSectionProbability.mass N 5 *
        HistoryHaarSectionProbability.average N 5
          (fun i u => scoreVariance N i u (equilibrium N)) := by
  rw [(equilibrium_secondDeriv N).deriv]
  exact completeCurvature_eq_average N (by norm_num) (by linarith [equilibrium_pos N])

def equilibriumForce (N : ℕ) (v : ℝ) : ℝ :=
  completeForce N 5 (equilibrium N + v) - 1

def equilibriumPotential (N : ℕ) (v : ℝ) : ℝ :=
  sourcePotential N 5 (equilibrium N + v) - sourcePotential N 5 (equilibrium N)

@[simp] theorem equilibriumForce_zero (N : ℕ) : equilibriumForce N 0 = 0 := by
  simp [equilibriumForce, equilibrium_balance]

@[simp] theorem equilibriumPotential_zero (N : ℕ) : equilibriumPotential N 0 = 0 := by
  simp [equilibriumPotential]

theorem equilibriumForce_hasDerivAt (N : ℕ) {v : ℝ}
    (hv : -(1 / 2 : ℝ) < equilibrium N + v) :
    HasDerivAt (equilibriumForce N) (completeCurvature N 5 (equilibrium N + v)) v := by
  convert! ((completeForce_hasDerivAt N 5 hv).comp v
    ((hasDerivAt_id v).const_add (equilibrium N))).sub_const 1 using 1
  simp

theorem equilibriumForce_hasDerivAt_zero (N : ℕ) :
    HasDerivAt (equilibriumForce N) (equilibriumCurvature N) 0 := by
  simpa [equilibriumCurvature] using equilibriumForce_hasDerivAt N
    (v := 0) (by linarith [equilibrium_pos N])

theorem equilibriumPotential_hasDerivAt (N : ℕ) {v : ℝ}
    (hv : -(1 / 2 : ℝ) < equilibrium N + v) :
    HasDerivAt (equilibriumPotential N) (equilibriumForce N v) v := by
  convert! ((sourcePotential_hasDerivAt N 5 hv).comp v
    ((hasDerivAt_id v).const_add (equilibrium N))).sub_const
      (sourcePotential N 5 (equilibrium N)) using 1
  simp [equilibriumForce]

theorem equilibriumPotential_secondDeriv_zero (N : ℕ) :
    HasDerivAt (fun v => deriv (equilibriumPotential N) v) (equilibriumCurvature N) 0 := by
  apply (equilibriumForce_hasDerivAt_zero N).congr_of_eventuallyEq
  have hc : Continuous (fun v : ℝ => equilibrium N + v) := continuous_const.add continuous_id
  filter_upwards [hc.continuousAt.preimage_mem_nhds
    (isOpen_Ioi.mem_nhds (show -(1 / 2 : ℝ) < equilibrium N + 0 by
      linarith [equilibrium_pos N]))] with v hv
  exact (equilibriumPotential_hasDerivAt N hv).deriv

theorem equilibriumPotential_ray_secondDeriv_zero (N : ℕ) (v : ℝ) :
    HasDerivAt (fun t => deriv (fun s => equilibriumPotential N (s * v)) t)
      (equilibriumCurvature N * v ^ 2) 0 := by
  have hlin (t : ℝ) : HasDerivAt (fun s : ℝ => s * v) v t := by
    simpa using (hasDerivAt_id t).mul_const v
  have hzero : HasDerivAt (equilibriumForce N) (equilibriumCurvature N) (0 * v) := by
    simpa using equilibriumForce_hasDerivAt_zero N
  have hd := (hzero.comp 0 (hlin 0)).mul_const v
  have hc : Continuous (fun t : ℝ => equilibrium N + t * v) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have he : (fun t => deriv (fun s => equilibriumPotential N (s * v)) t) =ᶠ[𝓝 0]
      fun t => equilibriumForce N (t * v) * v := by
    filter_upwards [hc.continuousAt.preimage_mem_nhds
      (isOpen_Ioi.mem_nhds (show -(1 / 2 : ℝ) < equilibrium N + 0 * v by
        simpa using (show -(1 / 2 : ℝ) < equilibrium N by linarith [equilibrium_pos N])))]
      with t ht
    exact ((equilibriumPotential_hasDerivAt N ht).comp t (hlin t)).deriv
  convert! hd.congr_of_eventuallyEq he using 1
  ring

structure Conclusions : Prop where
  actual_score_mean : ∀ N i u z, -(1 / 2 : ℝ) < z →
    force (kineticFraction N i u) z = 2 * (scoreMean N i u 0 - scoreMean N i u z)
  actual_score_variance : ∀ N i u z, -(1 / 2 : ℝ) < z →
    curvature (kineticFraction N i u) z = 2 * scoreVariance N i u z
  full_force_variation : ∀ N B z, -(1 / 2 : ℝ) < z →
    HasDerivAt (completeForce N B) (completeCurvature N B z) z
  full_positive_curvature : ∀ N B z, 0 < B → 0 ≤ z → 0 < completeCurvature N B z
  actual_equilibrium_curvature : ∀ N,
    HasDerivAt (fun z => deriv (sourcePotential N 5) z)
      (equilibriumCurvature N) (equilibrium N)
  uniform_equilibrium_restoration : ∀ N, Real.exp (-4) ≤ equilibriumCurvature N
  selected_window_fluctuations : ∀ N,
    deriv (fun z => deriv (sourcePotential N 5) z) (equilibrium N) =
      2 * HistoryHaarSectionProbability.mass N 5 *
        HistoryHaarSectionProbability.average N 5
          (fun i u => scoreVariance N i u (equilibrium N))
  centred_ray_curvature : ∀ N v,
    HasDerivAt (fun t => deriv (fun s => equilibriumPotential N (s * v)) t)
      (equilibriumCurvature N * v ^ 2) 0

theorem generated : Conclusions where
  actual_score_mean := fun N i u _ hz => force_eq_mean_loss N i u hz
  actual_score_variance := fun N i u _ hz => curvature_eq_variance N i u hz
  full_force_variation := fun N B _ hz => completeForce_hasDerivAt N B hz
  full_positive_curvature := fun N _ _ hB hz => completeCurvature_pos N hB hz
  actual_equilibrium_curvature := equilibrium_secondDeriv
  uniform_equilibrium_restoration := equilibriumCurvature_uniform_lower
  selected_window_fluctuations := equilibrium_fluctuation_restoration
  centred_ray_curvature := equilibriumPotential_ray_secondDeriv_zero

end GeneratedFoundations.Arithmetic.HistoryHaarSectionRestoration
