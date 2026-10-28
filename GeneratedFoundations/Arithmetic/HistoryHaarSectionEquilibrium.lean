module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionSourceBalance
public import GeneratedFoundations.Operations.GaussianPrecisionBregman
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Global Gaussian comparison equilibria on the admissible windows

The shell and content conditions of the source-unit comparison are evaluated
on the original joint window. The exact tangent remainder is the relative
entropy between two perturbed Gaussian laws, averaged with the unchanged
original spectral weights. It proves a strict global minimum, rather than
only a stationary response equation. Every integer window from five
onwards admits such a minimum. At level five the field and scalar
position counts are both one; this does not single out that window.

This is the variational completion of the source-unit comparison protocol.
It does not identify the comparison amplitude with a coordinate scale or
the scalar Casimir positions with physical Dirac positions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionEquilibrium

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionSourceBalance
open HistoryHaarSectionJointHessian (Index)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def branchGap (N : ℕ) (B : ℝ) (i : Index N) (z v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
    weight N i u * betweenCost (kineticFraction N i u) z v

def comparisonGap (N : ℕ) (B z v : ℝ) : ℝ :=
  ∑ i ∈ support N B, branchGap N B i z v

/-- Both laws vary, but the label and frequency measure is the same original
window measure in both directions of the comparison. -/
def betweenRelativeEntropy (N : ℕ) (B z v : ℝ) : ℝ :=
  HistoryHaarSectionProbability.average N B (fun i u =>
    (InformationTheory.klDiv
      (Operations.GaussianPrecisionKL.law
        (precision N i u + z * kineticPrecision N i u))
      (Operations.GaussianPrecisionKL.law
        (precision N i u + v * kineticPrecision N i u))).toReal)

theorem relative_precision_pos (N : ℕ) (i : Index N) (u : ℝ) {z : ℝ}
    (hz : 0 ≤ z) : 0 < 1 + z * kineticFraction N i u := by
  nlinarith [kineticFraction_nonneg N i u]

theorem comparison_integrand_continuous (N : ℕ) (i : Index N) {z : ℝ}
    (hz : 0 ≤ z) :
    Continuous (fun u => weight N i u * cost (kineticFraction N i u) z) := by
  unfold cost
  exact (weight_continuous N i).mul
    ((continuous_const.mul (kineticFraction_continuous N i)).sub
      ((continuous_const.add (continuous_const.mul (kineticFraction_continuous N i))).log
        (fun u => (relative_precision_pos N i u hz).ne')))

theorem gap_integrand_continuous (N : ℕ) (i : Index N) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) :
    Continuous (fun u => weight N i u * betweenCost (kineticFraction N i u) z v) := by
  have he (u : ℝ) : weight N i u * betweenCost (kineticFraction N i u) z v =
      weight N i u * cost (kineticFraction N i u) v -
      weight N i u * cost (kineticFraction N i u) z -
      (weight N i u * force (kineticFraction N i u) z) * (v - z) := by
    rw [betweenCost_eq (relative_precision_pos N i u hz) (relative_precision_pos N i u hv)]
    ring
  simp_rw [he]
  exact ((comparison_integrand_continuous N i hv).sub
    (comparison_integrand_continuous N i hz)).sub ((force_continuous N i hz).mul_const _)

theorem branchGap_eq (N : ℕ) (B : ℝ) (i : Index N) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) :
    branchGap N B i z v = branchComparison N B i v - branchComparison N B i z -
      branchForce N B i z * (v - z) := by
  have he (u : ℝ) : weight N i u * betweenCost (kineticFraction N i u) z v =
      weight N i u * cost (kineticFraction N i u) v -
      weight N i u * cost (kineticFraction N i u) z -
      (weight N i u * force (kineticFraction N i u) z) * (v - z) := by
    rw [betweenCost_eq (relative_precision_pos N i u hz) (relative_precision_pos N i u hv)]
    ring
  unfold branchGap branchComparison comparisonIntegral branchForce forceIntegral
  simp_rw [he]
  rw [intervalIntegral.integral_sub
    (((comparison_integrand_continuous N i hv).intervalIntegrable _ _).sub
      ((comparison_integrand_continuous N i hz).intervalIntegrable _ _))
    (((force_continuous N i hz).mul_const _).intervalIntegrable _ _),
    intervalIntegral.integral_sub
      ((comparison_integrand_continuous N i hv).intervalIntegrable _ _)
      ((comparison_integrand_continuous N i hz).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const]

theorem comparisonGap_eq (N : ℕ) (B : ℝ) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) :
    comparisonGap N B z v = comparison N B v - comparison N B z -
      completeForce N B z * (v - z) := by
  simp only [comparisonGap, branchGap_eq N B _ hz hv, Finset.sum_sub_distrib,
    Finset.sum_mul, comparison, completeForce]

theorem branchGap_nonneg (N : ℕ) (B : ℝ) (i : Index N) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) : 0 ≤ branchGap N B i z v :=
  intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
    (fun u => mul_nonneg (weight_pos N i u).le
      (betweenCost_nonneg (relative_precision_pos N i u hz) (relative_precision_pos N i u hv)))

theorem comparisonGap_nonneg (N : ℕ) (B : ℝ) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) : 0 ≤ comparisonGap N B z v :=
  Finset.sum_nonneg (fun i _ => branchGap_nonneg N B i hz hv)

theorem branchGap_pos (N : ℕ) (B : ℝ) (i : Index N) (hi : i ∈ support N B)
    {z v : ℝ} (hz : 0 ≤ z) (hv : 0 ≤ v) (hne : v ≠ z) :
    0 < branchGap N B i z v := by
  have ht : 0 < Real.sqrt (B - kinetic N i) :=
    Real.sqrt_pos.mpr (sub_pos.mpr ((mem_support N B i).mp hi))
  let u := Real.sqrt (B - kinetic N i) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hr : 0 < kineticFraction N i u := div_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (kinetic_nonneg N i))
    (precision_pos N i u)
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    continuousOn_const (gap_integrand_continuous N i hz hv).continuousOn
    (fun t _ => mul_nonneg (weight_pos N i t).le
      (betweenCost_nonneg (relative_precision_pos N i t hz) (relative_precision_pos N i t hv)))
    ⟨u, ⟨hu.le, by dsimp [u]; linarith⟩,
      mul_pos (weight_pos N i u) (betweenCost_pos hr
        (relative_precision_pos N i u hz) (relative_precision_pos N i u hv) hne)⟩
  simpa only [intervalIntegral.integral_zero, branchGap] using h

theorem comparisonGap_pos (N : ℕ) {B z v : ℝ} (hB : 0 < B)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hne : v ≠ z) : 0 < comparisonGap N B z v := by
  obtain ⟨i, hi⟩ := HistoryHaarSectionProbability.support_nonempty_of_pos N hB
  exact Finset.sum_pos' (fun j _ => branchGap_nonneg N B j hz hv)
    ⟨i, hi, branchGap_pos N B i hi hz hv hne⟩

theorem betweenRelativeEntropy_eq_gap (N : ℕ) (B : ℝ) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) : betweenRelativeEntropy N B z v =
      comparisonGap N B z v / (2 * HistoryHaarSectionProbability.mass N B) := by
  unfold betweenRelativeEntropy HistoryHaarSectionProbability.average
  have he (i : Index N) (u : ℝ) := Operations.GaussianPrecisionKL.between_varied_precisions
    (precision_pos N i u)
    (HistoryHaarSectionSourceBalance.perturbedPrecision_pos N i u (z := z) (by linarith))
    (HistoryHaarSectionSourceBalance.perturbedPrecision_pos N i u (z := v) (by linarith))
  simp_rw [he]
  change (∑ i ∈ support N B, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
    weight N i u * (betweenCost (kineticFraction N i u) z v / 2)) /
      HistoryHaarSectionProbability.mass N B = _
  simp_rw [← mul_div_assoc, intervalIntegral.integral_div]
  rw [← Finset.sum_div]
  change (comparisonGap N B z v / 2) / HistoryHaarSectionProbability.mass N B = _
  rw [div_div]

theorem betweenRelativeEntropy_pos (N : ℕ) {B z v : ℝ} (hB : 0 < B)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (hne : v ≠ z) :
    0 < betweenRelativeEntropy N B z v := by
  rw [betweenRelativeEntropy_eq_gap N B hz hv]
  exact div_pos (comparisonGap_pos N hB hz hv hne)
    (mul_pos (by norm_num) (HistoryHaarSectionProbability.mass_pos_of_pos N hB))

theorem potential_difference (N : ℕ) (B : ℝ) {z v : ℝ}
    (hz : 0 ≤ z) (hv : 0 ≤ v) :
    sourcePotential N B v - sourcePotential N B z = comparisonGap N B z v +
      (completeForce N B z - 1) * (v - z) := by
  rw [comparisonGap_eq N B hz hv, sourcePotential, sourcePotential,
    HistoryGaussianCovariance.generatedIntensity_eq]
  ring

theorem balance_potential_difference (N : ℕ) {B z v : ℝ} (hB : 0 < B)
    (hz : 0 ≤ z) (hv : 0 ≤ v) (he : completeForce N B z = 1) :
    sourcePotential N B v - sourcePotential N B z =
      2 * HistoryHaarSectionProbability.mass N B * betweenRelativeEntropy N B z v := by
  rw [potential_difference N B hz hv, he, sub_self, zero_mul, add_zero,
    betweenRelativeEntropy_eq_gap N B hz hv]
  have hm := HistoryHaarSectionProbability.mass_pos_of_pos N hB
  field_simp

theorem global_minimum_of_balance (N : ℕ) {B z : ℝ} (hB : 0 < B)
    (hz : 0 ≤ z) (he : completeForce N B z = 1) :
    ∀ v : ℝ, 0 ≤ v → sourcePotential N B z ≤ sourcePotential N B v ∧
      (sourcePotential N B v = sourcePotential N B z ↔ v = z) := by
  intro v hv
  have hd := potential_difference N B hz hv
  rw [he, sub_self, zero_mul, add_zero] at hd
  refine ⟨by linarith [comparisonGap_nonneg N B hz hv], ?_⟩
  constructor
  · intro hval
    by_contra hne
    have hp := comparisonGap_pos N hB hz hv hne
    linarith
  · rintro rfl
    rfl

theorem sourcePotential_strictAnti_below_four (N : ℕ) {B : ℝ} (hB : B ≤ 4) :
    StrictAntiOn (sourcePotential N B) (Ici 0) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
  · intro z hz
    change 0 ≤ z at hz
    exact (sourcePotential_hasDerivAt N B (by linarith)).continuousAt.continuousWithinAt
  · intro z hz
    have hz0 : 0 ≤ z := (interior_subset hz)
    rw [(sourcePotential_hasDerivAt N B (by linarith : -(1 / 2 : ℝ) < z)).deriv]
    linarith [no_balance_below_four N hB hz0]

theorem no_minimum_below_four (N : ℕ) {B : ℝ} (hB : B ≤ 4) :
    ¬ ∃ z : ℝ, 0 ≤ z ∧ ∀ v : ℝ, 0 ≤ v → sourcePotential N B z ≤ sourcePotential N B v := by
  rintro ⟨z, hz, hmin⟩
  have hd := sourcePotential_strictAnti_below_four N hB hz
    (show 0 ≤ z + 1 by linarith) (by linarith : z < z + 1)
  exact not_lt_of_ge (hmin (z + 1) (by linarith)) hd

def HasMinimum (N R : ℕ) : Prop :=
  ∃ z : ℝ, 0 ≤ z ∧ ∀ v : ℝ, 0 ≤ v → sourcePotential N R z ≤ sourcePotential N R v

theorem hasMinimum_iff (N R : ℕ) : HasMinimum N R ↔ 5 ≤ R := by
  constructor
  · intro h
    by_contra hn
    have hR : R ≤ 4 := by omega
    exact no_minimum_below_four N (B := (R : ℝ)) (by exact_mod_cast hR) h
  · intro hR
    obtain ⟨z, hz, _⟩ := existsUnique_balance_above_five N
      (B := (R : ℝ)) (by exact_mod_cast hR)
    refine ⟨z, hz.1.le, fun v hv => ?_⟩
    exact (global_minimum_of_balance N (B := (R : ℝ))
      (by
        have hRR : (5 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
        linarith) hz.1.le hz.2 v hv).1

def equilibrium (N : ℕ) : ℝ :=
  Classical.choose (existsUnique_balance_above_five N (B := 5) le_rfl).exists

theorem equilibrium_pos (N : ℕ) : 0 < equilibrium N :=
  (Classical.choose_spec (existsUnique_balance_above_five N (B := 5) le_rfl).exists).1

theorem equilibrium_balance (N : ℕ) : completeForce N 5 (equilibrium N) = 1 :=
  (Classical.choose_spec (existsUnique_balance_above_five N (B := 5) le_rfl).exists).2

theorem equilibrium_lt_seven (N : ℕ) : equilibrium N < 7 := by
  by_contra hn
  have hle := completeForce_strictMonoOn N (B := 5) (by norm_num)
  have hm := hle.monotoneOn (show (7 : ℝ) ∈ Ici 0 by norm_num)
    (equilibrium_pos N).le (le_of_not_gt hn)
  rw [equilibrium_balance] at hm
  linarith [completeForce_five_seven_gt_one N]

theorem equilibrium_global_minimum (N : ℕ) :
    ∀ v : ℝ, 0 ≤ v → sourcePotential N 5 (equilibrium N) ≤ sourcePotential N 5 v ∧
      (sourcePotential N 5 v = sourcePotential N 5 (equilibrium N) ↔ v = equilibrium N) :=
  global_minimum_of_balance N (by norm_num) (equilibrium_pos N).le (equilibrium_balance N)

theorem forwardEntropy_eq (N : ℕ) (B : ℝ) {z : ℝ} (_hz : 0 ≤ z) :
    betweenRelativeEntropy N B 0 z = HistoryHaarSectionProbability.relativeEntropy N B z := by
  simp only [betweenRelativeEntropy, zero_mul, add_zero,
    HistoryHaarSectionProbability.relativeEntropy]

theorem comparison_add_reverse (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    comparison N B z + comparisonGap N B z 0 = z * completeForce N B z := by
  rw [comparisonGap_eq N B hz (by norm_num), comparison_zero]
  ring

theorem gaussian_entropy_balance (N : ℕ) {B z : ℝ} (hB : 0 < B)
    (hz : 0 ≤ z) :
    2 * HistoryHaarSectionProbability.mass N B *
      (HistoryHaarSectionProbability.relativeEntropy N B z + betweenRelativeEntropy N B z 0) =
        z * completeForce N B z := by
  rw [HistoryHaarSectionSourceBalance.relativeEntropy_eq_comparison N B (by linarith),
    betweenRelativeEntropy_eq_gap N B hz (by norm_num), ← add_div]
  have hm := HistoryHaarSectionProbability.mass_pos_of_pos N hB
  rw [mul_div_cancel₀ _ (mul_pos (by norm_num : (0 : ℝ) < 2) hm).ne']
  exact comparison_add_reverse N B hz

theorem equilibrium_entropy_balance (N : ℕ) :
    2 * HistoryHaarSectionProbability.mass N 5 *
      (HistoryHaarSectionProbability.relativeEntropy N 5 (equilibrium N) +
        betweenRelativeEntropy N 5 (equilibrium N) 0) = equilibrium N := by
  rw [gaussian_entropy_balance N (by norm_num) (equilibrium_pos N).le,
    equilibrium_balance, mul_one]

theorem equilibrium_entropies_pos (N : ℕ) :
    0 < HistoryHaarSectionProbability.relativeEntropy N 5 (equilibrium N) ∧
      0 < betweenRelativeEntropy N 5 (equilibrium N) 0 := by
  constructor
  · rw [← forwardEntropy_eq N 5 (equilibrium_pos N).le]
    exact betweenRelativeEntropy_pos N (by norm_num) (by norm_num)
      (equilibrium_pos N).le (equilibrium_pos N).ne'
  · exact betweenRelativeEntropy_pos N (by norm_num) (equilibrium_pos N).le
      (by norm_num) (ne_of_lt (equilibrium_pos N))

theorem equilibrium_potential_eq_reverseEntropy (N : ℕ) :
    sourcePotential N 5 (equilibrium N) =
      -(2 * HistoryHaarSectionProbability.mass N 5 *
        betweenRelativeEntropy N 5 (equilibrium N) 0) := by
  have h := balance_potential_difference N (B := 5) (z := equilibrium N) (v := 0)
    (by norm_num) (equilibrium_pos N).le (by norm_num) (equilibrium_balance N)
  have hzero : sourcePotential N 5 0 = 0 := by simp [sourcePotential]
  rw [hzero] at h
  linarith

structure Conclusions : Prop where
  exact_two_state_comparison : ∀ N B z v, 0 ≤ z → 0 ≤ v →
    betweenRelativeEntropy N B z v =
      comparisonGap N B z v / (2 * HistoryHaarSectionProbability.mass N B)
  global_minimum_window : ∀ N R, HasMinimum N R ↔ 5 ≤ R
  actual_joint_content :
    HistoryHaarSectionRetention.fieldPositionCount 5 = 1 ∧
      HistoryHaarSectionContent.positionCount 5 = 1
  calculated_equilibrium : ∀ N, 0 < equilibrium N ∧ equilibrium N < 7
  unique_global_minimum : ∀ N v, 0 ≤ v →
    sourcePotential N 5 (equilibrium N) ≤ sourcePotential N 5 v ∧
      (sourcePotential N 5 v = sourcePotential N 5 (equilibrium N) ↔ v = equilibrium N)
  exact_entropy_balance : ∀ N,
    2 * HistoryHaarSectionProbability.mass N 5 *
      (HistoryHaarSectionProbability.relativeEntropy N 5 (equilibrium N) +
        betweenRelativeEntropy N 5 (equilibrium N) 0) = equilibrium N
  positive_two_direction_entropy : ∀ N,
    0 < HistoryHaarSectionProbability.relativeEntropy N 5 (equilibrium N) ∧
      0 < betweenRelativeEntropy N 5 (equilibrium N) 0

theorem generated : Conclusions where
  exact_two_state_comparison := fun N B _ _ hz hv => betweenRelativeEntropy_eq_gap N B hz hv
  global_minimum_window := hasMinimum_iff
  actual_joint_content := balancedLevel_five_joint_content
  calculated_equilibrium := fun N => ⟨equilibrium_pos N, equilibrium_lt_seven N⟩
  unique_global_minimum := equilibrium_global_minimum
  exact_entropy_balance := equilibrium_entropy_balance
  positive_two_direction_entropy := equilibrium_entropies_pos

end GeneratedFoundations.Arithmetic.HistoryHaarSectionEquilibrium
