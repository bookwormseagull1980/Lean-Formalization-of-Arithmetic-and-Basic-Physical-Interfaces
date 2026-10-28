module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGaussianVariation
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionSourceBalance
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# All equilibria of the common Gaussian heat-vertex response

The vertex is the one evaluated in the complete joint Gaussian partition.
Frequency is integrated with its original Lebesgue measure; its heat factor
already belongs to the vertex. No second, external Gaussian weight is
inserted into the logarithm or its derivatives.

The unit-work comparison is classified on its entire positive amplitude ray:
it has exactly one equilibrium precisely when its complete score capacity
exceeds the generated source unit. This is a classification of every window,
not a choice of the first feasible integer. In particular the unit-work
comparison admits different windows, so its amplitude uniqueness cannot be
used as joint endpoint-window uniqueness.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionCommonBalance

open HistoryHaarSectionWindow
open HistoryHaarSectionJointHessian (Index)
open HistoryHaarSectionComparison (kineticPrecision kineticFraction weight weight_pos)
open HistoryHaarSectionGaussianVariation (vertexRatio vertexRatio_nonneg vertexRatio_le)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

theorem vertexRatio_continuous (N : ℕ) (i : Index N) :
    Continuous (vertexRatio N i) := by
  rw [show vertexRatio N i = fun u => Real.exp (-kineticPrecision N i u / 2) *
      kineticFraction N i u from funext (HistoryHaarSectionGaussianVariation.vertexRatio_eq N i)]
  have hkin : Continuous (kineticPrecision N i) := by unfold kineticPrecision; fun_prop
  exact (Real.continuous_exp.comp (hkin.neg.div_const 2)).mul
    (HistoryHaarSectionComparison.kineticFraction_continuous N i)

theorem vertexRatio_le_one (N : ℕ) (i : Index N) (u : ℝ) : vertexRatio N i u ≤ 1 :=
  (vertexRatio_le N i u).trans (HistoryHaarSectionComparison.kineticFraction_le_one N i u)

def branchCapacity (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), vertexRatio N i u

def capacity (N : ℕ) (B : ℝ) : ℝ := ∑ i ∈ support N B, branchCapacity N B i

def branchForce (N : ℕ) (B : ℝ) (i : Index N) (z : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), force (vertexRatio N i u) z

def completeForce (N : ℕ) (B z : ℝ) : ℝ := ∑ i ∈ support N B, branchForce N B i z

def branchComparison (N : ℕ) (B : ℝ) (i : Index N) (z : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), cost (vertexRatio N i u) z

def comparison (N : ℕ) (B z : ℝ) : ℝ := ∑ i ∈ support N B, branchComparison N B i z

/-- The same unit-work protocol as before, now applied to the actual common
heat-score partition. Identifying it with a geometric endpoint action would
be a further theorem, not part of this definition. -/
def unitWorkPotential (N : ℕ) (B z : ℝ) : ℝ :=
  comparison N B z - HistoryGaussianCovariance.generatedIntensity N * z

def frequencyVolume (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, Real.sqrt (B - kinetic N i)

theorem force_continuous (N : ℕ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    Continuous (fun u => force (vertexRatio N i u) z) := by
  unfold force
  exact (vertexRatio_continuous N i).sub ((vertexRatio_continuous N i).div
    (continuous_const.add (continuous_const.mul (vertexRatio_continuous N i)))
    (fun u => (HistoryHaarSectionGaussianVariation.relative_pos N i u hz).ne'))

theorem comparison_hasDerivAt (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (comparison N B) (completeForce N B z) z := by
  have h (i : Index N) := positive_comparisonIntegral_hasDerivAt (vertexRatio N i)
    (fun _ => (1 : ℝ)) 0 (Real.sqrt (B - kinetic N i))
    (vertexRatio_continuous N i) continuous_const (vertexRatio_nonneg N i)
    (vertexRatio_le_one N i) (fun _ => zero_le_one) (fun _ => le_rfl)
    (show z ∈ Ioi (-(1 / 2 : ℝ)) by change -(1 / 2 : ℝ) < z; linarith)
  have hd := HasDerivAt.fun_sum (fun i (_ : i ∈ support N B) => h i)
  simp only [comparisonIntegral, forceIntegral, one_mul] at hd
  convert! hd using 1

theorem unitWorkPotential_hasDerivAt (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    HasDerivAt (unitWorkPotential N B) (completeForce N B z - 1) z := by
  convert! (comparison_hasDerivAt N B hz).sub
    ((hasDerivAt_id z).const_mul (HistoryGaussianCovariance.generatedIntensity N)) using 1
  rw [HistoryGaussianCovariance.generatedIntensity_eq]
  norm_num

theorem completeForce_continuousOn (N : ℕ) (B : ℝ) :
    ContinuousOn (completeForce N B) (Ici 0) := by
  intro z hz
  change 0 ≤ z at hz
  have h (i : Index N) := positive_forceIntegral_hasDerivAt (vertexRatio N i)
    (fun _ => (1 : ℝ)) 0 (Real.sqrt (B - kinetic N i))
    (vertexRatio_continuous N i) continuous_const (vertexRatio_nonneg N i)
    (vertexRatio_le_one N i) (fun _ => zero_le_one) (fun _ => le_rfl)
    (show z ∈ Ioi (-(1 / 2 : ℝ)) by change -(1 / 2 : ℝ) < z; linarith)
  have hc := (HasDerivAt.fun_sum (fun i (_ : i ∈ support N B) => h i)).continuousAt.continuousWithinAt (s := Ici 0)
  simp only [forceIntegral, one_mul] at hc
  convert! hc using 1

@[simp] theorem completeForce_zero (N : ℕ) (B : ℝ) : completeForce N B 0 = 0 := by
  simp [completeForce, branchForce]

theorem vertexRatio_pos_of_pos_frequency (N : ℕ) (i : Index N) {u : ℝ} (hu : 0 < u) :
    0 < vertexRatio N i u := by
  rw [HistoryHaarSectionGaussianVariation.vertexRatio_eq]
  exact mul_pos (Real.exp_pos _) (div_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (kinetic_nonneg N i))
    (HistoryHaarSectionComparison.precision_pos N i u))

theorem branchForce_strictMonoOn (N : ℕ) (B : ℝ) (i : Index N)
    (hi : i ∈ support N B) : StrictMonoOn (branchForce N B i) (Ici 0) := by
  intro z hz v hv hzv
  have ht : 0 < Real.sqrt (B - kinetic N i) :=
    Real.sqrt_pos.mpr (sub_pos.mpr ((mem_support N B i).mp hi))
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (force_continuous N i hz).continuousOn (force_continuous N i hv).continuousOn
    (fun u _ => HistoryHaarSectionSourceBalance.force_monotone_nonneg
      (vertexRatio_nonneg N i u) hz hv hzv.le)
  let u := Real.sqrt (B - kinetic N i) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  exact ⟨u, ⟨hu.le, by dsimp [u]; linarith⟩,
    HistoryHaarSectionSourceBalance.force_strictMonoOn_nonneg
      (vertexRatio_pos_of_pos_frequency N i hu) hz hv hzv⟩

theorem branchForce_monotone (N : ℕ) (B : ℝ) (i : Index N) :
    MonotoneOn (branchForce N B i) (Ici 0) := by
  intro z hz v hv hzv
  exact intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
    ((force_continuous N i hz).intervalIntegrable _ _)
    ((force_continuous N i hv).intervalIntegrable _ _)
    (fun u _ => HistoryHaarSectionSourceBalance.force_monotone_nonneg
      (vertexRatio_nonneg N i u) hz hv hzv)

theorem completeForce_strictMonoOn (N : ℕ) {B : ℝ} (hB : 0 < B) :
    StrictMonoOn (completeForce N B) (Ici 0) := by
  intro z hz v hv hzv
  obtain ⟨i, hi⟩ := HistoryHaarSectionProbability.support_nonempty_of_pos N hB
  exact Finset.sum_lt_sum (fun j _ => branchForce_monotone N B j hz hv hzv.le)
    ⟨i, hi, branchForce_strictMonoOn N B i hi hz hv hzv⟩

theorem branchForce_lt_capacity (N : ℕ) (B : ℝ) (i : Index N)
    (hi : i ∈ support N B) {z : ℝ} (hz : 0 ≤ z) :
    branchForce N B i z < branchCapacity N B i := by
  have ht : 0 < Real.sqrt (B - kinetic N i) :=
    Real.sqrt_pos.mpr (sub_pos.mpr ((mem_support N B i).mp hi))
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (force_continuous N i hz).continuousOn (vertexRatio_continuous N i).continuousOn
    (fun u _ => HistoryHaarSectionSourceBalance.force_le_fraction (vertexRatio_nonneg N i u) hz)
  let u := Real.sqrt (B - kinetic N i) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  refine ⟨u, ⟨hu.le, by dsimp [u]; linarith⟩, ?_⟩
  have hp := div_pos (vertexRatio_pos_of_pos_frequency N i hu)
    (HistoryHaarSectionGaussianVariation.relative_pos N i u hz)
  unfold force
  linarith

theorem completeForce_lt_capacity (N : ℕ) {B : ℝ} (hB : 0 < B)
    {z : ℝ} (hz : 0 ≤ z) : completeForce N B z < capacity N B := by
  obtain ⟨i, hi⟩ := HistoryHaarSectionProbability.support_nonempty_of_pos N hB
  exact Finset.sum_lt_sum
    (fun j hj => (branchForce_lt_capacity N B j hj hz).le)
    ⟨i, hi, branchForce_lt_capacity N B i hi hz⟩

/-- The entire nonlinear saturation remainder, before any bound. -/
theorem capacity_sub_force_eq (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    capacity N B - completeForce N B z =
      ∑ i ∈ support N B, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
        vertexRatio N i u / (1 + z * vertexRatio N i u) := by
  rw [capacity, completeForce, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [branchCapacity, branchForce, ← intervalIntegral.integral_sub
    ((vertexRatio_continuous N i).intervalIntegrable _ _)
    ((force_continuous N i hz).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro u _
  unfold force
  ring

theorem frequencyVolume_nonneg (N : ℕ) (B : ℝ) : 0 ≤ frequencyVolume N B :=
  Finset.sum_nonneg (fun _ _ => Real.sqrt_nonneg _)

/-- The bound is on the exact saturation deficit. No expansion in z is used. -/
theorem capacity_sub_force_le (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 < z) :
    capacity N B - completeForce N B z ≤ frequencyVolume N B / z := by
  have h (i : Index N) : branchCapacity N B i - branchForce N B i z ≤
      Real.sqrt (B - kinetic N i) / z := by
    rw [branchCapacity, branchForce, ← intervalIntegral.integral_sub
      ((vertexRatio_continuous N i).intervalIntegrable _ _)
      ((force_continuous N i hz.le).intervalIntegrable _ _)]
    have hc : Continuous (fun u : ℝ => 1 / z) := continuous_const
    have hi := intervalIntegral.integral_mono_on (μ := volume) (Real.sqrt_nonneg (B - kinetic N i))
      (((vertexRatio_continuous N i).sub (force_continuous N i hz.le)).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _) (fun u _ => ?_)
    · simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one_div, Pi.sub_apply] using hi
    · change vertexRatio N i u - force (vertexRatio N i u) z ≤ 1 / z
      have hp := HistoryHaarSectionGaussianVariation.relative_pos N i u hz.le
      rw [force]
      have hd : vertexRatio N i u / (1 + z * vertexRatio N i u) ≤ 1 / z := by
        rw [div_le_div_iff₀ hp hz]
        nlinarith
      linarith
  simpa only [capacity, completeForce, frequencyVolume, ← Finset.sum_sub_distrib,
    Finset.sum_div] using Finset.sum_le_sum (fun i _ => h i)

/-- A complete test over the entire amplitude ray for each original window. -/
theorem existsUnique_balance_iff (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (∃! z : ℝ, 0 < z ∧ completeForce N B z = 1) ↔ 1 < capacity N B := by
  constructor
  · rintro ⟨z, ⟨hz, he⟩, _⟩
    simpa only [he] using completeForce_lt_capacity N hB hz.le
  · intro hcap
    let z₀ := (frequencyVolume N B + 1) / (capacity N B - 1)
    have hz₀ : 0 < z₀ := div_pos (by linarith [frequencyVolume_nonneg N B]) (by linarith)
    have htop : 1 < completeForce N B z₀ := by
      have hd := capacity_sub_force_le N B hz₀
      have hid : z₀ * (capacity N B - 1) = frequencyVolume N B + 1 := by
        exact div_mul_cancel₀ _ (sub_pos.mpr hcap).ne'
      have hdiv : frequencyVolume N B / z₀ < capacity N B - 1 :=
        (div_lt_iff₀ hz₀).mpr (by nlinarith [hid])
      linarith
    have hcont := (completeForce_continuousOn N B).mono
      (show Icc (0 : ℝ) z₀ ⊆ Ici 0 from fun _ h => h.1)
    obtain ⟨z, hz, he⟩ := intermediate_value_Icc (le_of_lt hz₀) hcont
      (show (1 : ℝ) ∈ Icc (completeForce N B 0) (completeForce N B z₀) by
        rw [completeForce_zero]; exact ⟨by norm_num, htop.le⟩)
    have hz0 : 0 < z := by
      by_contra hn
      have heq : z = 0 := le_antisymm (le_of_not_gt hn) hz.1
      subst z
      norm_num at he
    refine ⟨z, ⟨hz0, he⟩, ?_⟩
    intro v hv
    exact (completeForce_strictMonoOn N hB).injOn hv.1.le hz0.le (hv.2.trans he.symm)

/-- The exact common capacity dominates the old finite-amplitude comparison.
This use of the old comparison is a one-sided bound, not an identification. -/
theorem old_force_le_capacity (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    HistoryHaarSectionComparison.completeForce N B z ≤ capacity N B := by
  have h (i : Index N) : HistoryHaarSectionComparison.branchForce N B i z ≤
      branchCapacity N B i := by
    apply intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
      ((HistoryHaarSectionSourceBalance.force_continuous N i hz).intervalIntegrable _ _)
      ((vertexRatio_continuous N i).intervalIntegrable _ _)
    intro u _
    have hr := HistoryHaarSectionComparison.kineticFraction_nonneg N i u
    have hf := HistoryHaarSectionSourceBalance.force_le_fraction hr hz
    have he : weight N i u ≤ Real.exp (-kineticPrecision N i u / 2) := by
      apply Real.exp_le_exp.mpr
      have hk := HistoryHaarSectionGaussianVariation.kineticPrecision_nonneg N i u
      change -kineticPrecision N i u ≤ -kineticPrecision N i u / 2
      linarith
    rw [HistoryHaarSectionGaussianVariation.vertexRatio_eq]
    exact (mul_le_mul_of_nonneg_left hf (weight_pos N i u).le).trans
      (mul_le_mul_of_nonneg_right he hr)
  exact Finset.sum_le_sum (fun i _ => h i)

theorem capacity_gt_one_above_five (N : ℕ) {B : ℝ} (hB : 5 ≤ B) : 1 < capacity N B :=
  lt_of_lt_of_le
    (lt_of_lt_of_le (HistoryHaarSectionSourceBalance.completeForce_five_seven_gt_one N)
      (HistoryHaarSectionSourceBalance.completeForce_mono_window N (z := 7) (by norm_num) hB))
    (old_force_le_capacity N B (z := 7) (by norm_num))

theorem existsUnique_balance_above_five (N : ℕ) {B : ℝ} (hB : 5 ≤ B) :
    ∃! z : ℝ, 0 < z ∧ completeForce N B z = 1 :=
  (existsUnique_balance_iff N (by linarith)).mpr (capacity_gt_one_above_five N hB)

/-- Distinct windows really survive the full common Gaussian response.
The two amplitudes are not assumed equal, and no first-feasible rule is used. -/
theorem distinct_windows_admit_balance (N : ℕ) :
    ∃ z₅ z₆ : ℝ, 0 < z₅ ∧ completeForce N 5 z₅ = 1 ∧
      0 < z₆ ∧ completeForce N 6 z₆ = 1 := by
  obtain ⟨z₅, hz₅, _⟩ := existsUnique_balance_above_five N (B := 5) le_rfl
  obtain ⟨z₆, hz₆, _⟩ := existsUnique_balance_above_five N (B := 6) (by norm_num)
  exact ⟨z₅, z₆, hz₅.1, hz₅.2, hz₆.1, hz₆.2⟩

theorem stationary_iff_balance (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    deriv (unitWorkPotential N B) z = 0 ↔ completeForce N B z = 1 := by
  rw [(unitWorkPotential_hasDerivAt N B hz).deriv]
  exact sub_eq_zero

/-- This excludes joint uniqueness for the unit-work comparison itself.
An endpoint/content law has to be identified before it can select a window. -/
theorem no_joint_unique_balance (N : ℕ) :
    ¬ ∃! x : ℝ × ℝ, 0 < x.1 ∧ 0 < x.2 ∧ completeForce N x.1 x.2 = 1 := by
  rintro ⟨x, hx, huniq⟩
  obtain ⟨z₅, z₆, hz₅, he₅, hz₆, he₆⟩ := distinct_windows_admit_balance N
  have h₅ := huniq (5, z₅) ⟨by norm_num, hz₅, he₅⟩
  have h₆ := huniq (6, z₆) ⟨by norm_num, hz₆, he₆⟩
  have heq := congrArg Prod.fst (h₅.trans h₆.symm)
  norm_num at heq

structure Conclusions : Prop where
  actual_partition_vertex : ∀ N i u,
    vertexRatio N i u = Real.exp (-kineticPrecision N i u / 2) * kineticFraction N i u
  exact_saturation_remainder : ∀ N B z, 0 ≤ z →
    capacity N B - completeForce N B z =
      ∑ i ∈ support N B, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
        vertexRatio N i u / (1 + z * vertexRatio N i u)
  actual_amplitude_variation : ∀ N B z, 0 ≤ z →
    HasDerivAt (comparison N B) (completeForce N B z) z
  exact_saturation_budget : ∀ N B z, 0 < z →
    capacity N B - completeForce N B z ≤ frequencyVolume N B / z
  all_amplitude_roots : ∀ N B, 0 < B →
    ((∃! z : ℝ, 0 < z ∧ completeForce N B z = 1) ↔ 1 < capacity N B)
  all_large_windows : ∀ N B, 5 ≤ B →
    ∃! z : ℝ, 0 < z ∧ completeForce N B z = 1
  joint_uniqueness_test : ∀ N,
    ¬ ∃! x : ℝ × ℝ, 0 < x.1 ∧ 0 < x.2 ∧ completeForce N x.1 x.2 = 1
  distinct_feasible_windows : ∀ N,
    ∃ z₅ z₆ : ℝ, 0 < z₅ ∧ completeForce N 5 z₅ = 1 ∧
      0 < z₆ ∧ completeForce N 6 z₆ = 1

theorem generated : Conclusions where
  actual_partition_vertex := HistoryHaarSectionGaussianVariation.vertexRatio_eq
  exact_saturation_remainder := fun N B _ hz => capacity_sub_force_eq N B hz
  actual_amplitude_variation := fun N B _ hz => comparison_hasDerivAt N B hz
  exact_saturation_budget := fun N B _ hz => capacity_sub_force_le N B hz
  all_amplitude_roots := fun N _ hB => existsUnique_balance_iff N hB
  all_large_windows := fun N _ hB => existsUnique_balance_above_five N hB
  joint_uniqueness_test := no_joint_unique_balance
  distinct_feasible_windows := distinct_windows_admit_balance

end GeneratedFoundations.Arithmetic.HistoryHaarSectionCommonBalance
