module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionRestoration
public import GeneratedFoundations.Arithmetic.HistoryHaarSectionBoundary

/-!
# Window variation of the complete Gaussian comparison

Amplitude variation and window variation act on the same original spectral
integral. The former has a unique positive equilibrium above the calculated
capacity crossing. The latter increases the comparison at every positive
amplitude. The exact boundary derivative retains the logarithm, all original
labels and the Gaussian factor at the moving edge.

Consequently, balancing the amplitude does not make the window stationary.
The balanced amplitude decreases when the window grows, and the minimized
comparison value increases. These are properties of the existing precision
comparison, before any additional endpoint-content coupling is identified.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionWindowVariation

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionSourceBalance HistoryHaarSectionEquilibrium
open HistoryHaarSectionJointHessian (Index)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

theorem branchComparison_nonneg (N : ℕ) (B : ℝ) (i : Index N)
    {z : ℝ} (hz : 0 ≤ z) : 0 ≤ branchComparison N B i z :=
  intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
    (fun u => mul_nonneg (weight_pos N i u).le
      (cost_nonneg _ _ (relative_precision_pos N i u hz)))

theorem branchComparison_eq_zero (N : ℕ) (B : ℝ) (i : Index N)
    (hi : B ≤ kinetic N i) (z : ℝ) : branchComparison N B i z = 0 := by
  simp only [branchComparison, comparisonIntegral,
    Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hi), intervalIntegral.integral_same]

theorem comparison_eq_larger_sum (N : ℕ) {B C : ℝ} (hBC : B ≤ C) (z : ℝ) :
    comparison N B z = ∑ i ∈ support N C, branchComparison N B i z := by
  apply Finset.sum_subset (support_mono N hBC)
  intro i _ hi
  exact branchComparison_eq_zero N B i
    (le_of_not_gt (fun h => hi ((mem_support N B i).mpr h))) z

/-- The complete support includes births; their earlier integrals are zero. -/
theorem comparison_continuous_window (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    Continuous (fun B => comparison N B z) := by
  apply continuous_iff_continuousAt.mpr
  intro B
  have hc (i : Index N) : Continuous (fun C => branchComparison N C i z) :=
    (intervalIntegral.differentiable_integral_of_continuous
      (comparison_integrand_continuous N i hz)).continuous.comp
        (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))
  have h := (continuous_finsetSum (support N (B + 1)) (fun i _ => hc i)).continuousAt
    (x := B)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact comparison_eq_larger_sum N hC.le z

theorem branchComparison_mono_window (N : ℕ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    Monotone (fun B => branchComparison N B i z) := by
  intro B C hBC
  apply intervalIntegral.integral_mono_interval le_rfl (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (sub_le_sub_right hBC _))
  · exact Filter.Eventually.of_forall (fun u => mul_nonneg (weight_pos N i u).le
      (cost_nonneg _ _ (relative_precision_pos N i u hz)))
  · exact (comparison_integrand_continuous N i hz).intervalIntegrable _ _

theorem branchComparison_strictMonoOn_window (N : ℕ) (i : Index N)
    {z : ℝ} (hz : 0 < z) :
    StrictMonoOn (fun B => branchComparison N B i z) (Ici (kinetic N i)) := by
  intro B hB C _ hBC
  have hs : Real.sqrt (B - kinetic N i) < Real.sqrt (C - kinetic N i) :=
    Real.sqrt_lt_sqrt (sub_nonneg.mpr hB) (sub_lt_sub_right hBC _)
  have hc := comparison_integrand_continuous N i hz.le
  have hp : 0 < ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      weight N i u * cost (kineticFraction N i u) z := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ hs
    intro u hu
    have hu0 := lt_of_le_of_lt (Real.sqrt_nonneg _) hu.1
    have hr : 0 < kineticFraction N i u := div_pos
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu0) (kinetic_nonneg N i))
      (precision_pos N i u)
    exact mul_pos (weight_pos N i u)
      (cost_pos (relative_precision_pos N i u hz.le) (mul_pos hz hr).ne')
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
    (hc.intervalIntegrable (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i)))
  dsimp [branchComparison, comparisonIntegral]
  linarith

theorem comparison_mono_window (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    Monotone (fun B => comparison N B z) := by
  intro B C hBC
  calc
    comparison N B z ≤ ∑ i ∈ support N B, branchComparison N C i z :=
      Finset.sum_le_sum (fun i _ => branchComparison_mono_window N i hz hBC)
    _ ≤ comparison N C z := Finset.sum_le_sum_of_subset_of_nonneg
      (support_mono N hBC) (fun i _ _ => branchComparison_nonneg N C i hz)

theorem comparison_strictMonoOn_window (N : ℕ) {z : ℝ} (hz : 0 < z) :
    StrictMonoOn (fun B => comparison N B z) (Ici 0) := by
  intro B hB C _ hBC
  change 0 ≤ B at hB
  let i := positionIndex N 0 (HistoryHaarSectionExhaustion.basePositionLabel N 0)
  have hi0 : kinetic N i = 0 := by
    change Geometry.SourceScalarKineticForm.position 0 = 0
    norm_num [Geometry.SourceScalarKineticForm.position_eq]
  have hi : i ∈ support N C := (mem_support N C i).mpr (by rw [hi0]; linarith)
  change comparison N B z < comparison N C z
  rw [comparison_eq_larger_sum N hBC.le z]
  exact Finset.sum_lt_sum (fun j _ => branchComparison_mono_window N j hz.le hBC.le)
    ⟨i, hi, branchComparison_strictMonoOn_window N i hz
      (by simpa only [mem_Ici, hi0] using hB)
      (by simp only [mem_Ici, hi0]; linarith) hBC⟩

theorem sourcePotential_strictMonoOn_window (N : ℕ) {z : ℝ} (hz : 0 < z) :
    StrictMonoOn (fun B => sourcePotential N B z) (Ici 0) := by
  intro B hB C hC hBC
  exact sub_lt_sub_right (comparison_strictMonoOn_window N hz hB hC hBC) _

theorem branchForce_strictMonoOn_window (N : ℕ) (i : Index N)
    {z : ℝ} (hz : 0 < z) :
    StrictMonoOn (fun B => branchForce N B i z) (Ici (kinetic N i)) := by
  intro B hB C _ hBC
  have hs : Real.sqrt (B - kinetic N i) < Real.sqrt (C - kinetic N i) :=
    Real.sqrt_lt_sqrt (sub_nonneg.mpr hB) (sub_lt_sub_right hBC _)
  have hc := force_continuous N i hz.le
  have hp : 0 < ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      weight N i u * force (kineticFraction N i u) z := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ hs
    intro u hu
    have hu0 := lt_of_le_of_lt (Real.sqrt_nonneg _) hu.1
    have hr : 0 < kineticFraction N i u := div_pos
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu0) (kinetic_nonneg N i))
      (precision_pos N i u)
    have hf := force_strictMonoOn_nonneg hr (show (0 : ℝ) ∈ Ici 0 by norm_num) hz.le hz
    exact mul_pos (weight_pos N i u) (by simpa [force] using hf)
  have ha := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
    (hc.intervalIntegrable (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i)))
  dsimp [branchForce, forceIntegral]
  linarith

theorem completeForce_strictMonoOn_window (N : ℕ) {z : ℝ} (hz : 0 < z) :
    StrictMonoOn (fun B => completeForce N B z) (Ici 0) := by
  intro B hB C _ hBC
  change 0 ≤ B at hB
  let i := positionIndex N 0 (HistoryHaarSectionExhaustion.basePositionLabel N 0)
  have hi0 : kinetic N i = 0 := by
    change Geometry.SourceScalarKineticForm.position 0 = 0
    norm_num [Geometry.SourceScalarKineticForm.position_eq]
  have hi : i ∈ support N C := (mem_support N C i).mpr (by rw [hi0]; linarith)
  have he : completeForce N B z = ∑ j ∈ support N C, branchForce N B j z := by
    apply Finset.sum_subset (support_mono N hBC.le)
    intro j _ hj
    have hjB : B ≤ kinetic N j :=
      le_of_not_gt (fun h => hj ((mem_support N B j).mpr h))
    simp only [branchForce, forceIntegral,
      Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hjB),
      intervalIntegral.integral_same]
  change completeForce N B z < completeForce N C z
  rw [he]
  exact Finset.sum_lt_sum (fun j _ => branchForce_mono_window N j hz.le hBC.le)
    ⟨i, hi, branchForce_strictMonoOn_window N i hz
      (by simpa only [mem_Ici, hi0] using hB)
      (by simp only [mem_Ici, hi0]; linarith) hBC⟩

/-- Two balanced windows use different amplitudes, even within one content cell. -/
theorem balanced_amplitudes_strictly_decrease (N : ℕ) {B C z v : ℝ}
    (hB : 0 < B) (hBC : B < C) (hz : 0 < z) (hv : 0 < v)
    (hez : completeForce N B z = 1) (hev : completeForce N C v = 1) : v < z := by
  have hwin : completeForce N B z < completeForce N C z :=
    completeForce_strictMonoOn_window N hz hB.le (by change 0 ≤ C; linarith) hBC
  rw [hez] at hwin
  by_contra hn
  have hle := (completeForce_strictMonoOn N (B := C) (by linarith)).monotoneOn
    hz.le hv.le (le_of_not_gt hn)
  rw [hev] at hle
  linarith

theorem balanced_minimum_values_strictly_increase (N : ℕ) {B C z v : ℝ}
    (hB : 0 < B) (hBC : B < C) (hz : 0 < z) (hv : 0 < v)
    (hez : completeForce N B z = 1) (_hev : completeForce N C v = 1) :
    sourcePotential N B z < sourcePotential N C v := by
  exact lt_of_le_of_lt (global_minimum_of_balance N hB hz.le hez v hv.le).1
    (sourcePotential_strictMonoOn_window N hv hB.le (by change 0 ≤ C; linarith) hBC)

theorem five_and_six_have_distinct_balances (N : ℕ) :
    ∃ v : ℝ, 0 < v ∧ completeForce N 6 v = 1 ∧ v < equilibrium N ∧
      sourcePotential N 5 (equilibrium N) < sourcePotential N 6 v := by
  obtain ⟨v, hv, _⟩ := existsUnique_balance_above_five N (B := 6) (by norm_num)
  exact ⟨v, hv.1, hv.2,
    balanced_amplitudes_strictly_decrease N (B := 5) (C := 6) (by norm_num)
      (by norm_num) (equilibrium_pos N) hv.1 (equilibrium_balance N) hv.2,
    balanced_minimum_values_strictly_increase N (B := 5) (C := 6) (by norm_num)
      (by norm_num) (equilibrium_pos N) hv.1 (equilibrium_balance N) hv.2⟩

theorem kineticFraction_at_edge (N : ℕ) (i : Index N) {B : ℝ}
    (hB : kinetic N i < B) :
    kineticFraction N i (Real.sqrt (B - kinetic N i)) = B / (B + restoring N i) := by
  unfold kineticFraction kineticPrecision precision
  rw [Real.sq_sqrt (sub_nonneg.mpr hB.le), source_response_decomposition]
  congr 1 <;> ring

def comparisonEdge (N : ℕ) (B z : ℝ) (i : Index N) : ℝ :=
  cost (B / (B + restoring N i)) z / (2 * Real.sqrt (B - kinetic N i))

def comparisonBoundary (N : ℕ) (B z : ℝ) : ℝ :=
  ∑ i ∈ support N B, comparisonEdge N B z i

def branchComparisonSlope (N : ℕ) (B z : ℝ) (i : Index N) : ℝ :=
  if kinetic N i < B then Real.exp (-B) * comparisonEdge N B z i else 0

theorem branchComparison_hasDerivAt_window (N : ℕ) (i : Index N) {B z : ℝ}
    (hregular : kinetic N i ≠ B) (hz : 0 ≤ z) :
    HasDerivAt (fun C => branchComparison N C i z) (branchComparisonSlope N B z i) B := by
  have hc := comparison_integrand_continuous N i hz
  by_cases h : kinetic N i < B
  · have hs := ((hasDerivAt_id B).sub_const (kinetic N i)).sqrt (sub_pos.mpr h).ne'
    have hi := intervalIntegral.integral_hasDerivAt_right
      (hc.intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
    convert! hi.comp B hs using 1
    simp only [branchComparisonSlope, ite_eq_left h, comparisonEdge,
      HistoryHaarSectionBoundary.weight_at_edge N i h, kineticFraction_at_edge N i h,
      id_eq, mul_one_div]
    ring
  · have hl : B < kinetic N i := lt_of_le_of_ne (le_of_not_gt h) hregular.symm
    simp only [branchComparisonSlope, ite_eq_right h]
    apply (hasDerivAt_const B (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.mem_nhds hl] with C hC
    exact branchComparison_eq_zero N C i hC.le z

theorem comparison_hasDerivAt_window (N : ℕ) {B z : ℝ}
    (hregular : ∀ i : Index N, kinetic N i ≠ B) (hz : 0 ≤ z) :
    HasDerivAt (fun C => comparison N C z)
      (Real.exp (-B) * comparisonBoundary N B z) B := by
  have hd := HasDerivAt.fun_sum (u := support N (B + 1))
    (fun i _ => branchComparison_hasDerivAt_window N i (hregular i) hz)
  have he : (∑ i ∈ support N (B + 1), branchComparisonSlope N B z i) =
      Real.exp (-B) * comparisonBoundary N B z := by
    have he' : (∑ i ∈ support N B, branchComparisonSlope N B z i) =
        ∑ i ∈ support N (B + 1), branchComparisonSlope N B z i := by
      apply Finset.sum_subset (support_mono N (show B ≤ B + 1 by linarith))
      intro i _ hi
      simp only [branchComparisonSlope,
        ite_eq_right (fun h => hi ((mem_support N B i).mpr h))]
    rw [← he', comparisonBoundary, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [branchComparisonSlope, ite_eq_left ((mem_support N B i).mp hi)]
  rw [he] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact comparison_eq_larger_sum N hC.le z

theorem comparisonBoundary_pos (N : ℕ) {B z : ℝ} (hB : 0 < B) (hz : 0 < z) :
    0 < comparisonBoundary N B z := by
  apply Finset.sum_pos _ (HistoryHaarSectionProbability.support_nonempty_of_pos N hB)
  intro i hi
  have hr := div_pos hB (add_pos_of_pos_of_nonneg hB (restoring_nonneg N i))
  apply div_pos (cost_pos (by nlinarith [mul_pos hz hr]) (mul_pos hz hr).ne')
  exact mul_pos (by norm_num)
    (Real.sqrt_pos.mpr (sub_pos.mpr ((mem_support N B i).mp hi)))

theorem sourcePotential_hasDerivAt_window (N : ℕ) {B z : ℝ}
    (hregular : ∀ i : Index N, kinetic N i ≠ B) (hz : 0 ≤ z) :
    HasDerivAt (fun C => sourcePotential N C z)
      (Real.exp (-B) * comparisonBoundary N B z) B :=
  (comparison_hasDerivAt_window N hregular hz).sub_const _

/-- An amplitude equilibrium is not a joint amplitude/window stationary point. -/
theorem balanced_window_derivative_pos (N : ℕ) {B z : ℝ} (hB : 0 < B)
    (hregular : ∀ i : Index N, kinetic N i ≠ B) (hz : 0 ≤ z)
    (he : completeForce N B z = 1) :
    0 < deriv (fun C => sourcePotential N C z) B := by
  have hz0 : 0 < z := by
    rcases eq_or_lt_of_le hz with h | h
    · rw [← h, completeForce_zero] at he
      norm_num at he
    · exact h
  rw [(sourcePotential_hasDerivAt_window N hregular hz).deriv]
  exact mul_pos (Real.exp_pos _) (comparisonBoundary_pos N hB hz0)

theorem first_joint_cell_regular (N : ℕ) {B : ℝ} (hlo : 4 < B) (hhi : B < 8) :
    ∀ i : Index N, kinetic N i ≠ B := by
  intro i hi
  have hmem : i ∈ support N 8 := (mem_support N 8 i).mpr (by rwa [hi])
  have hshape := (mem_support_first_plateau N (B := 8) (by norm_num) le_rfl i).mp hmem
  cases i with
  | inl a =>
    change kinetic N (.inl a) = 4 at hshape
    linarith
  | inr a =>
    change a.2.val.1 = 0 at hshape
    have hz : kinetic N (.inr a) = 0 := by
      change Geometry.SourceCasimirClosure.energy a.2.val.1 = 0
      rw [hshape]
      norm_num [Geometry.SourceCasimirClosure.energy]
    linarith

theorem equilibrium_five_window_derivative_pos (N : ℕ) :
    0 < deriv (fun B => sourcePotential N B (equilibrium N)) 5 :=
  balanced_window_derivative_pos N (by norm_num)
    (first_joint_cell_regular N (by norm_num) (by norm_num))
    (equilibrium_pos N).le (equilibrium_balance N)

structure Conclusions : Prop where
  continuous_original_window : ∀ N z, 0 ≤ z → Continuous (fun B => comparison N B z)
  strict_window_force : ∀ N z, 0 < z →
    StrictMonoOn (fun B => completeForce N B z) (Ici 0)
  strict_window_potential : ∀ N z, 0 < z →
    StrictMonoOn (fun B => sourcePotential N B z) (Ici 0)
  ordered_actual_equilibria : ∀ N B C z v, 0 < B → B < C → 0 < z → 0 < v →
    completeForce N B z = 1 → completeForce N C v = 1 → v < z
  exact_original_boundary : ∀ N B z, (∀ i : Index N, kinetic N i ≠ B) → 0 ≤ z →
    HasDerivAt (fun C => sourcePotential N C z)
      (Real.exp (-B) * comparisonBoundary N B z) B
  amplitude_balance_does_not_stationarize_window : ∀ N B z, 0 < B →
    (∀ i : Index N, kinetic N i ≠ B) → 0 ≤ z → completeForce N B z = 1 →
    0 < deriv (fun C => sourcePotential N C z) B
  actual_selected_window_derivative : ∀ N,
    0 < deriv (fun B => sourcePotential N B (equilibrium N)) 5

theorem generated : Conclusions where
  continuous_original_window := fun N _ hz => comparison_continuous_window N hz
  strict_window_force := fun N _ hz => completeForce_strictMonoOn_window N hz
  strict_window_potential := fun N _ hz => sourcePotential_strictMonoOn_window N hz
  ordered_actual_equilibria := fun N _ _ _ _ hB hBC hz hv hez hev =>
    balanced_amplitudes_strictly_decrease N hB hBC hz hv hez hev
  exact_original_boundary := fun N _ _ hr hz => sourcePotential_hasDerivAt_window N hr hz
  amplitude_balance_does_not_stationarize_window := fun N _ _ hB hr hz he =>
    balanced_window_derivative_pos N hB hr hz he
  actual_selected_window_derivative := equilibrium_five_window_derivative_pos

end GeneratedFoundations.Arithmetic.HistoryHaarSectionWindowVariation
