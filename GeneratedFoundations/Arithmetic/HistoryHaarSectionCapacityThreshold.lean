module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionEquilibrium

/-!
# Retained spectral capacity and the source-unit window threshold

The available response is calculated from every original joint spectral
row, with its original Gaussian weight and frequency interval. It is the
exact saturation value of the comparison force. Thus window selection can
be tested on the retained spectrum before solving the response equation.

The affine source unit is the comparison protocol specified in
`HistoryHaarSectionSourceBalance`. This module classifies its complete
real-window feasibility family. No least-admissible-integer selection rule
is used to choose a generated endpoint.

The same original spectrum also determines a unique real capacity crossing
strictly between four and five. Its field and scalar position counts are
calculated from the joint spectral cell, and its natural ceiling is five.
Keeping one position in each sector alone allows all integer levels from
five through eight. Neither the crossing ceiling nor this content cell
selects a unique generated endpoint.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionCapacityThreshold

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionSourceBalance HistoryHaarSectionEquilibrium
open HistoryHaarSectionJointHessian (Index)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def branchCapacity (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
    weight N i u * kineticFraction N i u

def capacity (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i ∈ support N B, branchCapacity N B i

theorem remainder_fraction_bounds {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : 0 ≤ z) : 0 ≤ r / (1 + z * r) ∧ r / (1 + z * r) ≤ 1 / (1 + z) := by
  have hd : 0 < 1 + z * r := by positivity
  have he : 0 < 1 + z := by positivity
  exact ⟨div_nonneg hr hd.le, (div_le_div_iff₀ hd he).mpr (by nlinarith)⟩

theorem branchCapacity_nonneg (N : ℕ) (B : ℝ) (i : Index N) :
    0 ≤ branchCapacity N B i :=
  intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
    (fun u => mul_nonneg (weight_pos N i u).le (kineticFraction_nonneg N i u))

theorem capacity_nonneg (N : ℕ) (B : ℝ) : 0 ≤ capacity N B :=
  Finset.sum_nonneg (fun i _ => branchCapacity_nonneg N B i)

theorem branchCapacity_mono (N : ℕ) (i : Index N) :
    Monotone (fun B => branchCapacity N B i) := by
  intro B C hBC
  apply intervalIntegral.integral_mono_interval le_rfl (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (sub_le_sub_right hBC _))
  · exact Filter.Eventually.of_forall (fun u => mul_nonneg
      (weight_pos N i u).le (kineticFraction_nonneg N i u))
  · exact ((weight_continuous N i).mul
      (kineticFraction_continuous N i)).intervalIntegrable _ _

/-- Both the growing original frequency intervals and the newly retained
spectral labels contribute; births are included in the monotonicity proof. -/
theorem capacity_mono (N : ℕ) : Monotone (capacity N) := by
  intro B C hBC
  calc
    capacity N B ≤ ∑ i ∈ support N B, branchCapacity N C i :=
      Finset.sum_le_sum (fun i _ => branchCapacity_mono N i hBC)
    _ ≤ capacity N C := Finset.sum_le_sum_of_subset_of_nonneg
      (support_mono N hBC) (fun i _ _ => branchCapacity_nonneg N C i)

theorem branchCapacity_eq_zero (N : ℕ) (B : ℝ) (i : Index N)
    (hi : B ≤ kinetic N i) : branchCapacity N B i = 0 := by
  simp only [branchCapacity, Real.sqrt_eq_zero'.mpr (sub_nonpos.mpr hi),
    intervalIntegral.integral_same]

/-- A larger finite support contains every original row needed in a
neighborhood; inactive rows contribute exactly zero, including at birth. -/
theorem capacity_eq_larger_sum (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    capacity N B = ∑ i ∈ support N C, branchCapacity N B i := by
  apply Finset.sum_subset (support_mono N hBC)
  intro i _ hi
  exact branchCapacity_eq_zero N B i
    (le_of_not_gt (fun h => hi ((mem_support N B i).mpr h)))

theorem branchCapacity_continuous (N : ℕ) (i : Index N) :
    Continuous (fun B => branchCapacity N B i) :=
  (intervalIntegral.differentiable_integral_of_continuous
    ((weight_continuous N i).mul (kineticFraction_continuous N i))).continuous.comp
      (Real.continuous_sqrt.comp (continuous_id.sub continuous_const))

theorem capacity_continuous (N : ℕ) : Continuous (capacity N) := by
  apply continuous_iff_continuousAt.mpr
  intro B
  have h := (continuous_finsetSum (support N (B + 1))
    (fun i _ => branchCapacity_continuous N i)).continuousAt (x := B)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Iio.mem_nhds (show B < B + 1 by linarith)] with C hC
  exact capacity_eq_larger_sum N hC.le

theorem branchCapacity_strictMonoOn (N : ℕ) (i : Index N) :
    StrictMonoOn (fun B => branchCapacity N B i) (Ici (kinetic N i)) := by
  intro B hB C _ hBC
  have hc := (weight_continuous N i).mul (kineticFraction_continuous N i)
  have hs : Real.sqrt (B - kinetic N i) < Real.sqrt (C - kinetic N i) :=
    Real.sqrt_lt_sqrt (sub_nonneg.mpr hB) (sub_lt_sub_right hBC _)
  have hp : 0 < ∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
      weight N i u * kineticFraction N i u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on
      (hc.intervalIntegrable _ _) (fun u hu => ?_) hs
    have hu0 : 0 < u := lt_of_le_of_lt (Real.sqrt_nonneg _) hu.1
    exact mul_pos (weight_pos N i u) (div_pos
      (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu0) (kinetic_nonneg N i))
      (precision_pos N i u))
  have ha : (∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
        weight N i u * kineticFraction N i u) +
      (∫ u in Real.sqrt (B - kinetic N i)..Real.sqrt (C - kinetic N i),
        weight N i u * kineticFraction N i u) =
      ∫ u in (0 : ℝ)..Real.sqrt (C - kinetic N i),
        weight N i u * kineticFraction N i u :=
    intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable 0 (Real.sqrt (B - kinetic N i)))
      (hc.intervalIntegrable (Real.sqrt (B - kinetic N i)) (Real.sqrt (C - kinetic N i)))
  dsimp [branchCapacity]
  linarith

theorem capacity_strictMonoOn (N : ℕ) : StrictMonoOn (capacity N) (Ici 0) := by
  intro B hB C hC hBC
  change 0 ≤ B at hB
  change 0 ≤ C at hC
  let i := positionIndex N 0 (HistoryHaarSectionExhaustion.basePositionLabel N 0)
  have hi0 : kinetic N i = 0 := by
    change Geometry.SourceScalarKineticForm.position 0 = 0
    norm_num [Geometry.SourceScalarKineticForm.position_eq]
  have hi : i ∈ support N C := (mem_support N C i).mpr (by rw [hi0]; linarith [hB])
  rw [capacity_eq_larger_sum N hBC.le]
  exact Finset.sum_lt_sum (fun j _ => branchCapacity_mono N j hBC.le)
    ⟨i, hi, branchCapacity_strictMonoOn N i
      (by simpa only [mem_Ici, hi0] using hB)
      (by simpa only [mem_Ici, hi0] using hC) hBC⟩

theorem capacity_le_mass (N : ℕ) (B : ℝ) :
    capacity N B ≤ HistoryHaarSectionProbability.mass N B := by
  apply Finset.sum_le_sum
  intro i _
  apply intervalIntegral.integral_mono (Real.sqrt_nonneg _)
    (((weight_continuous N i).mul (kineticFraction_continuous N i)).intervalIntegrable _ _)
    ((weight_continuous N i).intervalIntegrable _ _)
  intro u
  exact (mul_le_mul_of_nonneg_left (kineticFraction_le_one N i u)
    (weight_pos N i u).le).trans_eq (mul_one _)

theorem branch_remainder_eq (N : ℕ) (B : ℝ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    branchCapacity N B i - branchForce N B i z =
      ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
        weight N i u * (kineticFraction N i u / (1 + z * kineticFraction N i u)) := by
  have hi : IntervalIntegrable (fun u => weight N i u * kineticFraction N i u)
      volume 0 (Real.sqrt (B - kinetic N i)) :=
    ((weight_continuous N i).mul (kineticFraction_continuous N i)).intervalIntegrable _ _
  rw [branchCapacity, branchForce, forceIntegral, ← intervalIntegral.integral_sub
    hi ((force_continuous N i hz).intervalIntegrable _ _)]
  apply intervalIntegral.integral_congr
  intro u _
  simp only [force]
  ring

theorem branch_remainder_bounds (N : ℕ) (B : ℝ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ branchCapacity N B i - branchForce N B i z ∧
      branchCapacity N B i - branchForce N B i z ≤
        HistoryHaarSectionProbability.branchMass N B i / (1 + z) := by
  rw [branch_remainder_eq N B i hz]
  have hd (u : ℝ) : 1 + z * kineticFraction N i u ≠ 0 :=
    ne_of_gt (by nlinarith [kineticFraction_nonneg N i u])
  have hc := (weight_continuous N i).mul
    ((kineticFraction_continuous N i).div
      (continuous_const.add (continuous_const.mul (kineticFraction_continuous N i))) hd)
  constructor
  · exact intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
      (fun u => mul_nonneg (weight_pos N i u).le
        (remainder_fraction_bounds (kineticFraction_nonneg N i u)
          (kineticFraction_le_one N i u) hz).1)
  · rw [HistoryHaarSectionProbability.branchMass, ← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono (Real.sqrt_nonneg _)
      (hc.intervalIntegrable _ _) (((weight_continuous N i).div_const _).intervalIntegrable _ _)
    intro u
    change weight N i u * (kineticFraction N i u / (1 + z * kineticFraction N i u)) ≤
      weight N i u / (1 + z)
    calc
      _ ≤ weight N i u * (1 / (1 + z)) := mul_le_mul_of_nonneg_left
        (remainder_fraction_bounds (kineticFraction_nonneg N i u)
          (kineticFraction_le_one N i u) hz).2 (weight_pos N i u).le
      _ = _ := by ring

/-- The error retains all rows. Only its exact positive remainder is bounded. -/
theorem saturation_budget (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ capacity N B - completeForce N B z ∧
      capacity N B - completeForce N B z ≤ HistoryHaarSectionProbability.mass N B / (1 + z) := by
  rw [capacity, completeForce, ← Finset.sum_sub_distrib]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (branch_remainder_bounds N B i hz).1)
  · rw [HistoryHaarSectionProbability.mass, Finset.sum_div]
    exact Finset.sum_le_sum (fun i _ => (branch_remainder_bounds N B i hz).2)

theorem force_lt_capacity (N : ℕ) {B z : ℝ} (hB : 0 < B) (hz : 0 ≤ z) :
    completeForce N B z < capacity N B :=
  lt_of_lt_of_le (completeForce_strictMonoOn N hB hz
    (show 0 ≤ z + 1 by linarith) (by linarith))
    (sub_nonneg.mp (saturation_budget N B (show 0 ≤ z + 1 by linarith)).1)

theorem capacity_le_of_force_le (N : ℕ) (B C : ℝ)
    (h : ∀ z : ℝ, 0 ≤ z → completeForce N B z ≤ C) : capacity N B ≤ C := by
  by_contra hn
  let gap := capacity N B - C
  have hg : 0 < gap := by dsimp [gap]; linarith
  let z := HistoryHaarSectionProbability.mass N B / gap
  have hz : 0 ≤ z := div_nonneg (HistoryHaarSectionProbability.mass_nonneg N B) hg.le
  have hzg : z * gap = HistoryHaarSectionProbability.mass N B := by
    dsimp [z]
    exact div_mul_cancel₀ _ hg.ne'
  have herr : HistoryHaarSectionProbability.mass N B / (1 + z) < gap := by
    apply (div_lt_iff₀ (show 0 < 1 + z by linarith)).mpr
    nlinarith
  have hb := (saturation_budget N B hz).2
  have hf := h z hz
  dsimp [gap] at herr
  linarith

/-- The bound comes from the actual scalar ground row and its generated
restoring Casimir. No field shell is retained at bandwidth four. -/
theorem capacity_four_le (N : ℕ) :
    capacity N 4 ≤ (8 / 15 : ℝ) * Real.sqrt Real.pi :=
  capacity_le_of_force_le N 4 _ (fun _ hz => completeForce_four_le N hz)

theorem capacity_four_lt_one (N : ℕ) : capacity N 4 < 1 := by
  have hroot : Real.sqrt Real.pi < (9 / 5 : ℝ) := by
    have hs := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
  linarith [capacity_four_le N]

/-- The first complete field shell, with its six polarizations times the
square of the actual history dimension, crosses the source-unit budget. -/
theorem capacity_five_gt_one (N : ℕ) : 1 < capacity N 5 :=
  lt_trans (completeForce_five_seven_gt_one N)
    (force_lt_capacity N (B := 5) (z := 7) (by norm_num) (by norm_num))

/-- This crossing is obtained from the complete original spectral mass,
not from an assumed response root or a supplied position count. -/
theorem existsUnique_capacity_crossing (N : ℕ) :
    ∃! B : ℝ, 0 ≤ B ∧ capacity N B = 1 := by
  obtain ⟨B, hB, he⟩ := intermediate_value_Icc (by norm_num : (4 : ℝ) ≤ 5)
    (capacity_continuous N).continuousOn
    (show (1 : ℝ) ∈ Icc (capacity N 4) (capacity N 5) from
      ⟨(capacity_four_lt_one N).le, (capacity_five_gt_one N).le⟩)
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB.1
  refine ⟨B, ⟨hB0, he⟩, fun C hC => ?_⟩
  exact (capacity_strictMonoOn N).injOn hC.1 hB0 (hC.2.trans he.symm)

def criticalBandwidth (N : ℕ) : ℝ :=
  Classical.choose (existsUnique_capacity_crossing N).exists

theorem criticalBandwidth_spec (N : ℕ) :
    0 ≤ criticalBandwidth N ∧ capacity N (criticalBandwidth N) = 1 :=
  Classical.choose_spec (existsUnique_capacity_crossing N).exists

theorem criticalBandwidth_bounds (N : ℕ) :
    4 < criticalBandwidth N ∧ criticalBandwidth N < 5 := by
  have he := (criticalBandwidth_spec N).2
  constructor
  · by_contra hn
    have hm := capacity_mono N (le_of_not_gt hn)
    rw [he] at hm
    linarith [capacity_four_lt_one N]
  · by_contra hn
    have hm := capacity_mono N (le_of_not_gt hn)
    rw [he] at hm
    linarith [capacity_five_gt_one N]

theorem capacity_gt_one_iff (N : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    1 < capacity N B ↔ criticalBandwidth N < B := by
  have he := (criticalBandwidth_spec N).2
  constructor
  · intro h
    by_contra hn
    have hm := capacity_mono N (le_of_not_gt hn)
    rw [he] at hm
    linarith
  · intro h
    have hm := capacity_strictMonoOn N (criticalBandwidth_spec N).1 hB h
    simpa only [he] using hm

/-- The crossing and its smallest integer resolution occupy the same
calculated joint cell. Every original multiplicity remains in the trace. -/
theorem criticalBandwidth_joint_content (N : ℕ) :
    HistoryHaarSectionRetention.fieldPositionCount (criticalBandwidth N) = 1 ∧
      HistoryHaarSectionContent.positionCount (criticalBandwidth N) = 1 :=
  (HistoryHaarSectionRetention.first_joint_cell _).mpr
    ⟨(criticalBandwidth_bounds N).1, by linarith [(criticalBandwidth_bounds N).2]⟩

theorem criticalBandwidth_ceil (N : ℕ) : Nat.ceil (criticalBandwidth N) = 5 := by
  apply Nat.le_antisymm
  · exact Nat.ceil_le.mpr (criticalBandwidth_bounds N).2.le
  · have h : (4 : ℕ) < Nat.ceil (criticalBandwidth N) :=
      Nat.lt_ceil.mpr (criticalBandwidth_bounds N).1
    exact Nat.succ_le_of_lt h

/-- Feasibility is decided by the original spectral capacity, not by an
assumed root of the response equation. This holds at every positive real window. -/
theorem positive_balance_iff_capacity (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (∃! z : ℝ, 0 < z ∧ completeForce N B z = 1) ↔ 1 < capacity N B := by
  constructor
  · rintro ⟨z, ⟨hz, he⟩, _⟩
    simpa only [he] using force_lt_capacity N hB hz.le
  · intro hcap
    let gap := capacity N B - 1
    have hg : 0 < gap := by dsimp [gap]; linarith
    let z := HistoryHaarSectionProbability.mass N B / gap
    have hz : 0 < z := div_pos (HistoryHaarSectionProbability.mass_pos_of_pos N hB) hg
    have hzg : z * gap = HistoryHaarSectionProbability.mass N B := by
      dsimp [z]
      exact div_mul_cancel₀ _ hg.ne'
    have herr : HistoryHaarSectionProbability.mass N B / (1 + z) < gap := by
      apply (div_lt_iff₀ (show 0 < 1 + z by linarith)).mpr
      nlinarith
    have hforce : 1 < completeForce N B z := by
      have hb := (saturation_budget N B hz.le).2
      dsimp [gap] at herr
      linarith
    have hc := (completeForce_continuousOn N B).mono
      (show Icc (0 : ℝ) z ⊆ Ici 0 from fun _ h => h.1)
    obtain ⟨v, hv, he⟩ := intermediate_value_Icc hz.le hc
      (show (1 : ℝ) ∈ Icc (completeForce N B 0) (completeForce N B z) by
        rw [completeForce_zero]; exact ⟨by norm_num, hforce.le⟩)
    have hv0 : 0 < v := by
      by_contra hn
      have hvz : v = 0 := le_antisymm (le_of_not_gt hn) hv.1
      subst v
      norm_num at he
    refine ⟨v, ⟨hv0, he⟩, fun u hu => ?_⟩
    exact (completeForce_strictMonoOn N hB).injOn hu.1.le hv0.le (hu.2.trans he.symm)

theorem no_minimum_of_capacity_le_one (N : ℕ) {B : ℝ} (hB : 0 < B)
    (hcap : capacity N B ≤ 1) :
    ¬ ∃ z : ℝ, 0 ≤ z ∧ ∀ v : ℝ, 0 ≤ v → sourcePotential N B z ≤ sourcePotential N B v := by
  have hanti : StrictAntiOn (sourcePotential N B) (Ici 0) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici (0 : ℝ))
    · intro z hz
      change 0 ≤ z at hz
      exact (sourcePotential_hasDerivAt N B (by linarith : -(1 / 2 : ℝ) < z)).continuousAt.continuousWithinAt
    · intro z hz
      have hz0 : 0 ≤ z := interior_subset hz
      rw [(sourcePotential_hasDerivAt N B (by linarith : -(1 / 2 : ℝ) < z)).deriv]
      have := force_lt_capacity N hB hz0
      linarith
  rintro ⟨z, hz, hmin⟩
  exact not_lt_of_ge (hmin (z + 1) (by linarith))
    (hanti hz (show 0 ≤ z + 1 by linarith) (by linarith))

theorem real_window_minimum_iff (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (∃ z : ℝ, 0 ≤ z ∧ ∀ v : ℝ, 0 ≤ v → sourcePotential N B z ≤ sourcePotential N B v) ↔
      1 < capacity N B := by
  constructor
  · intro h
    by_contra hn
    exact no_minimum_of_capacity_le_one N hB (le_of_not_gt hn) h
  · intro h
    obtain ⟨z, hz, _⟩ := (positive_balance_iff_capacity N hB).mpr h
    exact ⟨z, hz.1.le, fun v hv => (global_minimum_of_balance N hB hz.1.le hz.2 v hv).1⟩

theorem real_window_balance_iff_critical (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (∃! z : ℝ, 0 < z ∧ completeForce N B z = 1) ↔ criticalBandwidth N < B := by
  rw [positive_balance_iff_capacity N hB, capacity_gt_one_iff N hB.le]

theorem real_window_minimum_iff_critical (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (∃ z : ℝ, 0 ≤ z ∧ ∀ v : ℝ, 0 ≤ v → sourcePotential N B z ≤ sourcePotential N B v) ↔
      criticalBandwidth N < B := by
  rw [real_window_minimum_iff N hB, capacity_gt_one_iff N hB.le]

theorem integer_capacity_iff (N R : ℕ) (hR : 0 < R) :
    1 < capacity N R ↔ 5 ≤ R := by
  rw [← real_window_minimum_iff N (by exact_mod_cast hR)]
  exact hasMinimum_iff N R

/-- Same content is a plateau, not a unique integer selector. The complete
classification prevents confusing the least admissible window with the
only window admitting a response equilibrium. -/
theorem first_cell_feasible_integers (N R : ℕ) :
    ((HistoryHaarSectionRetention.fieldPositionCount (R : ℝ) = 1 ∧
        HistoryHaarSectionContent.positionCount (R : ℝ) = 1) ∧ 1 < capacity N R) ↔
      5 ≤ R ∧ R ≤ 8 := by
  rw [HistoryHaarSectionRetention.first_joint_cell]
  constructor
  · rintro ⟨⟨hl, hu⟩, _⟩
    have hl' : 4 < R := by exact_mod_cast hl
    have hu' : R ≤ 8 := by exact_mod_cast hu
    omega
  · rintro ⟨hl, hu⟩
    have hR : 0 < R := by omega
    refine ⟨⟨?_, ?_⟩, (integer_capacity_iff N R hR).mpr hl⟩
    · exact_mod_cast (show 4 < R by omega)
    · exact_mod_cast hu

structure Conclusions : Prop where
  original_spectral_budget : ∀ N B z, 0 ≤ z →
    0 ≤ capacity N B - completeForce N B z ∧
      capacity N B - completeForce N B z ≤ HistoryHaarSectionProbability.mass N B / (1 + z)
  actual_capacity_bound : ∀ N B, 0 ≤ capacity N B ∧
    capacity N B ≤ HistoryHaarSectionProbability.mass N B
  original_support_monotonicity : ∀ N, Monotone (capacity N)
  calculated_shell_crossing : ∀ N, capacity N 4 < 1 ∧ 1 < capacity N 5
  real_window_balance : ∀ N B, 0 < B →
    ((∃! z : ℝ, 0 < z ∧ completeForce N B z = 1) ↔ 1 < capacity N B)
  real_window_variational_criterion : ∀ N B, 0 < B →
    ((∃ z : ℝ, 0 ≤ z ∧ ∀ v : ℝ, 0 ≤ v → sourcePotential N B z ≤ sourcePotential N B v) ↔
      1 < capacity N B)
  calculated_integer_threshold : ∀ (N R : ℕ), 0 < R → (1 < capacity N R ↔ 5 ≤ R)
  calculated_real_crossing : ∀ N,
    4 < criticalBandwidth N ∧ criticalBandwidth N < 5 ∧
      capacity N (criticalBandwidth N) = 1 ∧ Nat.ceil (criticalBandwidth N) = 5
  calculated_crossing_content : ∀ N,
    HistoryHaarSectionRetention.fieldPositionCount (criticalBandwidth N) = 1 ∧
      HistoryHaarSectionContent.positionCount (criticalBandwidth N) = 1
  complete_first_cell_classification : ∀ (N R : ℕ),
    (((HistoryHaarSectionRetention.fieldPositionCount (R : ℝ) = 1 ∧
      HistoryHaarSectionContent.positionCount (R : ℝ) = 1) ∧ 1 < capacity N R) ↔
        5 ≤ R ∧ R ≤ 8)

theorem generated : Conclusions where
  original_spectral_budget := fun N B _ hz => saturation_budget N B hz
  actual_capacity_bound := fun N B => ⟨capacity_nonneg N B, capacity_le_mass N B⟩
  original_support_monotonicity := capacity_mono
  calculated_shell_crossing := fun N => ⟨capacity_four_lt_one N, capacity_five_gt_one N⟩
  real_window_balance := fun N _ hB => positive_balance_iff_capacity N hB
  real_window_variational_criterion := fun N _ hB => real_window_minimum_iff N hB
  calculated_integer_threshold := integer_capacity_iff
  calculated_real_crossing := fun N => ⟨(criticalBandwidth_bounds N).1,
    (criticalBandwidth_bounds N).2, (criticalBandwidth_spec N).2, criticalBandwidth_ceil N⟩
  calculated_crossing_content := criticalBandwidth_joint_content
  complete_first_cell_classification := first_cell_feasible_integers

end GeneratedFoundations.Arithmetic.HistoryHaarSectionCapacityThreshold
