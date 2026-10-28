module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionRetention
public import GeneratedFoundations.Operations.ScalarPrecisionPositive
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Source-unit balance on the complete Gaussian section window

The comparison uses the original differentiated joint spectrum and Gaussian
weights. Its affine term is one total generated source intensity, not one
copy per retained coefficient. This defines a source-unit comparison
protocol. The complete admissible integer family is calculated below;
feasibility does not select one member of that family.

The actual scalar ground row and the first complete connection shell give
opposite bounds at levels four and five, uniformly in the history stage.
The comparison amplitude, the spectral bandwidth and a coordinate scale
remain different variables.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionSourceBalance

open HistoryHaarSectionWindow HistoryHaarSectionContent HistoryHaarSectionShells
open HistoryHaarSectionComparison HistoryHaarSectionExhaustion
open HistoryHaarSectionJointHessian (Index)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

theorem force_nonneg_of_nonneg {r z : ℝ} (hr : 0 ≤ r) (hz : 0 ≤ z) :
    0 ≤ force r z := by
  have hp : 0 < 1 + z * r := by positivity
  rw [force, sub_nonneg, div_le_iff₀ hp]
  nlinarith [mul_nonneg hz (sq_nonneg r)]

theorem force_le_fraction {r z : ℝ} (hr : 0 ≤ r) (hz : 0 ≤ z) :
    force r z ≤ r := by
  unfold force
  have : 0 ≤ r / (1 + z * r) := div_nonneg hr (by positivity)
  linarith

theorem force_continuous (N : ℕ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    Continuous (fun u => weight N i u * force (kineticFraction N i u) z) := by
  apply (weight_continuous N i).mul
  exact (kineticFraction_continuous N i).sub
    ((kineticFraction_continuous N i).div
      (continuous_const.add (continuous_const.mul (kineticFraction_continuous N i)))
      (fun u => ne_of_gt (by nlinarith [kineticFraction_nonneg N i u])))

theorem branchForce_nonneg (N : ℕ) (B : ℝ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ branchForce N B i z :=
  intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
    (fun u => mul_nonneg (weight_pos N i u).le
      (force_nonneg_of_nonneg (kineticFraction_nonneg N i u) hz))

theorem completeForce_nonneg (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    0 ≤ completeForce N B z :=
  Finset.sum_nonneg (fun i _ => branchForce_nonneg N B i hz)

theorem branchComparison_positive_hasDerivAt (N : ℕ) (B : ℝ) (i : Index N)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    HasDerivAt (branchComparison N B i) (branchForce N B i z) z :=
  positive_comparisonIntegral_hasDerivAt _ _ _ _ (kineticFraction_continuous N i)
    (weight_continuous N i) (kineticFraction_nonneg N i) (kineticFraction_le_one N i)
    (fun u => (weight_pos N i u).le) (weight_le_one N i) hz

theorem comparison_positive_hasDerivAt (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    HasDerivAt (comparison N B) (completeForce N B z) z := by
  classical
  exact HasDerivAt.fun_sum (fun i _ => branchComparison_positive_hasDerivAt N B i hz)

/-- One total source unit is paired with the complete trace. This is a
specified comparison protocol using the already generated intensity. -/
def sourcePotential (N : ℕ) (B z : ℝ) : ℝ :=
  comparison N B z - HistoryGaussianCovariance.generatedIntensity N * z

theorem sourcePotential_hasDerivAt (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : -(1 / 2 : ℝ) < z) :
    HasDerivAt (sourcePotential N B) (completeForce N B z - 1) z := by
  convert! (comparison_positive_hasDerivAt N B hz).sub ((hasDerivAt_id z).const_mul
      (HistoryGaussianCovariance.generatedIntensity N)) using 1
  rw [HistoryGaussianCovariance.generatedIntensity_eq]
  norm_num

theorem field_fraction_eq_one (N : ℕ) (a : HistoryHaarClosedHessian.BasisIndex N)
    (u : ℝ) : kineticFraction N (.inl a) u = 1 := by
  unfold kineticFraction kineticPrecision precision kinetic
  change (u ^ 2 + Geometry.SourceOneFormHodgeLaplacian.hodgeEigenvalue a.2) /
    (u ^ 2 + Geometry.SourceOneFormHodgeLaplacian.hodgeEigenvalue a.2) = 1
  exact div_self (ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg u)
    (HistoryHaarClosedHessian.eigenvalue_pos N a)))

theorem branchForce_field (N : ℕ) (B : ℝ)
    (a : HistoryHaarClosedHessian.BasisIndex N) (z : ℝ) :
    branchForce N B (.inl a) z = force 1 z * branchIntegral N B (.inl a) := by
  rw [branchIntegral_field]
  simp only [branchForce, forceIntegral, field_fraction_eq_one, fieldIntegral]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u _
  change _ * _ = _ * _
  simp only [weight, kineticPrecision, kinetic, HistoryHaarClosedHessian.eigenvalue,
    Sum.elim_inl, mul_comm]

theorem field_force_le_complete (N : ℕ) (B : ℝ) {z : ℝ} (hz : 0 ≤ z) :
    force 1 z * fieldResponse N B ≤ completeForce N B z := by
  classical
  rw [fieldResponse, Finset.mul_sum]
  calc
    _ = ∑ i ∈ (support N B).filter (fun i => ¬ i.isRight = true), branchForce N B i z := by
      apply Finset.sum_congr rfl
      intro i hi
      cases i with
      | inl a => exact (branchForce_field N B a z).symm
      | inr a => simp at hi
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => branchForce_nonneg N B i hz)

theorem fieldResponse_five (N : ℕ) :
    fieldResponse N 5 = 6 * (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * fieldIntegral 5 4 := by
  rw [fieldResponse_eq_rows]
  norm_num [HistorySpectralWindow.enumerationBound, Finset.sum_range_succ,
    fieldIntegral_eq_zero (by norm_num : (5 : ℝ) ≤ 16),
    fieldIntegral_eq_zero (by norm_num : (5 : ℝ) ≤ 36)]
  ring

theorem gaussian_first_interval_lower :
    (2 / 3 : ℝ) ≤ ∫ u in (0 : ℝ)..1, Real.exp (-(u ^ 2)) := by
  have hc : Continuous (fun u : ℝ => 1 - u ^ 2) := by fun_prop
  have he : Continuous (fun u : ℝ => Real.exp (-(u ^ 2))) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 1)
    (hc.intervalIntegrable _ _) (he.intervalIntegrable _ _)
    (fun u _ => by linarith [Real.add_one_le_exp (-(u ^ 2))])
  have hv : (∫ u in (0 : ℝ)..1, 1 - u ^ 2) = 2 / 3 := by
    have hd (u : ℝ) : HasDerivAt (fun v : ℝ => v - v ^ 3 / 3) (1 - u ^ 2) u := by
      convert! (hasDerivAt_id u).sub (((hasDerivAt_id u).pow 3).div_const 3) using 1
      dsimp
      ring
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
      (hc.intervalIntegrable 0 1)
    convert! hi using 1
    norm_num
  rw [hv] at h
  linarith

theorem fieldIntegral_five_lower : (2 / 3 : ℝ) * Real.exp (-4) ≤ fieldIntegral 5 4 := by
  have he (u : ℝ) : Real.exp (-(u ^ 2 + 4)) =
      Real.exp (-4) * Real.exp (-(u ^ 2)) := by rw [← Real.exp_add]; congr 1; ring
  simp only [fieldIntegral, show (5 : ℝ) - 4 = 1 by norm_num, Real.sqrt_one, he,
    intervalIntegral.integral_const_mul]
  nlinarith [mul_le_mul_of_nonneg_left gaussian_first_interval_lower (Real.exp_pos (-4)).le]

theorem exp_four_lt_fifty_six : Real.exp 4 < 56 := by
  have he : Real.exp 1 < (68 / 25 : ℝ) := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hp : Real.exp 1 ^ 4 < (68 / 25 : ℝ) ^ 4 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by norm_num)
  have hh : Real.exp 4 = Real.exp 1 ^ 4 := by
    calc
      Real.exp 4 = Real.exp ((4 : ℝ) * 1) := by norm_num
      _ = Real.exp 1 ^ 4 := Real.exp_nat_mul (1 : ℝ) 4
  rw [hh]
  linarith

theorem completeForce_five_seven_gt_one (N : ℕ) : 1 < completeForce N 5 7 := by
  have hd : (4 : ℝ) ≤ HistoryAdjointCasimir.dimension N :=
    by exact_mod_cast HistoryAdjointCasimir.dimension_ge_four N
  have hl := fieldIntegral_five_lower
  have hfield := field_force_le_complete N 5 (z := 7) (by norm_num)
  rw [fieldResponse_five] at hfield
  norm_num [force] at hfield
  have hex : Real.exp (-4) = (Real.exp 4)⁻¹ := Real.exp_neg _
  have hpos := Real.exp_pos (4 : ℝ)
  have he : 1 < 56 * Real.exp (-4) := by
    rw [hex, ← div_eq_mul_inv, lt_div_iff₀ hpos]
    simpa using exp_four_lt_fifty_six
  have hfi := fieldIntegral_nonneg (5 : ℝ) 4
  have hsq : (16 : ℝ) ≤ (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 := by nlinarith
  have hmul := mul_nonneg (sub_nonneg.mpr hsq) hfi
  have hlo : 64 * Real.exp (-4) ≤
      6 * (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * fieldIntegral 5 4 := by
    nlinarith
  linarith

theorem ground_support_four (N : ℕ) (i : Index N) (hi : i ∈ support N 4) :
    i.isRight = true ∧ kinetic N i = 0 ∧
      HistoryHaarSectionJointHessian.eigenvalue N i = HistoryDefiningResponse.coefficient N := by
  have hcut := (mem_support N 4 i).mp hi
  cases i with
  | inl a =>
    obtain ⟨j, hj⟩ := HistoryHaarSectionRetention.field_kinetic_position N a
    rw [hj] at hcut
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    unfold HistoryHaarSectionRetention.fieldPosition at hcut
    nlinarith
  | inr a =>
    have hz := (scalar_first_shell a.2 (by norm_num : (0 : ℝ) < 4)
      (by norm_num : (4 : ℝ) ≤ 8)).mp hcut
    have hk : kinetic N (.inr a) = 0 := by
      change Geometry.SourceCasimirClosure.energy a.2.val.1 = 0
      rw [hz]
      norm_num [Geometry.SourceCasimirClosure.energy]
    exact ⟨rfl, hk, by rw [source_response_decomposition, hk]; simp [restoring]⟩

theorem ground_support_four_card (N : ℕ) :
    (support N 4).card = HistoryAdjointCasimir.dimension N := by
  have hs : (support N 4).filter (fun i => i.isRight = true) = support N 4 :=
    Finset.filter_eq_self.mpr (fun i hi => (ground_support_four N i hi).1)
  have hp : positionCount 4 = 1 := (positionCount_eq_one_iff 4).mpr (by norm_num)
  have h := scalarSupport_card N 4
  rw [hs, hp, content_card_one] at h
  exact h

def groundMoment : ℝ := ∫ u in (0 : ℝ)..2, u ^ 2 * Real.exp (-(u ^ 2))

theorem groundMoment_nonneg : 0 ≤ groundMoment :=
  intervalIntegral.integral_nonneg_of_forall (by norm_num)
    (fun u => mul_nonneg (sq_nonneg u) (Real.exp_pos _).le)

theorem groundMoment_le : groundMoment ≤ Real.sqrt Real.pi / 4 := by
  have hc : Continuous (fun u : ℝ => Real.exp (-(u ^ 2))) := by fun_prop
  have hm : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2))) := by fun_prop
  have hd (u : ℝ) : HasDerivAt (fun v : ℝ => v * Real.exp (-(v ^ 2)))
      (Real.exp (-(u ^ 2)) - 2 * (u ^ 2 * Real.exp (-(u ^ 2)))) u := by
    convert! (hasDerivAt_id u).mul (((hasDerivAt_id u).pow 2).neg.exp) using 1
    dsimp
    ring
  have hc2 := hm.const_mul (2 : ℝ)
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hd u)
    ((hc.sub hc2).intervalIntegrable 0 2)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
    (hc2.intervalIntegrable _ _), intervalIntegral.integral_const_mul] at hf
  have hg := fieldIntegral_le_full 4 0
  norm_num [fieldIntegral, frequencyMass] at hg
  norm_num only [one_mul, zero_mul, zero_pow, neg_zero, Real.exp_zero, sub_zero,
    show (2 : ℝ) ^ 2 = 4 by norm_num] at hf
  unfold groundMoment
  nlinarith [Real.exp_pos (-4)]

theorem dimension_div_restoring_le (N : ℕ) :
    (HistoryAdjointCasimir.dimension N : ℝ) / HistoryDefiningResponse.coefficient N ≤ 32 / 15 := by
  have hd : (4 : ℝ) ≤ HistoryAdjointCasimir.dimension N :=
    by exact_mod_cast HistoryAdjointCasimir.dimension_ge_four N
  have hp := HistoryDefiningResponse.coefficient_pos N
  rw [div_le_iff₀ hp, HistoryDefiningResponse.coefficient_eq]
  have hd0 : 0 < (HistoryAdjointCasimir.dimension N : ℝ) := by linarith
  have hinv : (HistoryAdjointCasimir.dimension N : ℝ) *
      (HistoryAdjointCasimir.dimension N : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hd0.ne'
  have he : 0 ≤ ((HistoryAdjointCasimir.dimension N : ℝ) - 4) *
      ((HistoryAdjointCasimir.dimension N : ℝ) + 4) := mul_nonneg (by linarith) (by linarith)
  apply (mul_le_mul_iff_right₀ hd0).mp
  nlinarith

theorem branchForce_four_le (N : ℕ) (i : Index N) (hi : i ∈ support N 4)
    {z : ℝ} (hz : 0 ≤ z) :
    branchForce N 4 i z ≤ groundMoment / HistoryDefiningResponse.coefficient N := by
  obtain ⟨_, hk, he⟩ := ground_support_four N i hi
  have hp := HistoryDefiningResponse.coefficient_pos N
  have hform (u : ℝ) : kineticFraction N i u =
      u ^ 2 / (u ^ 2 + HistoryDefiningResponse.coefficient N) := by
    simp [kineticFraction, kineticPrecision, precision, hk, he]
  have hw (u : ℝ) : weight N i u = Real.exp (-(u ^ 2)) := by
    simp [weight, kineticPrecision, hk]
  have hc : Continuous (fun u : ℝ => u ^ 2 * Real.exp (-(u ^ 2)) /
      HistoryDefiningResponse.coefficient N) := by fun_prop
  have h := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (0 : ℝ) ≤ 2)
    ((force_continuous N i hz).intervalIntegrable 0 2) (hc.intervalIntegrable 0 2)
    (fun u _ => ?_)
  · simpa only [branchForce, forceIntegral, hk, sub_zero,
      show Real.sqrt (4 : ℝ) = 2 by norm_num, groundMoment,
      intervalIntegral.integral_div] using h
  · have hr := force_le_fraction (kineticFraction_nonneg N i u) hz
    have hq : u ^ 2 / (u ^ 2 + HistoryDefiningResponse.coefficient N) ≤
        u ^ 2 / HistoryDefiningResponse.coefficient N :=
      div_le_div_of_nonneg_left (sq_nonneg u) hp (by nlinarith [sq_nonneg u])
    rw [hw]
    calc
      _ ≤ Real.exp (-(u ^ 2)) * (u ^ 2 / HistoryDefiningResponse.coefficient N) :=
        mul_le_mul_of_nonneg_left (hr.trans (by simpa only [hform] using hq)) (Real.exp_pos _).le
      _ = _ := by ring

theorem completeForce_four_le (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    completeForce N 4 z ≤ (8 / 15 : ℝ) * Real.sqrt Real.pi := by
  have h := Finset.sum_le_sum (fun i hi => branchForce_four_le N i hi hz)
  change completeForce N 4 z ≤ ∑ _i ∈ support N 4,
    groundMoment / HistoryDefiningResponse.coefficient N at h
  simp only [Finset.sum_const, nsmul_eq_mul, ground_support_four_card] at h
  have hd := dimension_div_restoring_le N
  have hprod := mul_le_mul hd groundMoment_le groundMoment_nonneg
    (by norm_num : (0 : ℝ) ≤ 32 / 15)
  have he : (HistoryAdjointCasimir.dimension N : ℝ) *
      (groundMoment / HistoryDefiningResponse.coefficient N) =
      ((HistoryAdjointCasimir.dimension N : ℝ) / HistoryDefiningResponse.coefficient N) *
        groundMoment := by ring
  rw [he] at h
  linarith

theorem completeForce_four_lt_one (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    completeForce N 4 z < 1 := by
  have hroot : Real.sqrt Real.pi < (9 / 5 : ℝ) := by
    have hs := Real.sq_sqrt Real.pi_pos.le
    nlinarith [Real.sqrt_nonneg Real.pi, Real.pi_lt_d2]
  linarith [completeForce_four_le N hz]

theorem force_monotone_nonneg {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (force r) (Ici 0) := by
  intro z hz v hv hzv
  change 0 ≤ z at hz
  change 0 ≤ v at hv
  have hp : 0 < 1 + z * r := by nlinarith
  have hq : 1 + z * r ≤ 1 + v * r := by nlinarith
  have hd := div_le_div_of_nonneg_left hr hp hq
  unfold force
  linarith

theorem force_strictMonoOn_nonneg {r : ℝ} (hr : 0 < r) :
    StrictMonoOn (force r) (Ici 0) := by
  intro z hz v hv hzv
  change 0 ≤ z at hz
  change 0 ≤ v at hv
  have hp : 0 < 1 + z * r := by nlinarith
  have hq : 1 + z * r < 1 + v * r := by nlinarith
  have hd := div_lt_div_of_pos_left hr hp hq
  unfold force
  linarith

theorem branchForce_monotone (N : ℕ) (B : ℝ) (i : Index N) :
    MonotoneOn (branchForce N B i) (Ici 0) := by
  intro z hz v hv hzv
  exact intervalIntegral.integral_mono_on (Real.sqrt_nonneg _)
    ((force_continuous N i hz).intervalIntegrable _ _)
    ((force_continuous N i hv).intervalIntegrable _ _)
    (fun u _ => mul_le_mul_of_nonneg_left
      (force_monotone_nonneg (kineticFraction_nonneg N i u) hz hv hzv) (weight_pos N i u).le)

theorem branchForce_strictMonoOn (N : ℕ) (B : ℝ) (i : Index N)
    (hi : i ∈ support N B) : StrictMonoOn (branchForce N B i) (Ici 0) := by
  intro z hz v hv hzv
  have ht : 0 < Real.sqrt (B - kinetic N i) :=
    Real.sqrt_pos.mpr (sub_pos.mpr ((mem_support N B i).mp hi))
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt ht
    (force_continuous N i hz).continuousOn (force_continuous N i hv).continuousOn
    (fun u _ => mul_le_mul_of_nonneg_left
      (force_monotone_nonneg (kineticFraction_nonneg N i u) hz hv hzv.le) (weight_pos N i u).le)
  let u := Real.sqrt (B - kinetic N i) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  refine ⟨u, ⟨hu.le, by dsimp [u]; linarith⟩, ?_⟩
  apply mul_lt_mul_of_pos_left _ (weight_pos N i u)
  exact force_strictMonoOn_nonneg (div_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (kinetic_nonneg N i))
    (precision_pos N i u)) hz hv hzv

theorem completeForce_strictMonoOn (N : ℕ) {B : ℝ} (hB : 0 < B) :
    StrictMonoOn (completeForce N B) (Ici 0) := by
  intro z hz v hv hzv
  obtain ⟨i, hi⟩ := HistoryHaarSectionProbability.support_nonempty_of_pos N hB
  exact Finset.sum_lt_sum (fun j _ => branchForce_monotone N B j hz hv hzv.le)
    ⟨i, hi, branchForce_strictMonoOn N B i hi hz hv hzv⟩

theorem completeForce_continuousOn (N : ℕ) (B : ℝ) :
    ContinuousOn (completeForce N B) (Ici 0) := by
  intro z hz
  change 0 ≤ z at hz
  have hder (i : Index N) := positive_forceIntegral_hasDerivAt
    (kineticFraction N i) (weight N i) 0 (Real.sqrt (B - kinetic N i))
    (kineticFraction_continuous N i) (weight_continuous N i)
    (kineticFraction_nonneg N i) (kineticFraction_le_one N i)
    (fun u => (weight_pos N i u).le) (weight_le_one N i)
    (show z ∈ Ioi (-(1 / 2 : ℝ)) by change -(1 / 2 : ℝ) < z; linarith)
  exact (HasDerivAt.fun_sum (fun i _ => hder i)).continuousAt.continuousWithinAt

theorem branchForce_mono_window (N : ℕ) (i : Index N) {z : ℝ} (hz : 0 ≤ z) :
    Monotone (fun B => branchForce N B i z) := by
  intro B C hBC
  apply intervalIntegral.integral_mono_interval le_rfl (Real.sqrt_nonneg _)
    (Real.sqrt_le_sqrt (sub_le_sub_right hBC _))
  · exact Filter.Eventually.of_forall (fun u => mul_nonneg (weight_pos N i u).le
      (force_nonneg_of_nonneg (kineticFraction_nonneg N i u) hz))
  · exact (force_continuous N i hz).intervalIntegrable _ _

theorem completeForce_mono_window (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    Monotone (fun B => completeForce N B z) := by
  intro B C hBC
  calc
    completeForce N B z ≤ ∑ i ∈ support N B, branchForce N C i z :=
      Finset.sum_le_sum (fun i _ => branchForce_mono_window N i hz hBC)
    _ ≤ completeForce N C z := Finset.sum_le_sum_of_subset_of_nonneg
      (support_mono N hBC) (fun i _ _ => branchForce_nonneg N C i hz)

theorem existsUnique_balance_above_five (N : ℕ) {B : ℝ} (hB : 5 ≤ B) :
    ∃! z : ℝ, 0 < z ∧ completeForce N B z = 1 := by
  have h5 : 1 < completeForce N B 7 := lt_of_lt_of_le
    (completeForce_five_seven_gt_one N) (completeForce_mono_window N (z := 7) (by norm_num) hB)
  have hcont := (completeForce_continuousOn N B).mono
    (show Icc (0 : ℝ) 7 ⊆ Ici 0 from fun _ h => h.1)
  obtain ⟨z, hz, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 7) hcont
    (show (1 : ℝ) ∈ Icc (completeForce N B 0) (completeForce N B 7) by
      rw [completeForce_zero]; exact ⟨by norm_num, h5.le⟩)
  have hz0 : 0 < z := by
    by_contra hn
    have heq : z = 0 := le_antisymm (le_of_not_gt hn) hz.1
    subst z
    norm_num at he
  refine ⟨z, ⟨hz0, he⟩, ?_⟩
  intro v hv
  exact (completeForce_strictMonoOn N (B := B) (by linarith)).injOn
    hv.1.le hz0.le (hv.2.trans he.symm)

theorem no_balance_below_four (N : ℕ) {B z : ℝ} (hB : B ≤ 4) (hz : 0 ≤ z) :
    completeForce N B z < 1 := lt_of_le_of_lt (completeForce_mono_window N hz hB)
      (completeForce_four_lt_one N hz)

/-- Feasibility in the specified source-unit comparison. This predicate
does not select a window from the admissible family. -/
def BalancedLevel (N R : ℕ) : Prop := ∃ z : ℝ, 0 < z ∧ completeForce N R z = 1

theorem balancedLevel_iff (N R : ℕ) : BalancedLevel N R ↔ 5 ≤ R := by
  constructor
  · rintro ⟨z, hz, he⟩
    by_contra hn
    have hR : R ≤ 4 := by omega
    have hh := no_balance_below_four N (B := (R : ℝ)) (by exact_mod_cast hR) hz.le
    linarith
  · intro hR
    exact (existsUnique_balance_above_five N (B := (R : ℝ)) (by exact_mod_cast hR)).exists

theorem balancedLevel_five_joint_content :
    HistoryHaarSectionRetention.fieldPositionCount 5 = 1 ∧ positionCount 5 = 1 :=
  (HistoryHaarSectionRetention.first_joint_cell 5).mpr (by norm_num)

theorem unique_stationary_at_five (N : ℕ) :
    ∃! z : ℝ, 0 < z ∧ deriv (sourcePotential N 5) z = 0 := by
  have heq (z : ℝ) (hz : 0 < z) :
      deriv (sourcePotential N 5) z = 0 ↔ completeForce N 5 z = 1 := by
    rw [(sourcePotential_hasDerivAt N 5 (by linarith : -(1 / 2 : ℝ) < z)).deriv]
    exact sub_eq_zero
  obtain ⟨z, hz, huniq⟩ := existsUnique_balance_above_five N (B := 5) le_rfl
  refine ⟨z, ⟨hz.1, (heq z hz.1).mpr hz.2⟩, ?_⟩
  intro v hv
  exact huniq v ⟨hv.1, (heq v hv.1).mp hv.2⟩

theorem perturbedPrecision_pos (N : ℕ) (i : Index N) (u : ℝ) {z : ℝ}
    (hz : -(1 / 2 : ℝ) < z) :
    0 < precision N i u + z * kineticPrecision N i u := by
  have h := positive_precision_lower (kineticFraction_nonneg N i u)
    (kineticFraction_le_one N i u) hz
  have hp := precision_pos N i u
  have he : precision N i u * (1 + z * kineticFraction N i u) =
      precision N i u + z * kineticPrecision N i u := by
    unfold kineticFraction
    field_simp
  rw [← he]
  exact mul_pos hp (by linarith)

/-- The same Gaussian probability comparison remains valid at the positive
equilibrium. No small-amplitude Taylor replacement is used. -/
theorem relativeEntropy_eq_comparison (N : ℕ) (B : ℝ) {z : ℝ}
    (hz : -(1 / 2 : ℝ) < z) :
    HistoryHaarSectionProbability.relativeEntropy N B z =
      comparison N B z / (2 * HistoryHaarSectionProbability.mass N B) := by
  unfold HistoryHaarSectionProbability.relativeEntropy HistoryHaarSectionProbability.average
  have he (i : Index N) (u : ℝ) := Operations.GaussianPrecisionKL.varied_precision
    (precision_pos N i u) (perturbedPrecision_pos N i u hz)
  simp_rw [he]
  change (∑ i ∈ support N B, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
    weight N i u * (cost (kineticFraction N i u) z / 2)) /
      HistoryHaarSectionProbability.mass N B = _
  simp_rw [← mul_div_assoc, intervalIntegral.integral_div]
  rw [← Finset.sum_div]
  change (comparison N B z / 2) / HistoryHaarSectionProbability.mass N B = _
  rw [div_div]

theorem sourcePotential_eq_relativeEntropy (N : ℕ) {B z : ℝ} (hB : 0 < B)
    (hz : -(1 / 2 : ℝ) < z) : sourcePotential N B z =
      2 * HistoryHaarSectionProbability.mass N B *
        HistoryHaarSectionProbability.relativeEntropy N B z - z := by
  rw [sourcePotential, HistoryGaussianCovariance.generatedIntensity_eq,
    relativeEntropy_eq_comparison N B hz]
  have hp := HistoryHaarSectionProbability.mass_pos_of_pos N hB
  field_simp

structure Conclusions : Prop where
  actual_first_shell : ∀ N,
    fieldResponse N 5 = 6 * (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 * fieldIntegral 5 4
  insufficient_ground_window : ∀ N B z, B ≤ 4 → 0 ≤ z → completeForce N B z < 1
  sufficient_first_joint_window : ∀ N, 1 < completeForce N 5 7
  integer_balance_criterion : ∀ N R, BalancedLevel N R ↔ 5 ≤ R
  joint_content_at_five :
    HistoryHaarSectionRetention.fieldPositionCount 5 = 1 ∧ positionCount 5 = 1
  unique_comparison_equilibrium : ∀ N,
    ∃! z : ℝ, 0 < z ∧ deriv (sourcePotential N 5) z = 0
  exact_probability_comparison : ∀ N B z, -(1 / 2 : ℝ) < z →
    HistoryHaarSectionProbability.relativeEntropy N B z =
      comparison N B z / (2 * HistoryHaarSectionProbability.mass N B)

theorem generated : Conclusions where
  actual_first_shell := fieldResponse_five
  insufficient_ground_window := fun N _ _ hB hz => no_balance_below_four N hB hz
  sufficient_first_joint_window := completeForce_five_seven_gt_one
  integer_balance_criterion := balancedLevel_iff
  joint_content_at_five := balancedLevel_five_joint_content
  unique_comparison_equilibrium := unique_stationary_at_five
  exact_probability_comparison := fun N B _ hz => relativeEntropy_eq_comparison N B hz

end GeneratedFoundations.Arithmetic.HistoryHaarSectionSourceBalance
