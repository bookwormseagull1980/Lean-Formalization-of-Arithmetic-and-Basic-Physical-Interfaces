module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionShells
public import GeneratedFoundations.Operations.GaussianPrecisionKL

/-!
# Probability normalization of the complete Gaussian window

The normalizer is the Gaussian mass of every original spectral label and
its actual frequency interval. It is calculated from that window, rather
than replaced by the number of connection coordinates. The normalized
average of the actual Gaussian relative entropy is then identified with
the complete precision comparison, including the real-coordinate factor.

Coordinate transport divides both the mass and the comparison by the
same Jacobian. Their normalized ratio is consequently invariant. This
probability normalization and an effective-action vertex normalization
are different operations; the former does not impose a content count.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionProbability

open HistoryHaarSectionWindow HistoryHaarSectionComparison
open HistoryHaarSectionJointHessian (Index)
open Operations.ScalarPrecisionComparison

local instance (N : ℕ) : DecidableEq (Index N) := Classical.decEq _

def branchMass (N : ℕ) (B : ℝ) (i : Index N) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), weight N i u

def mass (N : ℕ) (B : ℝ) : ℝ := ∑ i ∈ support N B, branchMass N B i

theorem support_nonempty_of_pos (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (support N B).Nonempty := by
  let a : HistoryHaarSectionAction.PositionLabels N 0 :=
    ((HistoryCliffordAction.historyPoint N, Sum.inl 0), 0, 0)
  refine ⟨positionIndex N 0 a, (position_membership N 0 B a).mpr ?_⟩
  simpa [Geometry.SourceScalarKineticForm.position_eq] using hB

theorem branchMass_eq_fieldIntegral (N : ℕ) (B : ℝ) (i : Index N) :
    branchMass N B i = HistoryHaarSectionShells.fieldIntegral B (kinetic N i) := rfl

theorem branchMass_nonneg (N : ℕ) (B : ℝ) (i : Index N) : 0 ≤ branchMass N B i :=
  HistoryHaarSectionShells.fieldIntegral_nonneg _ _

theorem branchMass_pos (N : ℕ) (B : ℝ) (i : Index N) (hi : i ∈ support N B) :
    0 < branchMass N B i := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((weight_continuous N i).intervalIntegrable _ _) (fun u _ => weight_pos N i u)
  exact Real.sqrt_pos.mpr (sub_pos.mpr ((mem_support N B i).mp hi))

theorem mass_nonneg (N : ℕ) (B : ℝ) : 0 ≤ mass N B :=
  Finset.sum_nonneg (fun i _ => branchMass_nonneg N B i)

theorem mass_pos (N : ℕ) (B : ℝ) (hB : (support N B).Nonempty) : 0 < mass N B := by
  exact Finset.sum_pos (fun i hi => branchMass_pos N B i hi) hB

theorem mass_pos_of_pos (N : ℕ) {B : ℝ} (hB : 0 < B) : 0 < mass N B :=
  mass_pos N B (support_nonempty_of_pos N hB)

def average (N : ℕ) (B : ℝ) (f : Index N → ℝ → ℝ) : ℝ :=
  (∑ i ∈ support N B,
    ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i), weight N i u * f i u) / mass N B

theorem average_one (N : ℕ) (B : ℝ) (hB : (support N B).Nonempty) :
    average N B (fun _ _ => 1) = 1 := by
  simp only [average, mul_one]
  exact div_self (mass_pos N B hB).ne'

theorem average_nonneg (N : ℕ) (B : ℝ) (f : Index N → ℝ → ℝ)
    (hf : ∀ i ∈ support N B, ∀ u, 0 ≤ f i u) : 0 ≤ average N B f := by
  apply div_nonneg _ (mass_nonneg N B)
  apply Finset.sum_nonneg
  intro i hi
  exact intervalIntegral.integral_nonneg_of_forall (Real.sqrt_nonneg _)
    (fun u => mul_nonneg (weight_pos N i u).le (hf i hi u))

theorem kernel_le_weight (N : ℕ) (i : Index N) (u : ℝ) :
    kernel N i u ≤ weight N i u := by
  have hr := kineticFraction_nonneg N i u
  have hr1 := kineticFraction_le_one N i u
  have hs : kineticFraction N i u ^ 2 ≤ 1 := by nlinarith
  rw [kernel_eq_comparison_curvature, curvature_zero]
  exact (mul_le_mul_of_nonneg_left hs (weight_pos N i u).le).trans_eq (mul_one _)

theorem branchIntegral_le_mass (N : ℕ) (B : ℝ) (i : Index N) :
    branchIntegral N B i ≤ branchMass N B i := by
  apply intervalIntegral.integral_mono (Real.sqrt_nonneg _)
    ((kernel_continuous N i).intervalIntegrable _ _)
    ((weight_continuous N i).intervalIntegrable _ _)
  exact fun u => kernel_le_weight N i u

theorem response_le_mass (N : ℕ) (B : ℝ) : responseTrace N B ≤ mass N B :=
  Finset.sum_le_sum (fun i _ => branchIntegral_le_mass N B i)

theorem average_fraction_sq (N : ℕ) (B : ℝ) :
    average N B (fun i u => kineticFraction N i u ^ 2) = responseTrace N B / mass N B := by
  unfold average responseTrace branchIntegral
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply intervalIntegral.integral_congr
  intro u _
  simpa only [curvature_zero] using (kernel_eq_comparison_curvature N i u).symm

theorem normalized_response_bounds (N : ℕ) (B : ℝ) (hB : (support N B).Nonempty) :
    0 < responseTrace N B / mass N B ∧ responseTrace N B / mass N B ≤ 1 := by
  exact ⟨div_pos (responseTrace_pos N B hB) (mass_pos N B hB),
    (div_le_one (mass_pos N B hB)).mpr (response_le_mass N B)⟩

theorem perturbedPrecision_pos (N : ℕ) (i : Index N) (u : ℝ) {z : ℝ}
    (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    0 < precision N i u + z * kineticPrecision N i u := by
  have h := local_precision_lower (kineticFraction_nonneg N i u)
    (kineticFraction_le_one N i u) hz
  have hp := precision_pos N i u
  have he : precision N i u * (1 + z * kineticFraction N i u) =
      precision N i u + z * kineticPrecision N i u := by
    unfold kineticFraction
    field_simp
  rw [← he]
  exact mul_pos hp (by linarith)

/-- The relative entropy is computed on the actual real Gaussian at each
original precision, and only then averaged over the complete source window. -/
def relativeEntropy (N : ℕ) (B z : ℝ) : ℝ :=
  average N B (fun i u =>
    (InformationTheory.klDiv
      (Operations.GaussianPrecisionKL.law (precision N i u))
      (Operations.GaussianPrecisionKL.law
        (precision N i u + z * kineticPrecision N i u))).toReal)

theorem relativeEntropy_eq_comparison (N : ℕ) (B : ℝ) {z : ℝ}
    (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    relativeEntropy N B z = comparison N B z / (2 * mass N B) := by
  unfold relativeEntropy average
  have he (i : Index N) (u : ℝ) := Operations.GaussianPrecisionKL.varied_precision
    (precision_pos N i u) (perturbedPrecision_pos N i u hz)
  simp_rw [he]
  change (∑ i ∈ support N B, ∫ u in (0 : ℝ)..Real.sqrt (B - kinetic N i),
    weight N i u * (cost (kineticFraction N i u) z / 2)) / mass N B = _
  simp_rw [← mul_div_assoc, intervalIntegral.integral_div]
  rw [← Finset.sum_div]
  change (comparison N B z / 2) / mass N B = _
  rw [div_div]

theorem relativeEntropy_hasDerivAt (N : ℕ) (B : ℝ) {z : ℝ}
    (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (relativeEntropy N B) (completeForce N B z / (2 * mass N B)) z := by
  apply ((comparison_hasDerivAt N B hz).div_const (2 * mass N B)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hz] with w hw
  exact relativeEntropy_eq_comparison N B hw

theorem relativeEntropy_secondDeriv_zero (N : ℕ) (B : ℝ) :
    HasDerivAt (fun z => deriv (relativeEntropy N B) z)
      (responseTrace N B / (2 * mass N B)) 0 := by
  apply ((completeForce_hasDerivAt_zero N B).div_const (2 * mass N B)).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  exact (relativeEntropy_hasDerivAt N B hz).deriv

def scaledMass (N : ℕ) (B c : ℝ) : ℝ :=
  ∑ i ∈ support N B,
    ∫ ω in (0 : ℝ)..HistoryHaarSectionScale.frequencyEdge N B c i,
      HistoryHaarSectionScale.scaledWeight N c i ω

theorem mass_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    scaledMass N B c = mass N B / c := by
  have hi (i : Index N) :
      (∫ ω in (0 : ℝ)..HistoryHaarSectionScale.frequencyEdge N B c i,
        HistoryHaarSectionScale.scaledWeight N c i ω) = branchMass N B i / c := by
    rw [HistoryHaarSectionScale.frequencyEdge_transport N B hc,
      show HistoryHaarSectionScale.scaledWeight N c i = fun ω => weight N i (c * ω) from
        funext (fun ω => HistoryHaarSectionScale.weight_transport N hc.ne' i ω),
      intervalIntegral.integral_comp_mul_left _ hc.ne']
    have he : c * (Real.sqrt (B - kinetic N i) / c) = Real.sqrt (B - kinetic N i) := by
      field_simp
    rw [mul_zero, he, smul_eq_mul]
    exact (div_eq_inv_mul _ _).symm
  simp only [scaledMass, hi, Finset.sum_div, mass]

theorem normalized_response_transport (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    HistoryHaarSectionScale.scaledResponse N B c / scaledMass N B c =
      responseTrace N B / mass N B := by
  rw [HistoryHaarSectionScale.response_transport N B hc, mass_transport N B hc]
  exact div_div_div_cancel_right₀ hc.ne' _ _

structure Conclusions : Prop where
  actual_window_mass : ∀ N B, (support N B).Nonempty → 0 < mass N B
  probability_normalization : ∀ N B, (support N B).Nonempty →
    average N B (fun _ _ => 1) = 1
  relative_entropy : ∀ N B z, z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) →
    relativeEntropy N B z = comparison N B z / (2 * mass N B)
  relative_entropy_curvature : ∀ N B,
    HasDerivAt (fun z => deriv (relativeEntropy N B) z)
      (responseTrace N B / (2 * mass N B)) 0
  normalized_response : ∀ N B, (support N B).Nonempty →
    0 < responseTrace N B / mass N B ∧ responseTrace N B / mass N B ≤ 1
  common_scale_transport : ∀ N B c, 0 < c →
    HistoryHaarSectionScale.scaledResponse N B c / scaledMass N B c =
      responseTrace N B / mass N B

theorem generated : Conclusions where
  actual_window_mass := mass_pos
  probability_normalization := average_one
  relative_entropy := fun _ _ _ hz => relativeEntropy_eq_comparison _ _ hz
  relative_entropy_curvature := relativeEntropy_secondDeriv_zero
  normalized_response := normalized_response_bounds
  common_scale_transport := fun N B _ hc => normalized_response_transport N B hc

end GeneratedFoundations.Arithmetic.HistoryHaarSectionProbability
