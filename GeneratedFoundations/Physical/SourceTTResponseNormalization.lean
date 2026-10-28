module

public import GeneratedFoundations.Physical.SourceTensorResponseEndpoint
public import GeneratedFoundations.Operations.FinitePrecisionPath

/-!
# Source normalization of the tensor response

The two tensor polarizations are measured with their actual half-trace
pairing. The mass-weighted profile is the logarithmic mass derivative of
the two-leg kernel, with the derivative divided by the number of legs.
For a finite positive precision the same kernel is twice the variance of
the kinetic quadratic insertion in the original Gaussian law. The
partition and its derivatives use that law, not a separately assigned
susceptibility. Nonlinear precision paths retain their direct second term.

The matching theorem concerns the existing endpoint rule. A common
positive rescaling of the spectral response and the reference profile
cancels from that rule. This normalization invariance does not identify
the spectral integral with its mass derivative or select a matching rule
from the extremum alone. The kinetic insertion below is stated explicitly;
identification with another projected source requires its vertex identity.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

namespace GeneratedFoundations.Physical.SourceTTResponseNormalization

open Geometry.SourceAxisTT SourceTensorResponseEndpoint
open Operations

/-! ## Polarization pairing -/

def tensorPairing (h k : SpatialTensor) : ℝ :=
  Matrix.trace (h.transpose * k) / 2

theorem tensorPairing_amplitudes (a b c d : ℝ) :
    tensorPairing (ttMatrix a b) (ttMatrix c d) = a * c + b * d := by
  norm_num [tensorPairing, ttMatrix, Matrix.trace, Matrix.mul_apply,
    Matrix.transpose_apply, Fin.sum_univ_succ]
  ring

theorem tensorPairing_self (a b : ℝ) :
    tensorPairing (ttMatrix a b) (ttMatrix a b) = a ^ 2 + b ^ 2 := by
  rw [tensorPairing_amplitudes]
  ring

theorem polarization_gram :
    tensorPairing plusPolarization.1 plusPolarization.1 = 1 ∧
    tensorPairing crossPolarization.1 crossPolarization.1 = 1 ∧
    tensorPairing plusPolarization.1 crossPolarization.1 = 0 := by
  norm_num [plusPolarization, crossPolarization, pairToTT,
    tensorPairing_amplitudes]

/-! ## Logarithmic mass response -/

def logMassKernel (q2 m2 z : ℝ) : ℝ := ttKernel q2 (Real.exp z * m2)

theorem logMassKernel_hasDerivAt (q2 m2 z : ℝ)
    (hden : q2 + Real.exp z * m2 ≠ 0) :
    HasDerivAt (logMassKernel q2 m2)
      (-2 * massWeightedResponse (massFraction q2 (Real.exp z * m2))) z := by
  have hd := (hasDerivAt_const z (q2 ^ 2)).div
    (((Real.hasDerivAt_exp z).mul_const m2).const_add q2 |>.pow 2)
    (pow_ne_zero 2 hden)
  convert! hd using 1
  unfold massWeightedResponse massFraction
  simp only [Pi.pow_apply, Nat.cast_ofNat, zero_mul, zero_sub]
  field_simp
  ring

theorem logMassKernel_response (q2 m2 z : ℝ)
    (hden : q2 + Real.exp z * m2 ≠ 0) :
    -(deriv (logMassKernel q2 m2) z) / 2 =
      massWeightedResponse (massFraction q2 (Real.exp z * m2)) := by
  rw [(logMassKernel_hasDerivAt q2 m2 z hden).deriv]
  ring

variable {ι : Type*} [Fintype ι]

theorem fixed_weight_logMass_hasDerivAt (w q2 m2 : ι → ℝ) (z : ℝ)
    (hden : ∀ i, q2 i + Real.exp z * m2 i ≠ 0) :
    HasDerivAt (fun t => ∑ i, w i * logMassKernel (q2 i) (m2 i) t)
      (-2 * ∑ i, w i *
        massWeightedResponse (massFraction (q2 i) (Real.exp z * m2 i))) z := by
  simpa only [Finset.sum_apply, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm] using
    HasDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (logMassKernel_hasDerivAt (q2 i) (m2 i) z (hden i)).const_mul (w i))

theorem weighted_response_bound (w y : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1) :
    (∑ i, w i * massWeightedResponse (y i)) ≤ (4 / 27 : ℝ) * ∑ i, w i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (massWeightedResponse_le (hy i).1 (hy i).2) (hw i)

/-! ## The same Gaussian partition and its kinetic insertion -/

variable [DecidableEq ι]

def kineticPrecision (q2 m2 : ι → ℝ) : ι → ℝ := fun i => q2 i + m2 i

def gaussianKineticResponse (q2 m2 : ι → ℝ) : ℝ :=
  2 * Var[FinitePrecisionGaussian.score q2;
    FinitePrecisionGaussian.law (kineticPrecision q2 m2)]

theorem gaussianKineticResponse_eq (q2 m2 : ι → ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    gaussianKineticResponse q2 m2 = ∑ i, ttKernel (q2 i) (m2 i) := by
  rw [gaussianKineticResponse,
    FinitePrecisionGaussian.score_variance (p := kineticPrecision q2 m2) hp]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold kineticPrecision ttKernel
  field_simp

def gaussianModeResponse (q2 m2 : ℝ) : ℝ :=
  gaussianKineticResponse (fun _ : Fin 1 => q2) (fun _ : Fin 1 => m2)

theorem gaussianModeResponse_eq (q2 m2 : ℝ) (hp : 0 < q2 + m2) :
    gaussianModeResponse q2 m2 = ttKernel q2 m2 := by
  rw [gaussianModeResponse, gaussianKineticResponse_eq _ _ (fun _ => hp)]
  simp

theorem kinetic_partition_eq (q2 m2 : ι → ℝ) (z : ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i)
    (hz : ∀ i, 0 < q2 i + m2 i + z * q2 i) :
    (∫ x : FinitePrecisionGaussian.Space ι,
      Real.exp (-z * FinitePrecisionGaussian.score q2 x)
        ∂FinitePrecisionGaussian.law (kineticPrecision q2 m2)) =
      Real.exp (FinitePrecisionTilt.logPartition (kineticPrecision q2 m2) q2 z) :=
  FinitePrecisionTilt.partition_eq_exp hp hz

omit [DecidableEq ι] in
theorem kinetic_partition_first_response (q2 m2 : ι → ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    HasDerivAt (FinitePrecisionTilt.logPartition (kineticPrecision q2 m2) q2)
      (-FinitePrecisionTilt.mean (kineticPrecision q2 m2) q2 0) 0 :=
  FinitePrecisionTilt.logPartition_hasDerivAt hp (by simpa [FinitePrecisionTilt.variedPrecision])

theorem kinetic_partition_second_response (q2 m2 : ι → ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    HasDerivAt (fun z => -FinitePrecisionTilt.mean (kineticPrecision q2 m2) q2 z)
      (gaussianKineticResponse q2 m2 / 2) 0 := by
  convert! FinitePrecisionTilt.negativeMean_hasDerivAt
    (p := kineticPrecision q2 m2) (q := q2) (z := 0)
    (by simpa [FinitePrecisionTilt.variedPrecision]) using 1
  rw [gaussianKineticResponse,
    FinitePrecisionGaussian.score_variance (p := kineticPrecision q2 m2) hp]
  simp [FinitePrecisionTilt.susceptibility, FinitePrecisionTilt.variedPrecision]

def kineticLogPartition (q2 m2 : ι → ℝ) (z : ℝ) : ℝ :=
  Real.log (FinitePrecisionTilt.partition (kineticPrecision q2 m2) q2 z)

omit [DecidableEq ι] in
private theorem variedPrecision_eventually_pos (q2 m2 : ι → ℝ) (z : ℝ)
    (hz : ∀ i, 0 < q2 i + m2 i + z * q2 i) :
    ∀ᶠ t in 𝓝 z, ∀ i, 0 < q2 i + m2 i + t * q2 i := by
  apply Filter.eventually_all.2
  intro i
  have hc : ContinuousAt (fun t : ℝ => q2 i + m2 i + t * q2 i) z := by fun_prop
  exact hc.eventually (eventually_gt_nhds (hz i))

/-- The derivative belongs to the logarithm of the original Gaussian
integral, using positivity in a neighbourhood of the varied precision. -/
theorem kineticLogPartition_hasDerivAt (q2 m2 : ι → ℝ) (z : ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i)
    (hz : ∀ i, 0 < q2 i + m2 i + z * q2 i) :
    HasDerivAt (kineticLogPartition q2 m2)
      (-FinitePrecisionTilt.mean (kineticPrecision q2 m2) q2 z) z := by
  apply (FinitePrecisionTilt.logPartition_hasDerivAt hp hz).congr_of_eventuallyEq
  filter_upwards [variedPrecision_eventually_pos q2 m2 z hz] with t ht
  exact FinitePrecisionTilt.log_partition hp ht

/-- The second derivative of the actual logarithmic Gaussian integral,
not only of its closed formula, is the same source variance. -/
theorem kineticLogPartition_second_response (q2 m2 : ι → ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    HasDerivAt (deriv (kineticLogPartition q2 m2))
      (gaussianKineticResponse q2 m2 / 2) 0 := by
  apply (kinetic_partition_second_response q2 m2 hp).congr_of_eventuallyEq
  have h0 : ∀ i, 0 < q2 i + m2 i + (0 : ℝ) * q2 i := by simpa using hp
  filter_upwards [variedPrecision_eventually_pos q2 m2 0 h0] with t ht
  exact (kineticLogPartition_hasDerivAt q2 m2 t hp ht).deriv

theorem kinetic_vertex_rescaling (q2 m2 : ι → ℝ) (r : ℝ)
    (hp : ∀ i, 0 < q2 i + m2 i) :
    2 * Var[FinitePrecisionGaussian.score (fun i => r * q2 i);
      FinitePrecisionGaussian.law (kineticPrecision q2 m2)] =
      r ^ 2 * gaussianKineticResponse q2 m2 := by
  rw [FinitePrecisionGaussian.score_variance (p := kineticPrecision q2 m2) hp,
    gaussianKineticResponse_eq _ _ hp]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold kineticPrecision ttKernel
  field_simp

/-- For a nonlinear precision path the directly varied quadratic term is
retained together with the score variance. -/
theorem nonlinear_source_response (p v a : ℝ → ι → ℝ) (z : ℝ)
    (hp : ∀ i, 0 < p z i) :
    -FinitePrecisionPath.curvature p v a z =
      Var[FinitePrecisionGaussian.score (v z); FinitePrecisionGaussian.law (p z)] -
      ∫ x, FinitePrecisionGaussian.score (a z) x ∂FinitePrecisionGaussian.law (p z) := by
  rw [FinitePrecisionPath.curvature_eq_mean_sub_variance hp]
  ring

/-- With the actual first and second precision derivatives, the complete
source expression is the derivative of the first partition response. -/
theorem nonlinear_partition_second_response (p v a : ℝ → ι → ℝ) (z : ℝ)
    (hp : ∀ i, 0 < p z i)
    (hv : ∀ i, HasDerivAt (fun t => p t i) (v z i) z)
    (ha : ∀ i, HasDerivAt (fun t => v t i) (a z i) z) :
    HasDerivAt (fun t => -FinitePrecisionPath.force p v t)
      (Var[FinitePrecisionGaussian.score (v z); FinitePrecisionGaussian.law (p z)] -
        ∫ x, FinitePrecisionGaussian.score (a z) x ∂FinitePrecisionGaussian.law (p z)) z := by
  have hd := (FinitePrecisionPath.force_hasDerivAt hp hv ha).neg
  rwa [nonlinear_source_response p v a z hp] at hd

/-! ## Common normalization of the existing endpoint matching -/

def calibratedResponse (κ A c : ℝ) : ℝ := κ * (A / c)

def calibratedProfile (κ y : ℝ) : ℝ := κ * massWeightedResponse y

theorem calibratedProfile_le {κ y : ℝ} (hκ : 0 < κ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    calibratedProfile κ y ≤ κ * (4 / 27) :=
  mul_le_mul_of_nonneg_left (massWeightedResponse_le hy0 hy1) hκ.le

theorem calibratedProfile_eq_iff {κ y : ℝ} (hκ : 0 < κ)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    calibratedProfile κ y = κ * (4 / 27) ↔ y = 1 / 3 := by
  rw [calibratedProfile, mul_right_inj' hκ.ne']
  exact massWeightedResponse_eq_critical_iff hy0 hy1

theorem common_normalization_matching_iff {κ A c : ℝ}
    (hκ : 0 < κ) (hA : 0 < A) (hc : 0 < c) :
    calibratedResponse κ A c = calibratedProfile κ (1 / 3) ↔ c = endpointRoot A := by
  rw [calibratedResponse, calibratedProfile, massWeightedResponse_oneThird,
    mul_right_inj' hκ.ne']
  simpa only [endpointResidual, sub_eq_zero] using endpointResidual_eq_zero_iff hA hc

theorem common_normalization_unique_endpoint {κ A : ℝ} (hκ : 0 < κ) (hA : 0 < A) :
    ∃! c : ℝ, 0 < c ∧
      calibratedResponse κ A c = calibratedProfile κ (1 / 3) := by
  refine ⟨endpointRoot A, ⟨endpointRoot_pos hA, ?_⟩, ?_⟩
  · exact (common_normalization_matching_iff hκ hA (endpointRoot_pos hA)).2 rfl
  · intro c hc
    exact (common_normalization_matching_iff hκ hA hc.1).1 hc.2

/-- Normalization results exported alongside the finite spectral coefficient.
The endpoint clauses retain the same source calibration on both sides. -/
structure Conclusions : Prop where
  polarization_pairing : ∀ a b c d : ℝ,
    tensorPairing (ttMatrix a b) (ttMatrix c d) = a * c + b * d
  logarithmic_mass_response : ∀ q2 m2 z : ℝ, q2 + Real.exp z * m2 ≠ 0 →
    -(deriv (logMassKernel q2 m2) z) / 2 =
      massWeightedResponse (massFraction q2 (Real.exp z * m2))
  gaussian_response : ∀ (n : ℕ) (q2 m2 : Fin n → ℝ),
    (∀ i, 0 < q2 i + m2 i) →
      gaussianKineticResponse q2 m2 = ∑ i, ttKernel (q2 i) (m2 i)
  partition_response : ∀ (n : ℕ) (q2 m2 : Fin n → ℝ),
    (∀ i, 0 < q2 i + m2 i) →
      HasDerivAt (deriv (kineticLogPartition q2 m2))
        (gaussianKineticResponse q2 m2 / 2) 0
  nonlinear_partition_response : ∀ (n : ℕ) (p v a : ℝ → Fin n → ℝ) (z : ℝ),
    (∀ i, 0 < p z i) →
    (∀ i, HasDerivAt (fun t => p t i) (v z i) z) →
    (∀ i, HasDerivAt (fun t => v t i) (a z i) z) →
      HasDerivAt (fun t => -FinitePrecisionPath.force p v t)
        (Var[FinitePrecisionGaussian.score (v z); FinitePrecisionGaussian.law (p z)] -
          ∫ x, FinitePrecisionGaussian.score (a z) x ∂FinitePrecisionGaussian.law (p z)) z
  common_calibration : ∀ κ A c : ℝ, 0 < κ → 0 < A → 0 < c →
    (calibratedResponse κ A c = calibratedProfile κ (1 / 3) ↔ c = endpointRoot A)
  endpoint_unique : ∀ κ A : ℝ, 0 < κ → 0 < A →
    ∃! c : ℝ, 0 < c ∧ calibratedResponse κ A c = calibratedProfile κ (1 / 3)

theorem generated : Conclusions where
  polarization_pairing := tensorPairing_amplitudes
  logarithmic_mass_response := logMassKernel_response
  gaussian_response := fun _ _ _ => gaussianKineticResponse_eq _ _
  partition_response := fun _ _ _ => kineticLogPartition_second_response _ _
  nonlinear_partition_response := fun _ _ _ _ _ => nonlinear_partition_second_response _ _ _ _
  common_calibration := fun _ _ _ => common_normalization_matching_iff
  endpoint_unique := fun _ _ => common_normalization_unique_endpoint

end GeneratedFoundations.Physical.SourceTTResponseNormalization
