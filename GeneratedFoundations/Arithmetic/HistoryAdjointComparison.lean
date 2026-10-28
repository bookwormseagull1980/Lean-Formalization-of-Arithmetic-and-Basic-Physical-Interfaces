module

public import GeneratedFoundations.Arithmetic.HistoryGaussianCovariance
public import GeneratedFoundations.Geometry.SourceConformalVariation

/-!
# Comparison trace on the actual arithmetic adjoint fibre

The real comparison fibre is the Hermitian traceless space of the original
history--phase/source carrier. Its independent generator count is computed
before any trace is taken. This count is distinct from both the coordinate
count and the Casimir coefficient. No colour multiplicity is imported.

The common-source scalar precision acts identically on these independent
directions. Its tensor trace, compensated finite comparison cost and complete
response therefore acquire exactly this multiplicity. The generated total
intensity remains one. Its balance must consequently use the scalar target
one divided by the actual rank. This is distinct from replicating both a
scalar response and its drive. The response per component is unchanged.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryAdjointComparison

open Geometry.SourceConformalResponse

/-- Real rank of the actual independent Hermitian traceless directions. -/
def multiplicity (N : ℕ) : ℝ :=
  Fintype.card (HistoryHermitianBasis.GeneratorIndex N)

theorem multiplicity_eq (N : ℕ) :
    multiplicity N = ((HistoryAdjointCasimir.dimension N ^ 2 - 1 : ℕ) : ℝ) := by
  rw [multiplicity, HistoryHermitianBasis.generator_count]

theorem multiplicity_pos (N : ℕ) : 0 < multiplicity N := by
  rw [multiplicity_eq]
  apply Nat.cast_pos.mpr
  have hd := HistoryAdjointCasimir.dimension_ge_four N
  have hs : 16 ≤ HistoryAdjointCasimir.dimension N ^ 2 := by nlinarith
  omega

theorem multiplicity_lower (N : ℕ) : (15 : ℝ) ≤ multiplicity N := by
  rw [multiplicity_eq]
  have hd := HistoryAdjointCasimir.dimension_ge_four N
  have hs : 16 ≤ HistoryAdjointCasimir.dimension N ^ 2 := by nlinarith
  have h : 15 ≤ HistoryAdjointCasimir.dimension N ^ 2 - 1 := by omega
  exact_mod_cast h

/-- The connection coefficient count also includes the actual coordinate
directions. That additional factor is not part of the adjoint trace. -/
theorem coefficientCount_eq (N : ℕ) :
    (HistoryGaussianCovariance.componentCount N : ℝ) =
      Fintype.card (HistoryGaugeJets.CoordinateIndex N) * multiplicity N := by
  simp only [HistoryGaussianCovariance.componentCount,
    HistoryResponseCertificates.coefficientCount, Nat.cast_mul, multiplicity]

theorem sum_components (N : ℕ) {ι : Type*} [Fintype ι] (e : ι → ℝ) :
    (∑ p : ι × HistoryHermitianBasis.GeneratorIndex N, e p.1) =
      multiplicity N * ∑ j : ι, e j := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa only [multiplicity] using
    (Finset.mul_sum (Finset.univ : Finset ι) e
      (Fintype.card (HistoryHermitianBasis.GeneratorIndex N) : ℝ)).symm

/-- Ordinary trace of the scalar spectral block tensored with every
independent arithmetic adjoint direction. -/
theorem trace_diagonal (N : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) :
    Matrix.trace (Matrix.diagonal
      (fun p : ι × HistoryHermitianBasis.GeneratorIndex N => e p.1)) =
      multiplicity N * Matrix.trace (Matrix.diagonal e) := by
  rw [Matrix.trace_diagonal, Matrix.trace_diagonal]
  exact sum_components N e

/-- Reference-subtracted Gaussian comparison on the full finite tensor
fibre, with the same scalar precision in every independent direction. -/
theorem finite_comparison (N : ℕ) {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (g q : ℝ) :
    (∑ p : ι × HistoryHermitianBasis.GeneratorIndex N,
      (g * q / a p.1 - Real.log (1 + g * q / a p.1))) =
      multiplicity N *
        ∑ j : ι, (g * q / a j - Real.log (1 + g * q / a j)) :=
  sum_components N (fun j => g * q / a j - Real.log (1 + g * q / a j))

def response (N : ℕ) (z : ℝ) : ℝ := multiplicity N * completeResponse z

def curvature (N : ℕ) (z : ℝ) : ℝ := multiplicity N * completeCurvature z

/-- The complete scalar tower and the actual finite adjoint trace agree
before any estimate on the shell response. -/
theorem complete_response_trace (N : ℕ) (z : ℝ) :
    (∑' j, ∑ _a : HistoryHermitianBasis.GeneratorIndex N, responseTerm j z) =
      response N z := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    tsum_mul_left, response, multiplicity, completeResponse]

theorem complete_curvature_trace (N : ℕ) (z : ℝ) :
    (∑' j, ∑ _a : HistoryHermitianBasis.GeneratorIndex N, curvatureTerm j z) =
      curvature N z := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    tsum_mul_left, curvature, multiplicity, completeCurvature]

theorem response_hasDerivAt (N : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (response N) (curvature N z) z :=
  (Geometry.SourceConformalVariation.completeResponse_hasDerivAt hz).const_mul
    (multiplicity N)

theorem curvature_pos (N : ℕ) {z : ℝ} (hz : 0 ≤ z) : 0 < curvature N z :=
  mul_pos (multiplicity_pos N) (completeCurvature_pos hz)

/-- Replication has not supplied another scalar source normalization. -/
theorem response_per_component (N : ℕ) (z : ℝ) :
    response N z / multiplicity N = completeResponse z := by
  unfold response
  exact mul_div_cancel_left₀ _ (multiplicity_pos N).ne'

/-- Per-component target obtained from the actual total source intensity. -/
def target (N : ℕ) : ℝ :=
  HistoryGaussianCovariance.generatedIntensity N / multiplicity N

theorem target_pos (N : ℕ) : 0 < target N :=
  div_pos (HistoryGaussianCovariance.generatedIntensity_pos N) (multiplicity_pos N)

theorem target_eq (N : ℕ) : target N = 1 / multiplicity N := by
  rw [target, HistoryGaussianCovariance.generatedIntensity_eq]

theorem target_upper (N : ℕ) : target N ≤ (1 / 15 : ℝ) := by
  rw [target_eq]
  apply (div_le_div_iff₀ (multiplicity_pos N) (by norm_num : (0 : ℝ) < 15)).mpr
  simpa only [one_mul] using multiplicity_lower N

/-- The full comparison balance is selected by its computed rank and the
already generated source intensity, with no independent target input. -/
def amplitude (N : ℕ) : ℝ :=
  Classical.choose (existsUnique_completeResponse_root (target_pos N))

theorem amplitude_spec (N : ℕ) :
    0 < amplitude N ∧ completeResponse (amplitude N) = target N :=
  (Classical.choose_spec (existsUnique_completeResponse_root (target_pos N))).1

theorem amplitude_unique (N : ℕ) {z : ℝ} (hz : 0 < z)
    (hr : completeResponse z = target N) : z = amplitude N :=
  (Classical.choose_spec (existsUnique_completeResponse_root (target_pos N))).2 z ⟨hz, hr⟩

/-- A single total source unit does not select the scalar unit-per-component
balance. Their strict ordering follows from the actual rank lower bound. -/
theorem amplitude_lt_scalar (N : ℕ) : amplitude N < canonicalAmplitude := by
  by_contra h
  have hle : canonicalAmplitude ≤ amplitude N := le_of_not_gt h
  have hr := completeResponse_strictMonoOn.monotoneOn
    canonicalAmplitude_spec.1.le (amplitude_spec N).1.le hle
  rw [canonicalAmplitude_spec.2, (amplitude_spec N).2] at hr
  have ht := target_upper N
  norm_num only [canonicalDrive] at hr
  linarith

/-- Reference-subtracted full comparison potential. The affine term keeps
one total source intensity instead of replicating the scalar drive. -/
def potential (N : ℕ) (z : ℝ) : ℝ :=
  multiplicity N * (Geometry.SourceConformalVariation.potential z -
    Geometry.SourceConformalVariation.potential (amplitude N)) +
    (multiplicity N * canonicalDrive - HistoryGaussianCovariance.generatedIntensity N) *
      (z - amplitude N)

def force (N : ℕ) (z : ℝ) : ℝ :=
  response N z - HistoryGaussianCovariance.generatedIntensity N

@[simp] theorem potential_amplitude (N : ℕ) : potential N (amplitude N) = 0 := by
  simp [potential]

theorem potential_hasDerivAt (N : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (potential N) (force N z) z := by
  have h := (((Geometry.SourceConformalVariation.potential_hasDerivAt hz).sub_const
    (Geometry.SourceConformalVariation.potential (amplitude N))).const_mul
      (multiplicity N)).add
    (((hasDerivAt_id z).sub_const (amplitude N)).const_mul
      (multiplicity N * canonicalDrive - HistoryGaussianCovariance.generatedIntensity N))
  convert! h using 1
  simp only [force, response, mul_one]
  ring

theorem force_hasDerivAt (N : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (force N) (curvature N z) z :=
  (response_hasDerivAt N hz).sub_const (HistoryGaussianCovariance.generatedIntensity N)

theorem potential_secondDeriv (N : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t : ℝ => deriv (potential N) t) (curvature N z) z := by
  apply (force_hasDerivAt N hz).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
  exact (potential_hasDerivAt N ht).deriv

/-- The stationary amplitude uses the one total source intensity. The
positive adjoint rank is divided out only after the full trace is formed. -/
theorem stationary_iff_amplitude (N : ℕ) {z : ℝ} (hz : 0 < z) :
    deriv (potential N) z = 0 ↔ z = amplitude N := by
  rw [(potential_hasDerivAt N hz).deriv]
  simp only [force, response, sub_eq_zero]
  rw [mul_comm (multiplicity N), ← eq_div_iff (multiplicity_pos N).ne']
  change completeResponse z = target N ↔ z = amplitude N
  constructor
  · exact amplitude_unique N hz
  · intro h
    subst z
    exact (amplitude_spec N).2

theorem existsUnique_stationary (N : ℕ) :
    ∃! z : ℝ, 0 < z ∧ deriv (potential N) z = 0 := by
  refine ⟨amplitude N, ⟨(amplitude_spec N).1,
    (stationary_iff_amplitude N (amplitude_spec N).1).2 rfl⟩, ?_⟩
  intro z hz
  exact (stationary_iff_amplitude N hz.1).1 hz.2

structure Conclusions : Prop where
  actual_rank : ∀ N,
    multiplicity N = ((HistoryAdjointCasimir.dimension N ^ 2 - 1 : ℕ) : ℝ)
  positive_rank : ∀ N, 0 < multiplicity N
  full_finite_trace : ∀ N {ι : Type} [Fintype ι] (e : ι → ℝ),
    (∑ p : ι × HistoryHermitianBasis.GeneratorIndex N, e p.1) =
      multiplicity N * ∑ j : ι, e j
  complete_response : ∀ N z,
    (∑' j, ∑ _a : HistoryHermitianBasis.GeneratorIndex N, responseTerm j z) =
      response N z
  actual_derivative : ∀ N z, 0 < z →
    HasDerivAt (response N) (curvature N z) z
  actual_second_derivative : ∀ N z, 0 < z →
    HasDerivAt (fun t : ℝ => deriv (potential N) t) (curvature N z) z
  positive_curvature : ∀ N z, 0 ≤ z → 0 < curvature N z
  actual_total_intensity : ∀ N, target N = 1 / multiplicity N
  unique_generated_amplitude : ∀ N,
    ∃! z : ℝ, 0 < z ∧ deriv (potential N) z = 0

theorem generated : Conclusions where
  actual_rank := multiplicity_eq
  positive_rank := multiplicity_pos
  full_finite_trace := sum_components
  complete_response := complete_response_trace
  actual_derivative := fun N _ hz => response_hasDerivAt N hz
  actual_second_derivative := fun N _ hz => potential_secondDeriv N hz
  positive_curvature := fun N _ hz => curvature_pos N hz
  actual_total_intensity := target_eq
  unique_generated_amplitude := existsUnique_stationary

end GeneratedFoundations.Arithmetic.HistoryAdjointComparison
