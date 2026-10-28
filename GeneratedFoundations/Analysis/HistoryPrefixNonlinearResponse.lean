module

public import GeneratedFoundations.Analysis.HistoryPrefixMobiusResponse
public import GeneratedFoundations.Operations.GibbsFullResponse

/-!
# Finite observations of the complete Gaussian prefix

Every reference intensity still belongs to the original root, history and
phase source. An observation is a direction in its matrix algebra. The full
connected Hessian is computed at every finite Hermitian observation, rather
than only at zero. In the diagonal case its probabilities are the original
positive intensities multiplied by their exact exponential likelihoods.

The occupation center, square-free support and Mobius probe are evaluated in
that same state. Their mixed curvatures are retained. Positivity is strict
for every nonconstant diagonal direction at each finite observation; it
does not require a balanced reference state.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix.Norms.Operator

namespace GeneratedFoundations.Analysis.HistoryPrefixNonlinearResponse

open Operations Operations.PreparedTraceForm
open GibbsExponentialDifferentiation (realDiagonal)
open HistoryPrefixGibbsResponse
open HistoryPrefixMobiusResponse (probe support probe_square support_square probe_mul_support)

/-- The complete matrix Hessian at any finite observation. Both directions
are transported by the same spectral unitary, so their mixed terms remain. -/
theorem full_hessian (N : ℕ) (alpha L : ℝ) (B K J : Hermitian (Index N)) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) B K J =
      GibbsTraceForm.gibbsForm (GibbsFullResponse.spectralValues _ (logIntensity N alpha L) B)
        (GibbsFullResponse.pullback _
          (GibbsFullResponse.spectralUnitary _ (logIntensity N alpha L) B) K : Mat (Index N))
        (GibbsFullResponse.pullback _
          (GibbsFullResponse.spectralUnitary _ (logIntensity N alpha L) B) J : Mat (Index N)) :=
  GibbsFullResponse.hessian_spectral _ _ B K J

theorem hessian_nonneg (N : ℕ) (alpha L : ℝ) (B K : Hermitian (Index N)) :
    0 ≤ fderiv ℝ (fderiv ℝ (response N alpha L)) B K K :=
  GibbsFullResponse.hessian_nonneg _ _ B K

theorem hessian_kernel (N : ℕ) (alpha L : ℝ) (B K : Hermitian (Index N)) :
    (∀ J : Hermitian (Index N), fderiv ℝ (fderiv ℝ (response N alpha L)) B K J = 0) ↔
      ∃ r : ℝ, (K : Mat (Index N)) = r • (1 : Mat (Index N)) :=
  GibbsFullResponse.hessian_kernel _ _ B K

theorem hessian_positive (N : ℕ) (alpha L : ℝ) (B : Hermitian (Index N))
    (K : Traceless (Index N)) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response N alpha L)) B K.val K.val :=
  GibbsFullResponse.hessian_traceless_pos _ _ B K hK

def tiltedLog (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) (i : Index N) : ℝ :=
  logIntensity N alpha L i + f i

def tiltedProbability (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) (i : Index N) : ℝ :=
  Real.exp (tiltedLog N alpha L f i) / GibbsTraceForm.Z (tiltedLog N alpha L f)

def tiltedMean (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ) : ℝ :=
  ∑ i, tiltedProbability N alpha L f i * g i

theorem exp_tiltedLog (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) (i : Index N) :
    Real.exp (tiltedLog N alpha L f i) = intensity N alpha L i * Real.exp (f i) := by
  rw [tiltedLog, Real.exp_add, exp_logIntensity]

theorem tiltedProbability_pos (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) (i : Index N) :
    0 < tiltedProbability N alpha L f i :=
  div_pos (Real.exp_pos _) (GibbsTraceForm.Z_pos _)

theorem tiltedProbability_total (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    (∑ i, tiltedProbability N alpha L f i) = 1 := by
  simp only [tiltedProbability, ← Finset.sum_div]
  exact div_self (GibbsTraceForm.Z_ne_zero _)

/-- A root observation preserves the generated conditional law on its
entire history--phase fibre. Its root weight changes by its exact likelihood. -/
theorem tiltedProbability_root_marginal (N : ℕ) (alpha L : ℝ)
    (f : Fin (N + 1) → ℝ) (b : Fin (N + 1)) :
    (∑ x : Arithmetic.HistoryPhaseBundle.Fiber b.val,
      tiltedProbability N alpha L (fun i => f i.1) ⟨b, x⟩) =
        Arithmetic.CompleteHistory.gaussianRootMass alpha L (b.val + 1) * Real.exp (f b) /
          GibbsTraceForm.Z (tiltedLog N alpha L (fun i => f i.1)) := by
  simp only [tiltedProbability, exp_tiltedLog, intensity, HistoryPhaseResponse.intensity,
    ← Finset.sum_div]
  have hs : (∑ x : Arithmetic.HistoryPhaseBundle.Fiber b.val,
      Arithmetic.CompleteHistory.gaussianRootMass alpha L (b.val + 1) *
        Arithmetic.HistoryPhaseBundle.probability x * Real.exp (f b)) =
      Arithmetic.CompleteHistory.gaussianRootMass alpha L (b.val + 1) * Real.exp (f b) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum, Arithmetic.HistoryPhaseBundle.probability_total,
      mul_one]
  rw [hs]

@[simp] theorem tiltedMean_one (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    tiltedMean N alpha L f (fun _ => 1) = 1 := by
  simpa only [tiltedMean, mul_one] using tiltedProbability_total N alpha L f

theorem diagonal_base (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    GibbsFullResponse.base _ (logIntensity N alpha L) (diagonalObservation f) =
      realDiagonal (tiltedLog N alpha L f) := by
  change realDiagonal (logIntensity N alpha L) + realDiagonal f = _
  ext i j
  by_cases hij : i = j
  · subst j
    simp [realDiagonal, tiltedLog]
  · simp [realDiagonal, hij]

theorem tilted_partition (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    GibbsTraceDifferentiation.partition _ (logIntensity N alpha L) (diagonalObservation f) =
      ∑ i, intensity N alpha L i * Real.exp (f i) := by
  change realTrace _ (NormedSpace.exp (GibbsFullResponse.base _ _ _)) = _
  rw [diagonal_base]
  have hp := GibbsConnectedResponse.partition_zero (Index N) (tiltedLog N alpha L f)
  change realTrace _ (NormedSpace.exp (realDiagonal _ + 0)) = _ at hp
  rw [add_zero] at hp
  rw [hp]
  simp only [GibbsTraceForm.Z, exp_tiltedLog]

theorem partition_eq_tiltedZ (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    GibbsTraceDifferentiation.partition _ (logIntensity N alpha L) (diagonalObservation f) =
      GibbsTraceForm.Z (tiltedLog N alpha L f) := by
  rw [tilted_partition]
  simp only [GibbsTraceForm.Z, exp_tiltedLog]

/-- A diagonal observation changes the likelihood, not the generated
reference source. At zero likelihood it returns the original probabilities. -/
@[simp] theorem tiltedProbability_zero (N : ℕ) (alpha L : ℝ) (i : Index N) :
    tiltedProbability N alpha L (fun _ => 0) i = probability N alpha L i := by
  have hz : tiltedLog N alpha L (fun _ => 0) = logIntensity N alpha L := by
    funext j
    simp [tiltedLog]
  simp only [tiltedProbability, hz, exp_logIntensity, probability]

@[simp] theorem tiltedMean_zero (N : ℕ) (alpha L : ℝ) (g : Index N → ℝ) :
    tiltedMean N alpha L (fun _ => 0) g = mean N alpha L g := by
  simp only [tiltedMean, tiltedProbability_zero, mean]

theorem diagonal_hessian (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ)
    (K J : Hermitian (Index N)) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f) K J =
      GibbsTraceForm.gibbsForm (tiltedLog N alpha L f)
        (K : Mat (Index N)) (J : Mat (Index N)) := by
  change fderiv ℝ (fderiv ℝ (GibbsConnectedResponse.response (Index N)
    (logIntensity N alpha L))) (diagonalObservation f) K J = _
  rw [GibbsFullResponse.full_hessian, diagonal_base, partition_eq_tiltedZ,
    GibbsExponentialDifferentiation.expDerivative_realDiagonal,
    GibbsExponentialDifferentiation.exp_realDiagonal]
  simp only [GibbsTraceForm.gibbsForm_apply, GibbsTraceForm.mean_apply]
  rfl

theorem tilted_diagonal_mean (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ) :
    GibbsTraceForm.mean (tiltedLog N alpha L f)
      (diagonalObservation g : Mat (Index N)) = tiltedMean N alpha L f g := by
  rw [GibbsTraceForm.mean_apply, GibbsTraceForm.weightedTrace_eq_sum]
  simp only [diagonalObservation, realDiagonal, Matrix.diagonal_apply_eq,
    Complex.ofReal_re, Finset.sum_div, tiltedMean, tiltedProbability]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gradient_at_diagonal (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ) :
    fderiv ℝ (response N alpha L) (diagonalObservation f) (diagonalObservation g) =
      tiltedMean N alpha L f g := by
  change fderiv ℝ (GibbsConnectedResponse.response (Index N) (logIntensity N alpha L))
    (diagonalObservation f) (diagonalObservation g) = _
  rw [GibbsConnectedResponse.response_fderiv, partition_eq_tiltedZ,
    GibbsTraceDifferentiation.partition_fderiv]
  change (GibbsTraceForm.Z (tiltedLog N alpha L f))⁻¹ *
    realTrace _ (NormedSpace.exp (GibbsFullResponse.base _ _ _) *
      (diagonalObservation g : Mat (Index N))) = _
  rw [diagonal_base, GibbsExponentialDifferentiation.exp_realDiagonal]
  exact tilted_diagonal_mean N alpha L f g

theorem hessian_covariance (N : ℕ) (alpha L : ℝ) (f g h : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation g) (diagonalObservation h) =
        tiltedMean N alpha L f (fun i => g i * h i) -
          tiltedMean N alpha L f g * tiltedMean N alpha L f h := by
  rw [diagonal_hessian]
  change GibbsTraceForm.responsePairing (tiltedLog N alpha L f)
      (diagonalObservation g : Mat (Index N)) (diagonalObservation h : Mat (Index N)) /
        GibbsTraceForm.Z (tiltedLog N alpha L f) - _ = _
  rw [tilted_diagonal_mean, tilted_diagonal_mean]
  congr 1
  rw [GibbsTraceForm.responsePairing_eq_sum]
  have hs : (∑ i : Index N, ∑ j : Index N,
      GibbsExponentialDifferentiation.expDividedDifference
        (tiltedLog N alpha L f i) (tiltedLog N alpha L f j) *
          ((diagonalObservation g : Mat (Index N)) i j *
            (diagonalObservation h : Mat (Index N)) j i).re) =
      ∑ i, Real.exp (tiltedLog N alpha L f i) * (g i * h i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single i]
    · simp [diagonalObservation, realDiagonal,
        GibbsExponentialDifferentiation.expDividedDifference_self]
    · intro j _ hji
      simp [diagonalObservation, realDiagonal, hji, Ne.symm hji]
    · simp
  rw [hs, Finset.sum_div]
  simp only [tiltedMean, tiltedProbability]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every finite likelihood has exactly the same scalar degeneracy.
No assumption about the reference center mean is used. -/
theorem diagonal_variance_zero_iff (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation g) (diagonalObservation g) = 0 ↔ ∃ r : ℝ, ∀ i, g i = r := by
  change fderiv ℝ (fderiv ℝ (GibbsConnectedResponse.response (Index N)
    (logIntensity N alpha L))) (diagonalObservation f)
      (diagonalObservation g) (diagonalObservation g) = 0 ↔ _
  rw [GibbsFullResponse.hessian_self_zero_iff]
  apply exists_congr
  intro r
  constructor
  · intro h i
    have hi := congrArg (fun K : Mat (Index N) => (K i i).re) h
    simpa only [diagonalObservation, realDiagonal, Matrix.diagonal_apply_eq,
      Complex.ofReal_re, Matrix.smul_apply, Matrix.one_apply_eq, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re,
      Complex.one_im, mul_one, mul_zero, sub_zero] using hi
  · intro h
    ext i j
    by_cases hij : i = j
    · subst j
      simp [diagonalObservation, realDiagonal, h i]
    · simp [diagonalObservation, realDiagonal, hij]

theorem diagonal_variance_pos (N : ℕ) (alpha L : ℝ) (f g : Index N → ℝ)
    (hg : ¬ ∃ r : ℝ, ∀ i, g i = r) :
    0 < fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation g) (diagonalObservation g) := by
  refine lt_of_le_of_ne (hessian_nonneg N alpha L _ _) ?_
  intro hz
  exact hg ((diagonal_variance_zero_iff N alpha L f g).mp hz.symm)

theorem probe_nonconstant (N : ℕ) (hN : 1 ≤ N) :
    ¬ ∃ r : ℝ, ∀ i : Index N, probe N i = r := by
  let i₁ : Index N := ⟨⟨0, by omega⟩, Arithmetic.HistoryModuleRepresentation.base 0⟩
  let i₂ : Index N := ⟨⟨1, by omega⟩, Arithmetic.HistoryModuleRepresentation.base 1⟩
  have h₁ : probe N i₁ = 1 := by
    simp [probe, i₁, GeneratedMobiusObservation.generatedMoebius_eq_moebius]
  have h₂ : probe N i₂ = -1 := by
    simp [probe, i₂, GeneratedMobiusObservation.generatedMoebius_eq_moebius,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  rintro ⟨r, hr⟩
  have h₁r := hr i₁
  have h₂r := hr i₂
  rw [h₁] at h₁r
  rw [h₂] at h₂r
  linarith

/-- The unit and first prime are already present in every prefix with at
least two roots. Their opposite native signs make its probe curvature
strictly positive at every finite diagonal observation. -/
theorem probe_curvature_pos (N : ℕ) (hN : 1 ≤ N) (alpha L : ℝ) (f : Index N → ℝ) :
    0 < fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation (probe N)) (diagonalObservation (probe N)) :=
  diagonal_variance_pos N alpha L f (probe N) (probe_nonconstant N hN)

theorem centre_curvature (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation (centre N)) (diagonalObservation (centre N)) =
        1 - (tiltedMean N alpha L f (centre N)) ^ 2 := by
  rw [hessian_covariance]
  simp only [centre_square, tiltedMean_one, pow_two]

theorem probe_curvature (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation (probe N)) (diagonalObservation (probe N)) =
        tiltedMean N alpha L f (support N) -
          (tiltedMean N alpha L f (probe N)) ^ 2 := by
  rw [hessian_covariance]
  simp only [probe_square, pow_two]

theorem support_curvature (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation (support N)) (diagonalObservation (support N)) =
        tiltedMean N alpha L f (support N) * (1 - tiltedMean N alpha L f (support N)) := by
  rw [hessian_covariance]
  simp only [support_square]
  ring

theorem probe_support_curvature (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation (probe N)) (diagonalObservation (support N)) =
        tiltedMean N alpha L f (probe N) * (1 - tiltedMean N alpha L f (support N)) := by
  rw [hessian_covariance]
  simp only [probe_mul_support]
  ring

structure Conclusions : Prop where
  full_curvature : ∀ (N : ℕ) (alpha L : ℝ) (B K : Hermitian (Index N)),
    0 ≤ fderiv ℝ (fderiv ℝ (response N alpha L)) B K K
  scalar_kernel : ∀ (N : ℕ) (alpha L : ℝ) (B K : Hermitian (Index N)),
    (∀ J : Hermitian (Index N), fderiv ℝ (fderiv ℝ (response N alpha L)) B K J = 0) ↔
      ∃ r : ℝ, (K : Mat (Index N)) = r • (1 : Mat (Index N))
  finite_likelihood : ∀ (N : ℕ) (alpha L : ℝ) (f : Index N → ℝ),
    GibbsTraceDifferentiation.partition _ (logIntensity N alpha L) (diagonalObservation f) =
      ∑ i, intensity N alpha L i * Real.exp (f i)
  complete_covariance : ∀ (N : ℕ) (alpha L : ℝ) (f g h : Index N → ℝ),
    fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation g) (diagonalObservation h) =
        tiltedMean N alpha L f (fun i => g i * h i) -
          tiltedMean N alpha L f g * tiltedMean N alpha L f h
  actual_probe_positive : ∀ (N : ℕ), 1 ≤ N → ∀ (alpha L : ℝ) (f : Index N → ℝ),
    0 < fderiv ℝ (fderiv ℝ (response N alpha L)) (diagonalObservation f)
      (diagonalObservation (probe N)) (diagonalObservation (probe N))

theorem generated : Conclusions where
  full_curvature := hessian_nonneg
  scalar_kernel := hessian_kernel
  finite_likelihood := tilted_partition
  complete_covariance := hessian_covariance
  actual_probe_positive := probe_curvature_pos

end GeneratedFoundations.Analysis.HistoryPrefixNonlinearResponse
