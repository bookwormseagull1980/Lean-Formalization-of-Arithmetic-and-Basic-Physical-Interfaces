module

public import GeneratedFoundations.Analysis.HistoryPrefixResponseReduction
public import GeneratedFoundations.Analysis.CenterEndpointPotential

/-!
# The intrinsic square-free probe in the full positive prefix state

The state remains the actual positive Gaussian law on every root, history
and phase. The native square-free projector is an observation on this law,
not a replacement source. The generated Mobius probe is the intrinsic
occupation center times that projector. Its square is the projector, so
its fluctuation differs from that of a two-valued center on the full carrier.

The mixed Hessian with the support observation and its exact Schur return
are calculated below. The Gaussian capacity factors are then restored to
the original complete signed amplitude. In particular the two endpoint
responses are combined before squaring.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryPrefixMobiusResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open GeneratedMobiusObservation GeneratedCentralCharacter
open HistoryPrefixGibbsResponse

def probe (N : ℕ) (i : Index N) : ℝ :=
  (generatedMoebius (i.1.val + 1) : ℝ)

def support (N : ℕ) (i : Index N) : ℝ :=
  (squarefreeProjector (i.1.val + 1) : ℝ)

theorem probe_eq_centre_mul_support (N : ℕ) (i : Index N) :
    probe N i = centre N i * support N i := by
  simp [probe, support, generatedMoebius, centreCharacter,
    Arithmetic.GeneratedPrimeParity.rootCentre, centre]

theorem probe_square (N : ℕ) (i : Index N) :
    probe N i * probe N i = support N i := by
  unfold probe support
  have h := generatedMoebius_sq (i.1.val + 1)
  exact_mod_cast (show generatedMoebius (i.1.val + 1) *
      generatedMoebius (i.1.val + 1) = squarefreeProjector (i.1.val + 1) by
    simpa only [pow_two] using h)

theorem support_cases (N : ℕ) (i : Index N) : support N i = 0 ∨ support N i = 1 := by
  by_cases h : GeneratedSquarefree (i.1.val + 1) <;> simp [support, squarefreeProjector, h]

theorem support_square (N : ℕ) (i : Index N) :
    support N i * support N i = support N i := by
  rcases support_cases N i with h | h <;> simp [h]

theorem probe_mul_support (N : ℕ) (i : Index N) :
    probe N i * support N i = probe N i := by
  rw [probe_eq_centre_mul_support, mul_assoc, support_square]

def signedMean (N : ℕ) (alpha L : ℝ) : ℝ := mean N alpha L (probe N)
def supportFraction (N : ℕ) (alpha L : ℝ) : ℝ := mean N alpha L (support N)

theorem supportFraction_nonneg (N : ℕ) (alpha L : ℝ) :
    0 ≤ supportFraction N alpha L := by
  apply Finset.sum_nonneg
  intro i _
  apply mul_nonneg (probability_pos N alpha L i).le
  rcases support_cases N i with h | h <;> simp [h]

/-- The unit root belongs to every prefix and has strictly positive source
weight. Positivity of the intrinsic support needs no additional assumption. -/
theorem supportFraction_pos (N : ℕ) (alpha L : ℝ) :
    0 < supportFraction N alpha L := by
  let i : Index N := ⟨⟨0, by omega⟩, HistoryModuleRepresentation.base 0⟩
  have hi : support N i = 1 := by
    have hs : GeneratedSquarefree 1 :=
      generatedSquarefree_iff_squarefree.mpr (by simp)
    simp [support, i, squarefreeProjector_of_generatedSquarefree hs]
  apply Finset.sum_pos'
  · intro j _
    apply mul_nonneg (probability_pos N alpha L j).le
    rcases support_cases N j with h | h <;> simp [h]
  · exact ⟨i, Finset.mem_univ _, by simpa [hi] using probability_pos N alpha L i⟩

theorem supportFraction_le_one (N : ℕ) (alpha L : ℝ) :
    supportFraction N alpha L ≤ 1 := by
  rw [← mean_one N alpha L]
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_of_nonneg_left _ (probability_pos N alpha L i).le
  rcases support_cases N i with h | h <;> simp [h]

/-- The original source's support capacity occurs in the fluctuation;
it is not replaced by one. -/
theorem probe_hessian (N : ℕ) (alpha L : ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (probe N)) (diagonalObservation (probe N)) =
        supportFraction N alpha L - (signedMean N alpha L) ^ 2 := by
  rw [hessian_covariance]
  simp only [probe_square, supportFraction, signedMean, pow_two]

theorem support_hessian (N : ℕ) (alpha L : ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (support N)) (diagonalObservation (support N)) =
        supportFraction N alpha L * (1 - supportFraction N alpha L) := by
  rw [hessian_covariance]
  simp only [support_square, supportFraction]
  ring

theorem probe_support_hessian (N : ℕ) (alpha L : ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (probe N)) (diagonalObservation (support N)) =
        signedMean N alpha L * (1 - supportFraction N alpha L) := by
  rw [hessian_covariance]
  simp only [probe_mul_support, supportFraction, signedMean]
  ring

theorem signedMean_sq_le_supportFraction (N : ℕ) (alpha L : ℝ) :
    (signedMean N alpha L) ^ 2 ≤ supportFraction N alpha L := by
  have h := hessian_nonneg N alpha L (diagonalObservation (probe N))
  rw [probe_hessian] at h
  linarith

open HistoryPrefixResponseReduction (form residual)

/-- Exact support-conditioned Schur response. The removed square remains
in the prefix reduction identity. Degenerate support directions are treated
by the scalar-kernel theorem rather than by an inverse. -/
private theorem support_schur_response_of_ne_one (N : ℕ) (alpha L : ℝ)
    (hs : supportFraction N alpha L ≠ 0)
    (hc : supportFraction N alpha L ≠ 1) :
    form N alpha L
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N)))
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N))) =
      supportFraction N alpha L -
        (signedMean N alpha L) ^ 2 / supportFraction N alpha L := by
  have h := HistoryPrefixResponseReduction.schur_identity alpha L
    (diagonalObservation (probe N)) (diagonalObservation (support N))
  have hMM : form N alpha L (diagonalObservation (probe N))
      (diagonalObservation (probe N)) = supportFraction N alpha L -
        (signedMean N alpha L) ^ 2 := by rw [HistoryPrefixResponseReduction.form_hessian, probe_hessian]
  have hMS : form N alpha L (diagonalObservation (probe N))
      (diagonalObservation (support N)) =
        signedMean N alpha L * (1 - supportFraction N alpha L) := by
    rw [HistoryPrefixResponseReduction.form_hessian, probe_support_hessian]
  have hSS : form N alpha L (diagonalObservation (support N))
      (diagonalObservation (support N)) =
        supportFraction N alpha L * (1 - supportFraction N alpha L) := by
    rw [HistoryPrefixResponseReduction.form_hessian, support_hessian]
  rw [hMM, hMS, hSS] at h
  have hc' : 1 - supportFraction N alpha L ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  have he : supportFraction N alpha L - (signedMean N alpha L) ^ 2 -
      (signedMean N alpha L * (1 - supportFraction N alpha L)) ^ 2 /
        (supportFraction N alpha L * (1 - supportFraction N alpha L)) =
      supportFraction N alpha L -
        (signedMean N alpha L) ^ 2 / supportFraction N alpha L := by
    field_simp [hs, hc']
    ring
  linarith

/-- Complete support reduction, including the scalar support direction.
All nondegeneracy facts are obtained from the actual generated prefix. -/
theorem support_schur_response (N : ℕ) (alpha L : ℝ) :
    form N alpha L
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N)))
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N))) =
      supportFraction N alpha L -
        (signedMean N alpha L) ^ 2 / supportFraction N alpha L := by
  by_cases hc : supportFraction N alpha L = 1
  · have hSS : form N alpha L (diagonalObservation (support N))
        (diagonalObservation (support N)) = 0 := by
      rw [HistoryPrefixResponseReduction.form_hessian, support_hessian, hc]
      ring
    simp only [HistoryPrefixResponseReduction.residual,
      HistoryPrefixResponseReduction.coefficient, hSS,
      div_zero, zero_smul, sub_zero]
    rw [HistoryPrefixResponseReduction.form_hessian, probe_hessian, hc, div_one]
  · exact support_schur_response_of_ne_one N alpha L
      (supportFraction_pos N alpha L).ne' hc

/-- The support-conditioned center imbalance retains its actual capacity. -/
theorem signedMean_sq_le_supportFraction_sq (N : ℕ) (alpha L : ℝ) :
    (signedMean N alpha L) ^ 2 ≤ (supportFraction N alpha L) ^ 2 := by
  have hn := HistoryPrefixResponseReduction.form_nonneg N alpha L
    (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N)))
  rw [support_schur_response] at hn
  have hh : (signedMean N alpha L) ^ 2 / supportFraction N alpha L ≤
      supportFraction N alpha L := by linarith
  have h := (div_le_iff₀ (supportFraction_pos N alpha L)).mp hh
  simpa only [pow_two] using h

theorem support_full_mixed_zero (N : ℕ) (alpha L : ℝ)
    (hs : supportFraction N alpha L = 1) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (probe N)) (diagonalObservation (support N)) = 0 := by
  rw [probe_support_hessian, hs]
  ring

private theorem sum_positive_roots (N : ℕ) (f : ℕ → ℝ) :
    (∑ b : Fin (N + 1), f (b.val + 1)) = ∑ n ∈ SignedGaussianEnergy.rootRange (N + 1), f n := by
  classical
  refine Finset.sum_bij (fun b _ => b.val + 1) ?_ ?_ ?_ ?_
  · intro b _
    simp only [SignedGaussianEnergy.rootRange, Finset.mem_Icc]
    have hb := b.isLt
    omega
  · intro a _ b _ hab
    apply Fin.ext
    omega
  · intro n hn
    simp only [SignedGaussianEnergy.rootRange, Finset.mem_Icc] at hn
    refine ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro b _
    rfl

/-- Restoring the actual Gaussian partition recovers the original signed
root amplitude, with the unit root retained. -/
theorem weighted_mean_eq_root_amplitude (N : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) * signedMean N alpha L =
      SignedGaussianEnergy.rootSignedAmplitude alpha L (N + 1) := by
  have h := mean_root_observation N alpha L
    (fun b => (generatedMoebius (b.val + 1) : ℝ))
  change signedMean N alpha L = _ at h
  rw [h]
  have hz := GibbsTraceForm.Z_ne_zero (logIntensity N alpha L)
  rw [mul_div_cancel₀ _ hz]
  rw [sum_positive_roots N (fun n => gaussianRootMass alpha L n * (generatedMoebius n : ℝ))]
  apply Finset.sum_congr rfl
  intro n _
  simp only [SignedGaussianEnergy.rootSignedMass]
  ring

/-- The projected support is measured in the original state; its capacity
is recovered by restoring the same full-source partition. -/
theorem weighted_support_eq_root_capacity (N : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) * supportFraction N alpha L =
      CenterEndpointPotential.finiteSupportCapacity (gaussianRootMass alpha L) (N + 1) := by
  have h := mean_root_observation N alpha L
    (fun b => (squarefreeProjector (b.val + 1) : ℝ))
  change supportFraction N alpha L = _ at h
  rw [h, mul_div_cancel₀ _ (GibbsTraceForm.Z_ne_zero (logIntensity N alpha L))]
  rw [sum_positive_roots N (fun n => gaussianRootMass alpha L n * (squarefreeProjector n : ℝ))]
  apply Finset.sum_congr rfl
  intro n _
  ring

/-- The exact reduced Hessian recovers the existing transverse support
capacity. Both full-source and support capacities retain their original
Gaussian weights. -/
theorem restored_schur_response (N : ℕ) (alpha L : ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) *
      form N alpha L
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N)))
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N))) =
      CenterEndpointPotential.finiteSupportCapacity (gaussianRootMass alpha L) (N + 1) -
        (SignedGaussianEnergy.rootSignedAmplitude alpha L (N + 1)) ^ 2 /
          CenterEndpointPotential.finiteSupportCapacity (gaussianRootMass alpha L) (N + 1) := by
  rw [support_schur_response, ← weighted_support_eq_root_capacity,
    ← weighted_mean_eq_root_amplitude]
  field_simp [GibbsTraceForm.Z_ne_zero (logIntensity N alpha L),
    (supportFraction_pos N alpha L).ne']

/-- Both natural endpoint responses are restored and combined before any
coherent square. The original signed endpoint response is recovered exactly. -/
theorem endpoint_response_eq_original (N : ℕ) (L : ℝ) :
    GibbsTraceForm.Z (logIntensity N 1 L) * signedMean N 1 L -
      GibbsTraceForm.Z (logIntensity N Real.pi L) * signedMean N Real.pi L =
        CenterEndpointPotential.finiteSignedResponse (CenterEndpointPotential.endpointWeight L)
          (N + 1) := by
  rw [weighted_mean_eq_root_amplitude, weighted_mean_eq_root_amplitude]
  simp only [SignedGaussianEnergy.rootSignedAmplitude, SignedGaussianEnergy.rootSignedMass,
    CenterEndpointPotential.finiteSignedResponse, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [CenterEndpointPotential.endpointWeight]
  ring

structure Conclusions : Prop where
  intrinsic_support : ∀ (N : ℕ) (i : Index N),
    probe N i = centre N i * support N i
  actual_probe_square : ∀ (N : ℕ) (i : Index N),
    probe N i * probe N i = support N i
  actual_susceptibility : ∀ (N : ℕ) (alpha L : ℝ),
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (probe N)) (diagonalObservation (probe N)) =
        supportFraction N alpha L - (signedMean N alpha L) ^ 2
  positive_support : ∀ (N : ℕ) (alpha L : ℝ),
    0 < supportFraction N alpha L
  support_reduction : ∀ (N : ℕ) (alpha L : ℝ),
    form N alpha L
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N)))
        (residual alpha L (diagonalObservation (probe N)) (diagonalObservation (support N))) =
      supportFraction N alpha L -
        (signedMean N alpha L) ^ 2 / supportFraction N alpha L
  complete_readout : ∀ (N : ℕ) (L : ℝ),
    GibbsTraceForm.Z (logIntensity N 1 L) * signedMean N 1 L -
      GibbsTraceForm.Z (logIntensity N Real.pi L) * signedMean N Real.pi L =
        CenterEndpointPotential.finiteSignedResponse (CenterEndpointPotential.endpointWeight L)
          (N + 1)

theorem generated : Conclusions where
  intrinsic_support := probe_eq_centre_mul_support
  actual_probe_square := probe_square
  actual_susceptibility := probe_hessian
  positive_support := supportFraction_pos
  support_reduction := support_schur_response
  complete_readout := endpoint_response_eq_original

end GeneratedFoundations.Analysis.HistoryPrefixMobiusResponse
