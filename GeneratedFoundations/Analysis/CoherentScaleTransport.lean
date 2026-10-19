module

public import GeneratedFoundations.Analysis.CapacityRestoredWindowBudget
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Common-response compatibility after restoring capacity

A prime birth compares the same old source at two observation scales. Its
signed response is an observation difference, with the natural-cutoff
boundary retained. This module carries that comparison through the complete
weighted quadratic integral using only the arithmetic branch.

All integrability statements below are proved for the actual finite source.
No bound on its coherent energy, correlation, or limiting budget is an input.
The finite cardinality used to establish integrability is not used as a
generation-independent energy bound. In the transport identity the signed
correlation is retained before the first inequality.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace GeneratedFoundations.Analysis.CoherentScaleTransport

open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedMobiusObservation
open CenterEndpointPotential CanonicalMobiusReadout CanonicalEndpointLedger
open MaximumPrimeFactorStage CapacityEnergyLedger CapacityRestoredWindowBudget
open PrimeCylinderScaleBudget NaturalSourceScaleBudget

/-- The real density of the existing weighted logarithmic scale measure. -/
def scaleDensity (sigma u : ℝ) : ℝ := Real.exp (-2 * sigma * u)

/-- Signed observation of a finite subset of the same generated source. -/
def response (S : Finset ℕ) (u : ℝ) : ℝ :=
  CentrePair.signed (sectorPairOn (gaussianWindowMass (Real.exp u)) S)

def energy (sigma : ℝ) (S : Finset ℕ) : ℝ :=
  ∫ u : ℝ, scaleDensity sigma u * response S u ^ 2

/-- The old source and the genuinely paired source at its forced scale.
This is a signed correlation, not a separately chosen response or state. -/
def returnCorrelation (sigma : ℝ) (p : PrimeIndex) (N : ℕ) : ℝ :=
  ∫ u : ℝ, scaleDensity sigma u * response (stageBefore p.1 N) u *
    response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))

@[fun_prop] theorem measurable_response (S : Finset ℕ) : Measurable (response S) := by
  classical
  have heq : response S = fun u =>
      ∑ n ∈ S, (generatedMoebius n : ℝ) * gaussianWindowMass (Real.exp u) n := by
    funext u
    exact sectorPairOn_signed _ S
  rw [heq]
  unfold gaussianWindowMass gaussianRootMass
  fun_prop

theorem scaleDensity_pos (sigma u : ℝ) : 0 < scaleDensity sigma u :=
  Real.exp_pos _

/-- The real scale density has the same covariance as its extended-real
counterpart. The factor is fixed by translation, not by a normalization. -/
theorem scaleDensity_shift (sigma a u : ℝ) :
    scaleDensity sigma u =
      scaleDensity sigma a * scaleDensity sigma (u - a) := by
  unfold scaleDensity
  rw [← Real.exp_add]
  congr 1
  ring

theorem gaussianWindowMass_le_one (L : ℝ) (n : ℕ) :
    gaussianWindowMass L n ≤ 1 := by
  unfold gaussianWindowMass gaussianRootMass
  have hfirst : Real.exp (-1 * (n : ℝ) ^ 2 / L ^ 2) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [sq_nonneg (n : ℝ)])
      (sq_nonneg L)
  linarith [Real.exp_pos (-Real.pi * (n : ℝ) ^ 2 / L ^ 2)]

private theorem capacity_le_card (S : Finset ℕ) (L : ℝ) :
    CentrePair.capacity (sectorPairOn (gaussianWindowMass L) S) ≤ (S.card : ℝ) := by
  classical
  unfold CentrePair.capacity sectorPairOn
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hm : generatedMoebius n = 0 ∨ generatedMoebius n = 1 ∨
          generatedMoebius n = -1 := by
        simpa only [generatedMoebius_eq_moebius] using ArithmeticFunction.moebius_eq_or n
      rcases hm with h | h | h <;>
        simp only [h] <;> norm_num <;> exact gaussianWindowMass_le_one L n
    _ = _ := by simp

private theorem capacity_integrable (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (N : ℕ) : Integrable (fun u : ℝ =>
      scaleDensity sigma u * capacityProfile N u) := by
  have hmeas : Measurable (fun u : ℝ =>
      scaleDensity sigma u * capacityProfile N u) := by
    have hcapacity : Measurable (capacityProfile N) := by
      change Measurable (fun u : ℝ => capacityProfile N u)
      simp_rw [capacityProfile_eq]
      apply Finset.measurable_fun_sum
      intro n _hn
      by_cases hs : GeneratedSquarefree n
      · simp only [hs, ↓reduceIte]
        unfold gaussianWindowMass gaussianRootMass
        fun_prop
      · simp only [hs, ↓reduceIte]
        exact measurable_const
    exact (by unfold scaleDensity; fun_prop : Measurable (scaleDensity sigma)).mul hcapacity
  have hnonneg : ∀ u : ℝ, 0 ≤ scaleDensity sigma u * capacityProfile N u := by
    intro u
    obtain ⟨hp, hn⟩ := canonicalEndpointPair_nonnegative (expScale u) N
    exact mul_nonneg (scaleDensity_pos sigma u).le (CentrePair.capacity_nonneg _ hp hn)
  apply (lintegral_ofReal_ne_top_iff_integrable hmeas.aestronglyMeasurable
    (ae_of_all _ hnonneg)).mp
  have hbudget : capacityBudget sigma N < ∞ :=
    lt_of_le_of_lt (capacityBudget_uniform sigma hsigma N)
      (uniformCapacityBound_lt_top sigma hsigma)
  simpa only [capacityBudget, scaleDensity, logWeight,
    ENNReal.ofReal_mul (Real.exp_pos _).le] using hbudget.ne

/-- Finite integrability is derived from the native Gaussian weights and the
actual generated support. Its finite-cardinality envelope is used only to
justify the subsequent signed integral identities. -/
theorem energy_integrable (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    {S : Finset ℕ} {N : ℕ} (hS : S ⊆ SignedGaussianEnergy.rootRange N) :
    Integrable (fun u : ℝ => scaleDensity sigma u * response S u ^ 2) := by
  apply ((capacity_integrable sigma hsigma N).const_mul (S.card : ℝ)).mono'
    ((by unfold scaleDensity; fun_prop : Measurable (fun u : ℝ =>
      scaleDensity sigma u * response S u ^ 2)).aestronglyMeasurable)
  apply ae_of_all
  intro u
  obtain ⟨hp, hn⟩ := sectorPairOn_nonnegative (gaussianWindowMass (Real.exp u)) S
    (fun n _ => endpointWeight_nonneg _ _)
  have hc := CentrePair.capacity_nonneg _ hp hn
  have hcap := sector_capacity_partition (gaussianWindowMass (Real.exp u)) hS
  obtain ⟨hrp, hrn⟩ := sectorPairOn_nonnegative (gaussianWindowMass (Real.exp u))
    (SignedGaussianEnergy.rootRange N \ S) (fun n _ => endpointWeight_nonneg _ _)
  have hrest := CentrePair.capacity_nonneg _ hrp hrn
  have hsub : CentrePair.capacity (sectorPairOn (gaussianWindowMass (Real.exp u)) S) ≤
      capacityProfile N u := by
    change _ ≤ CentrePair.capacity
      (sectorPairOn (gaussianWindowMass (Real.exp u)) (SignedGaussianEnergy.rootRange N))
    linarith
  have hsq := CentrePair.signed_sq_le_capacity_sq _ hp hn
  have hcard := capacity_le_card S (Real.exp u)
  have hpoint : response S u ^ 2 ≤ (S.card : ℝ) * capacityProfile N u := by
    unfold response
    nlinarith [mul_nonneg hc (sub_nonneg.mpr hcard),
      mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg S.card : (0 : ℝ) ≤ S.card)]
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (scaleDensity_pos sigma u).le (sq_nonneg _))]
  have h := mul_le_mul_of_nonneg_left hpoint (scaleDensity_pos sigma u).le
  nlinarith

theorem energy_nonneg (sigma : ℝ) (S : Finset ℕ) : 0 ≤ energy sigma S :=
  integral_nonneg fun u => mul_nonneg (scaleDensity_pos sigma u).le (sq_nonneg _)

/-- On a complete natural prefix this is exactly the existing occupation
observation, including its unit and every signed cross term. -/
theorem response_rootRange (N : ℕ) (u : ℝ) :
    response (SignedGaussianEnergy.rootRange N) u =
      canonicalOccupationAmplitude (expScale u) N := by
  exact canonicalEndpointPair_signed (expScale u) N

/-- The real quadratic integral and the existing extended-real coherent
budget measure the same finite source. Finiteness is established above,
before replacing the nonnegative integral by its real counterpart. -/
theorem energy_eq_coherentBudget (sigma : ℝ) (hsigma : 1 / 2 < sigma) (N : ℕ) :
    ENNReal.ofReal (energy sigma (SignedGaussianEnergy.rootRange N)) =
      coherentBudget sigma N := by
  rw [energy, ofReal_integral_eq_lintegral_ofReal
    (energy_integrable sigma hsigma (Finset.Subset.refl _))
    (ae_of_all _ (fun u =>
      mul_nonneg (scaleDensity_pos sigma u).le (sq_nonneg _)))]
  simp only [coherentBudget, scaleDensity, logWeight, response_rootRange,
    canonicalOccupationEnergy, ENNReal.ofReal_mul (Real.exp_pos _).le]

private theorem translated_integrable {f : ℝ → ℝ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun u : ℝ => f (u - a)) := by
  simpa only [Function.comp_def, sub_eq_add_neg] using
    (measurePreserving_add_right volume (-a)).integrable_comp_of_integrable hf

private theorem translated_integral (f : ℝ → ℝ) (a : ℝ) :
    (∫ u : ℝ, f (u - a)) = ∫ u : ℝ, f u := by
  simpa only [sub_eq_add_neg] using
    (measurePreserving_add_right volume (-a)).integral_comp
      (MeasurableEquiv.addRight (-a)).measurableEmbedding f

/-- Exact return of the *coherent* self-energy, with its original capacity
already restored. The coefficient is independent of cutoff and scale. -/
theorem returned_energy (sigma : ℝ) (p : PrimeIndex) (S : Finset ℕ) :
    (∫ u : ℝ, scaleDensity sigma u *
      response S (u - Real.log (p.1 : ℝ)) ^ 2) =
      primeReturn sigma p * energy sigma S := by
  have heq : ∀ u : ℝ, scaleDensity sigma u *
      response S (u - Real.log (p.1 : ℝ)) ^ 2 =
      primeReturn sigma p * (scaleDensity sigma (u - Real.log (p.1 : ℝ)) *
        response S (u - Real.log (p.1 : ℝ)) ^ 2) := by
    intro u
    rw [scaleDensity_shift sigma (Real.log (p.1 : ℝ)) u]
    simp only [primeReturn, scaleDensity]
    ring
  simp_rw [heq]
  rw [integral_const_mul]
  congr 1
  exact translated_integral (fun u => scaleDensity sigma u * response S u ^ 2) _

private theorem returned_integrable (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (p : PrimeIndex) {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ SignedGaussianEnergy.rootRange N) :
    Integrable (fun u : ℝ => scaleDensity sigma u *
      response S (u - Real.log (p.1 : ℝ)) ^ 2) := by
  have h := (translated_integrable (energy_integrable sigma hsigma hS)
    (Real.log (p.1 : ℝ))).const_mul (primeReturn sigma p)
  convert h using 1
  funext u
  rw [scaleDensity_shift sigma (Real.log (p.1 : ℝ)) u]
  simp only [primeReturn, scaleDensity]
  ring

theorem stageBefore_subset_range (p N : ℕ) :
    stageBefore p N ⊆ SignedGaussianEnergy.rootRange N := by
  intro n hn
  have h := mem_stageBefore.mp hn
  exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩

theorem stagePairedBase_subset_range (p N : ℕ) :
    stagePairedBase p N ⊆ SignedGaussianEnergy.rootRange N := by
  intro n hn
  have h := mem_stagePairedBase.mp hn
  exact Finset.mem_Icc.mpr ⟨h.1, h.2.1.trans (Nat.div_le_self N p)⟩

/-- Same-response cancellation and its actual cutoff remainder. Every term
is evaluated on the genuine generated old state. -/
theorem stage_response_difference (p : PrimeIndex) (N : ℕ) (u : ℝ) :
    response (stageAfter p.1 N) u =
      response (stagePairedBase p.1 N) u -
        response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) +
      response (stageCutoffBoundary p.1 N) u := by
  unfold response
  rw [sectorPairOn_stageAfter_eq_afterStagePair _ p.2, afterStagePair_signed]
  have hg := gaussian_returnPair_eq_scale_transport (expScale u) (N := N) p.2
  change returnPair (gaussianWindowMass (Real.exp u)) p.1 N =
    pairedPair (gaussianWindowMass (Real.exp u / (p.1 : ℝ))) p.1 N at hg
  rw [hg]
  have hs := dividedScale_expScale p u
  have hval := congrArg Subtype.val hs
  change Real.exp u / (p.1 : ℝ) = Real.exp (u - Real.log (p.1 : ℝ)) at hval
  simp only [pairedPair, cutoffBoundaryPair]
  rw [hval]

/-- The full old state includes the actual boundary. Only the returned
paired interior is translated. -/
theorem stage_response_transport (p : PrimeIndex) (N : ℕ) (u : ℝ) :
    response (stageAfter p.1 N) u = response (stageBefore p.1 N) u -
      response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) := by
  have h := stage_response_difference p N u
  have hold : response (stageBefore p.1 N) u =
      response (stagePairedBase p.1 N) u +
        response (stageCutoffBoundary p.1 N) u := by
    unfold response
    rw [← beforePair, beforePair_eq_add _ p.2.pos, CentrePair.signed_add]
    rfl
  linarith

theorem returnCorrelation_integrable (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (p : PrimeIndex) (N : ℕ) :
    Integrable (fun u : ℝ => scaleDensity sigma u * response (stageBefore p.1 N) u *
      response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))) := by
  have ho := energy_integrable sigma hsigma (stageBefore_subset_range p.1 N)
  have hr := returned_integrable sigma hsigma p (stagePairedBase_subset_range p.1 N)
  apply (ho.add hr).mono'
    ((by unfold scaleDensity; fun_prop : Measurable (fun u : ℝ =>
      scaleDensity sigma u * response (stageBefore p.1 N) u *
        response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)))).aestronglyMeasurable)
  apply ae_of_all
  intro u
  rw [Real.norm_eq_abs, abs_mul, abs_mul,
    abs_of_pos (scaleDensity_pos sigma u)]
  have hcs : |response (stageBefore p.1 N) u| *
      |response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))| ≤
        response (stageBefore p.1 N) u ^ 2 +
          response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2 := by
    nlinarith [sq_nonneg (|response (stageBefore p.1 N) u| -
      |response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))|),
      sq_abs (response (stageBefore p.1 N) u),
      sq_abs (response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)))]
  have h := mul_le_mul_of_nonneg_left hcs (scaleDensity_pos sigma u).le
  change scaleDensity sigma u * |response (stageBefore p.1 N) u| *
    |response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))| ≤
      scaleDensity sigma u * response (stageBefore p.1 N) u ^ 2 +
        scaleDensity sigma u *
          response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2
  nlinarith

/-- The capacity-restored, all-scale birth ledger. The boundary is already
in the old response, and the complete signed correlation survives integration. -/
theorem stage_energy_increment (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (p : PrimeIndex) (N : ℕ) :
    energy sigma (stageAfter p.1 N) - energy sigma (stageBefore p.1 N) =
      primeReturn sigma p * energy sigma (stagePairedBase p.1 N) -
        2 * returnCorrelation sigma p N := by
  have ho := energy_integrable sigma hsigma (stageBefore_subset_range p.1 N)
  have hr := returned_integrable sigma hsigma p (stagePairedBase_subset_range p.1 N)
  have hc := returnCorrelation_integrable sigma hsigma p N
  have heq : ∀ u : ℝ,
      scaleDensity sigma u * response (stageAfter p.1 N) u ^ 2 =
        scaleDensity sigma u * response (stageBefore p.1 N) u ^ 2 +
          scaleDensity sigma u *
            response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2 -
          2 * (scaleDensity sigma u * response (stageBefore p.1 N) u *
            response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))) := by
    intro u
    rw [stage_response_transport]
    ring
  have henergy : energy sigma (stageAfter p.1 N) =
      energy sigma (stageBefore p.1 N) +
        (∫ u : ℝ, scaleDensity sigma u *
          response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2) -
        2 * returnCorrelation sigma p N := by
    change (∫ u : ℝ, scaleDensity sigma u * response (stageAfter p.1 N) u ^ 2) = _
    simp_rw [heq]
    calc
      _ = (∫ u : ℝ, scaleDensity sigma u * response (stageBefore p.1 N) u ^ 2 +
          scaleDensity sigma u *
            response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2) -
          ∫ u : ℝ, 2 * (scaleDensity sigma u * response (stageBefore p.1 N) u *
            response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))) := by
        simpa only [Pi.add_apply] using integral_sub (ho.add hr) (hc.const_mul 2)
      _ = _ := by
        rw [integral_add ho hr, integral_const_mul]
        rfl
  rw [returned_energy] at henergy
  linarith

/-- A scale-independent inequality after the two source copies have been
combined. The positive comparison coefficient is a proof parameter, not a
new source input. The signed identity above is the stronger ledger. -/
theorem stage_energy_le (sigma : ℝ) (hsigma : 1 / 2 < sigma)
    (p : PrimeIndex) (N : ℕ) (q : ℝ) (hq : 0 < q) :
    energy sigma (stageAfter p.1 N) ≤
      (1 + q) * energy sigma (stageBefore p.1 N) +
        (1 + q⁻¹) * primeReturn sigma p * energy sigma (stagePairedBase p.1 N) := by
  have ho := energy_integrable sigma hsigma (stageBefore_subset_range p.1 N)
  have hr := returned_integrable sigma hsigma p (stagePairedBase_subset_range p.1 N)
  have ha := energy_integrable sigma hsigma (stageAfter_subset_rootRange (N := N) p.2)
  have hpoint : ∀ u : ℝ,
      scaleDensity sigma u * response (stageAfter p.1 N) u ^ 2 ≤
        (1 + q) * (scaleDensity sigma u * response (stageBefore p.1 N) u ^ 2) +
          (1 + q⁻¹) * (scaleDensity sigma u *
            response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2) := by
    intro u
    rw [stage_response_transport]
    have hy : (response (stageBefore p.1 N) u -
        response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))) ^ 2 ≤
      (1 + q) * response (stageBefore p.1 N) u ^ 2 +
        (1 + q⁻¹) *
          response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2 := by
      have heq :
          (1 + q) * response (stageBefore p.1 N) u ^ 2 +
              (1 + q⁻¹) *
                response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) ^ 2 -
            (response (stageBefore p.1 N) u -
              response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))) ^ 2 =
          (q * response (stageBefore p.1 N) u +
            response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ))) ^ 2 / q := by
        field_simp [hq.ne']
        ring
      have h := div_nonneg (sq_nonneg (q * response (stageBefore p.1 N) u +
        response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)))) hq.le
      linarith
    have h := mul_le_mul_of_nonneg_left hy (scaleDensity_pos sigma u).le
    nlinarith
  have h := integral_mono ha ((ho.const_mul (1 + q)).add (hr.const_mul (1 + q⁻¹))) hpoint
  have hadd := integral_add (ho.const_mul (1 + q)) (hr.const_mul (1 + q⁻¹))
  simp only [Pi.add_apply] at h hadd
  rw [hadd, integral_const_mul, integral_const_mul, returned_energy] at h
  simpa only [energy, mul_assoc] using h

structure Conclusions : Prop where
  same_coherent_budget : ∀ sigma, 1 / 2 < sigma → ∀ N,
    ENNReal.ofReal (energy sigma (SignedGaussianEnergy.rootRange N)) =
      coherentBudget sigma N
  actual_response_difference : ∀ (p : PrimeIndex) (N : ℕ) (u : ℝ),
    response (stageAfter p.1 N) u =
      response (stagePairedBase p.1 N) u -
        response (stagePairedBase p.1 N) (u - Real.log (p.1 : ℝ)) +
      response (stageCutoffBoundary p.1 N) u
  exact_return_energy : ∀ sigma p S,
    (∫ u : ℝ, scaleDensity sigma u *
      response S (u - Real.log (p.1 : ℝ)) ^ 2) =
        primeReturn sigma p * energy sigma S
  complete_energy_increment : ∀ sigma, 1 / 2 < sigma → ∀ p N,
    energy sigma (stageAfter p.1 N) - energy sigma (stageBefore p.1 N) =
      primeReturn sigma p * energy sigma (stagePairedBase p.1 N) -
        2 * returnCorrelation sigma p N
  combined_energy_bound : ∀ sigma, 1 / 2 < sigma → ∀ p N q, 0 < q →
    energy sigma (stageAfter p.1 N) ≤
      (1 + q) * energy sigma (stageBefore p.1 N) +
        (1 + q⁻¹) * primeReturn sigma p * energy sigma (stagePairedBase p.1 N)

theorem conclusions : Conclusions where
  same_coherent_budget := energy_eq_coherentBudget
  actual_response_difference := stage_response_difference
  exact_return_energy := returned_energy
  complete_energy_increment := stage_energy_increment
  combined_energy_bound := stage_energy_le

end GeneratedFoundations.Analysis.CoherentScaleTransport
