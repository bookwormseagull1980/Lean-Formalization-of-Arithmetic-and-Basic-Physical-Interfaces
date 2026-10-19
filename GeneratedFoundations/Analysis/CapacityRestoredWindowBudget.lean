module

public import GeneratedFoundations.Analysis.GaussianPrefixTail
public import GeneratedFoundations.Analysis.NaturalSourceScaleBudget

/-!
# Capacity-restored energy in the actual finite Gaussian window

The window and its weights restrict the existing natural source. The two
probabilities are obtained by dividing its actual positive sector masses by
their sum. This normalization does not discard the sum: it reappears squared
when the centre variance is converted back to the coherent energy.

For genuine prime births, multiplication by the restored capacity is performed
before any inequality. The resulting identity retains both the nonnegative
mixing dissipation and the capacity-transfer term. The level-five observation
and the Gaussian tail satisfy a two-sided quadratic comparison, including the
visible--outside cross term in the underlying exact reconstruction. Window
partition, joint prime flip and genuine prime birth each carry their exact
positive-capacity conservation law. The potential lost to mixing is recorded
as transverse capacity rather than removed from the source.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace GeneratedFoundations.Analysis.CapacityRestoredWindowBudget

open GeneratedFoundations.Arithmetic.JointOccupationScale
open CenterEndpointPotential CanonicalEndpointLedger CanonicalMobiusReadout
open CapacityEnergyLedger GaussianWindowCapacity GaussianPrefixTail
open MaximumPrimeFactorStage
open PrimeCylinderScaleBudget NaturalSourceScaleBudget

namespace CentrePair

open CenterEndpointPotential.CentrePair

def positiveProbability (x : CentrePair) : ℝ := x.positive / capacity x
def negativeProbability (x : CentrePair) : ℝ := x.negative / capacity x

/-- The variance of the centre character under the actual normalized pair.
The empty observation has zero first and second moments. -/
def centreVariance (x : CentrePair) : ℝ :=
  positiveProbability x + negativeProbability x - bias x ^ 2

theorem probabilities_sum (x : CentrePair) (hc : capacity x ≠ 0) :
    positiveProbability x + negativeProbability x = 1 := by
  rw [positiveProbability, negativeProbability, ← add_div]
  exact div_self hc

theorem probability_difference (x : CentrePair) :
    positiveProbability x - negativeProbability x = bias x := by
  simp [positiveProbability, negativeProbability, bias, signed, sub_div]

theorem centreVariance_eq_one_sub_bias_sq (x : CentrePair) (hc : capacity x ≠ 0) :
    centreVariance x = 1 - bias x ^ 2 := by
  rw [centreVariance, probabilities_sum x hc]

theorem centreVariance_eq (x : CentrePair) (hc : capacity x ≠ 0) :
    centreVariance x = 4 * positiveProbability x * negativeProbability x := by
  rw [centreVariance_eq_one_sub_bias_sq x hc]
  unfold positiveProbability negativeProbability bias signed capacity at *
  field_simp
  ring

theorem centreVariance_nonneg (x : CentrePair)
    (hp : 0 ≤ x.positive) (hn : 0 ≤ x.negative) : 0 ≤ centreVariance x := by
  by_cases hc : capacity x = 0
  · simp [centreVariance, positiveProbability, negativeProbability, bias, hc]
  · rw [centreVariance_eq x hc]
    have hcap := capacity_nonneg x hp hn
    exact mul_nonneg (mul_nonneg (by norm_num)
      (div_nonneg hp hcap)) (div_nonneg hn hcap)

/-- Recovering the coherent observation requires the square of the actual
capacity, even though the two probabilities sum to one. -/
theorem coherentEnergy_eq_variance_deficit (x : CentrePair)
    (hp : 0 ≤ x.positive) (hn : 0 ≤ x.negative) :
    coherentEnergy x = capacity x ^ 2 * (1 - centreVariance x) := by
  by_cases hc : capacity x = 0
  · have hs := signed_eq_zero_of_capacity_eq_zero x hp hn hc
    simp [coherentEnergy, centreVariance, hc, hs]
  · rw [centreVariance_eq_one_sub_bias_sq x hc]
    unfold coherentEnergy bias
    field_simp
    ring

/-- Complete opposite-centre mixing after capacity restoration. No term is
estimated separately and both sector capacities may vanish. -/
theorem restored_mixing_identity (x y : CentrePair)
    (hxp : 0 ≤ x.positive) (hxn : 0 ≤ x.negative)
    (hyp : 0 ≤ y.positive) (hyn : 0 ≤ y.negative) :
    coherentEnergy (oppositeMix x y) =
      coherentEnergy x + coherentEnergy y +
        capacity y * quadraticPotential x + capacity x * quadraticPotential y -
        (capacity x + capacity y) * mixingDissipation x y := by
  have hx := capacity_mul_potential_eq_coherentEnergy x hxp hxn
  have hy := capacity_mul_potential_eq_coherentEnergy y hyp hyn
  have hz := capacity_mul_potential_eq_coherentEnergy (oppositeMix x y)
    (by exact add_nonneg hxp hyn) (by exact add_nonneg hxn hyp)
  have hd := quadraticPotential_mixing_identity_nonnegative x y hxp hxn hyp hyn
  rw [capacity_oppositeMix] at hz
  nlinarith [congrArg (fun v : ℝ => (capacity x + capacity y) * v) hd]

/-- The exact excess of the restored mixing loss over its capacity-transfer
term is the original signed correlation. -/
theorem restored_dissipation_balance (x y : CentrePair)
    (hxp : 0 ≤ x.positive) (hxn : 0 ≤ x.negative)
    (hyp : 0 ≤ y.positive) (hyn : 0 ≤ y.negative) :
    (capacity x + capacity y) * mixingDissipation x y -
        (capacity y * quadraticPotential x + capacity x * quadraticPotential y) =
      2 * signed x * signed y := by
  have hd := restored_mixing_identity x y hxp hxn hyp hyn
  have he : coherentEnergy (oppositeMix x y) =
      coherentEnergy x + coherentEnergy y - 2 * signed x * signed y := by
    simp only [coherentEnergy, signed_oppositeMix]
    ring
  linarith

/-- Opposite-centre mixing transfers the normalized potential loss to the
transverse capacity. Their sum retains the entire original positive mass. -/
theorem transverse_mixing_identity (x y : CentrePair)
    (hxp : 0 ≤ x.positive) (hxn : 0 ≤ x.negative)
    (hyp : 0 ≤ y.positive) (hyn : 0 ≤ y.negative) :
    transverseCapacity (oppositeMix x y) =
      transverseCapacity x + transverseCapacity y + mixingDissipation x y := by
  have hd := quadraticPotential_mixing_identity_nonnegative x y hxp hxn hyp hyn
  simp only [transverseCapacity, capacity_oppositeMix]
  linarith

theorem mixing_capacity_conservation (x y : CentrePair)
    (hxp : 0 ≤ x.positive) (hxn : 0 ≤ x.negative)
    (hyp : 0 ≤ y.positive) (hyn : 0 ≤ y.negative) :
    quadraticPotential (oppositeMix x y) + transverseCapacity x +
        transverseCapacity y + mixingDissipation x y = capacity x + capacity y := by
  have hd := transverse_mixing_identity x y hxp hxn hyp hyn
  have hc := potential_add_transverse (oppositeMix x y)
  rw [capacity_oppositeMix] at hc
  linarith

end CentrePair

/-- The visible and retained outside masses resolve one and the same
positive capacity, with their original Gaussian weights. -/
theorem fiveWindow_capacity_conservation (L : PositiveScale) (N : ℕ) :
    CentrePair.capacity (fiveWindowPair L N) +
        CentrePair.capacity (outsidePair 5 L N) =
      CentrePair.capacity (canonicalEndpointPair L N) := by
  rw [five_window_complete, CentrePair.capacity_add]

/-- The joint prime flip preserves the Gaussian weight and its window
membership simultaneously. This acts on the complete joint source. -/
theorem windowed_capacity_jointFlip (R : ℝ) (p : PrimeIndex)
    (x : Occupation × PositiveScale) :
    windowedGaussianMass R (jointFlip p x).2 (label (jointFlip p x).1) =
      windowedGaussianMass R x.2 (label x.1) := by
  classical
  have hg := gaussianResponse_jointFlip p x
  rw [gaussianResponse_eq_window, gaussianResponse_eq_window] at hg
  unfold windowedGaussianMass
  rw [window_jointFlip]
  split_ifs <;> first | exact hg | rfl

/-- The two probabilities use the actual Gaussian sector weights of the
finite window. Their capacity is not replaced by its cardinality. -/
theorem fiveWindow_probabilities (L : PositiveScale) (N : ℕ)
    (hc : CentrePair.capacity (fiveWindowPair L N) ≠ 0) :
    CentrePair.positiveProbability (fiveWindowPair L N) +
      CentrePair.negativeProbability (fiveWindowPair L N) = 1 :=
  CentrePair.probabilities_sum _ hc

theorem fiveWindow_capacity_restored (L : PositiveScale) (N : ℕ) :
    coherentEnergy (fiveWindowPair L N) =
      CentrePair.capacity (fiveWindowPair L N) ^ 2 *
        (1 - CentrePair.centreVariance (fiveWindowPair L N)) := by
  obtain ⟨hp, hn⟩ := visiblePair_nonnegative 5 L N
  exact CentrePair.coherentEnergy_eq_variance_deficit _ hp hn

/-- The birth update uses exactly the old and returned source; there is no
independently chosen comparison state or driving term. -/
theorem generated_restored_dissipation (w : ℕ → ℝ) {p N : ℕ}
    (hw : ∀ n, 0 ≤ w n) :
    (CentrePair.capacity (beforePair w p N) + CentrePair.capacity (returnPair w p N)) *
        CentrePair.mixingDissipation (beforePair w p N) (returnPair w p N) -
      (CentrePair.capacity (returnPair w p N) *
          CentrePair.quadraticPotential (beforePair w p N) +
        CentrePair.capacity (beforePair w p N) *
          CentrePair.quadraticPotential (returnPair w p N)) =
      2 * CentrePair.signed (beforePair w p N) * CentrePair.signed (returnPair w p N) := by
  obtain ⟨hxp, hxn⟩ := sectorPairOn_nonnegative w (stageBefore p N) (fun n _ => hw n)
  obtain ⟨hyp, hyn⟩ := sectorPairOn_nonnegative (fun n => w (p * n))
    (stagePairedBase p N) (fun n _ => hw (p * n))
  exact CentrePair.restored_dissipation_balance _ _ hxp hxn hyp hyn

/-- A genuine generation stage retains both the old source and the returned
prime image. The unpaired cutoff boundary remains part of the old source. -/
theorem generated_capacity_conservation (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    CentrePair.capacity (sectorPairOn w (stageAfter p N)) =
      CentrePair.capacity (pairedPair w p N) +
        CentrePair.capacity (returnPair w p N) +
        CentrePair.capacity (cutoffBoundaryPair w p N) := by
  rw [generated_stage_capacity_increment w hp, beforePair_eq_add w hp.pos,
    CentrePair.capacity_add]
  ring

/-- Resolving any subset of an existing finite source preserves its total
capacity when the unresolved complement is retained. -/
theorem sector_capacity_partition (w : ℕ → ℝ) {S T : Finset ℕ}
    (hS : S ⊆ T) :
    CentrePair.capacity (sectorPairOn w S) +
        CentrePair.capacity (sectorPairOn w (T \ S)) =
      CentrePair.capacity (sectorPairOn w T) := by
  classical
  rw [← CentrePair.capacity_add, ← sectorPairOn_union w Finset.disjoint_sdiff,
    Finset.union_sdiff_of_subset hS]

theorem stageAfter_subset_rootRange {p N : ℕ} (hp : p.Prime) :
    stageAfter p N ⊆ SignedGaussianEnergy.rootRange N := by
  intro n hn
  simp only [stageAfter, Finset.mem_union] at hn
  rw [SignedGaussianEnergy.rootRange, Finset.mem_Icc]
  rcases hn with hn | hn
  · have h := mem_stageBefore.mp hn
    exact ⟨h.1, h.2.1⟩
  · obtain ⟨m, hm, rfl⟩ := mem_stageBirth.mp hn
    have h := mem_stagePairedBase.mp hm
    have hmpos : 0 < m := by omega
    exact ⟨Nat.succ_le_iff.mpr (Nat.mul_pos hp.pos hmpos),
      by simpa [Nat.mul_comm] using (Nat.le_div_iff_mul_le hp.pos).mp h.2.1⟩

/-- Generation resolves more of the same closed source. The increase in
resolved capacity equals the decrease in its actual unresolved complement. -/
theorem generated_closed_capacity_conservation (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    CentrePair.capacity (beforePair w p N) +
        CentrePair.capacity (sectorPairOn w
          (SignedGaussianEnergy.rootRange N \ stageBefore p N)) =
      CentrePair.capacity (sectorPairOn w (stageAfter p N)) +
        CentrePair.capacity (sectorPairOn w
          (SignedGaussianEnergy.rootRange N \ stageAfter p N)) := by
  classical
  have hbefore : stageBefore p N ⊆ SignedGaussianEnergy.rootRange N := by
    intro n hn
    have h := mem_stageBefore.mp hn
    exact Finset.mem_Icc.mpr ⟨h.1, h.2.1⟩
  change CentrePair.capacity (sectorPairOn w (stageBefore p N)) + _ = _
  rw [sector_capacity_partition w hbefore,
    sector_capacity_partition w (stageAfter_subset_rootRange hp)]

theorem generated_transverse_capacity_transfer (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) (hw : ∀ n, 0 ≤ w n) :
    transverseCapacity (sectorPairOn w (stageAfter p N)) =
      transverseCapacity (beforePair w p N) +
        transverseCapacity (returnPair w p N) +
        CentrePair.mixingDissipation (beforePair w p N) (returnPair w p N) := by
  have hupdate : sectorPairOn w (stageAfter p N) =
      CentrePair.oppositeMix (beforePair w p N) (returnPair w p N) := by
    rw [stageAfter, sectorPairOn_union w (disjoint_stageBefore_stageBirth hp),
      sectorPairOn_stageBirth_eq_birthPair w hp]
    rfl
  obtain ⟨hxp, hxn⟩ := sectorPairOn_nonnegative w (stageBefore p N) (fun n _ => hw n)
  obtain ⟨hyp, hyn⟩ := sectorPairOn_nonnegative (fun n => w (p * n))
    (stagePairedBase p N) (fun n _ => hw (p * n))
  rw [hupdate]
  exact CentrePair.transverse_mixing_identity _ _ hxp hxn hyp hyn

/-- Quadratic comparison with the finite window. The only estimate is on the
retained outside response, after exact signed reconstruction. -/
theorem completeEnergy_le_window_and_tail {R : ℝ} (hR : 0 ≤ R)
    (L : PositiveScale) (hK : 0 < windowCutoff R L) (N : ℕ) :
    canonicalOccupationEnergy L N ≤
      2 * coherentEnergy (visiblePair R L N) +
        2 * tailBound L (windowCutoff R L) ^ 2 := by
  have hb := outside_amplitude_uniform hR L hK N
  have hs := sq_abs (canonicalOccupationAmplitude L N -
    CentrePair.signed (visiblePair R L N))
  have ht := tailBound_nonneg L hK
  have hab := abs_nonneg (canonicalOccupationAmplitude L N -
    CentrePair.signed (visiblePair R L N))
  have hsq : (canonicalOccupationAmplitude L N -
      CentrePair.signed (visiblePair R L N)) ^ 2 ≤
      tailBound L (windowCutoff R L) ^ 2 := by nlinarith
  unfold coherentEnergy canonicalOccupationEnergy
  nlinarith [sq_nonneg (canonicalOccupationAmplitude L N -
    2 * CentrePair.signed (visiblePair R L N))]

theorem windowEnergy_le_complete_and_tail {R : ℝ} (hR : 0 ≤ R)
    (L : PositiveScale) (hK : 0 < windowCutoff R L) (N : ℕ) :
    coherentEnergy (visiblePair R L N) ≤
      2 * canonicalOccupationEnergy L N +
        2 * tailBound L (windowCutoff R L) ^ 2 := by
  have hb := outside_amplitude_uniform hR L hK N
  have hs := sq_abs (canonicalOccupationAmplitude L N -
    CentrePair.signed (visiblePair R L N))
  have ht := tailBound_nonneg L hK
  have hab := abs_nonneg (canonicalOccupationAmplitude L N -
    CentrePair.signed (visiblePair R L N))
  have hsq : (canonicalOccupationAmplitude L N -
      CentrePair.signed (visiblePair R L N)) ^ 2 ≤
      tailBound L (windowCutoff R L) ^ 2 := by nlinarith
  unfold coherentEnergy canonicalOccupationEnergy
  nlinarith [sq_nonneg (2 * canonicalOccupationAmplitude L N -
    CentrePair.signed (visiblePair R L N))]

/-- A concrete positive observation scale in the canonical unit-covariance
units. The underlying generated source is unchanged. -/
def halfScale : PositiveScale := ⟨1 / 2, by norm_num⟩

/-- At this scale the level-five window contains exactly the unit occupation.
This checks the actual strict cutoff, not an abstract pair of free masses. -/
theorem fiveWindow_half_labels {N : ℕ} (hN : 1 ≤ N) :
    visibleLabels 5 halfScale N = {1} := by
  classical
  ext n
  simp only [mem_visibleLabels, SignedGaussianEnergy.rootRange, Finset.mem_Icc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hn, _⟩, hw⟩
    have hsq : (n : ℝ) ^ 2 < 5 * (1 / 2 : ℝ) ^ 2 := hw
    have hnlt : n < 2 := by
      by_contra h
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt h)
      nlinarith [sq_nonneg ((n : ℝ) - 2)]
    omega
  · rintro rfl
    refine ⟨⟨le_rfl, hN⟩, ?_⟩
    norm_num [InWindow, halfScale]

theorem fiveWindow_half_pair {N : ℕ} (hN : 1 ≤ N) :
    fiveWindowPair halfScale N =
      ⟨gaussianWindowMass (1 / 2) 1, 0⟩ := by
  unfold fiveWindowPair visiblePair
  rw [fiveWindow_half_labels hN]
  simp [sectorPairOn, GeneratedMobiusObservation.generatedMoebius_eq_moebius, halfScale]

/-- Finite Gaussian normalization is legitimate but does not impose the
equal-sector trace state of the physical carrier on a selected arithmetic
window. This is an exact statement on the original source. -/
theorem fiveWindow_half_bias {N : ℕ} (hN : 1 ≤ N) :
    CentrePair.bias (fiveWindowPair halfScale N) = 1 := by
  rw [fiveWindow_half_pair hN]
  have hw : 0 < gaussianWindowMass (1 / 2) 1 := by
    have h := PrimeCylinderDescent.gaussianResponse_pos ∅ halfScale
    rw [gaussianResponse_eq_window] at h
    simpa [label, halfScale] using h
  simpa [CentrePair.bias, CentrePair.signed, CentrePair.capacity] using div_self hw.ne'

def fiveCapacityBudget (sigma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ, logWeight sigma u *
    ENNReal.ofReal (CentrePair.capacity (fiveWindowPair (expScale u) N))

def fiveNormalizedBudget (sigma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ, logWeight sigma u *
    ENNReal.ofReal (CentrePair.quadraticPotential (fiveWindowPair (expScale u) N))

def fiveCoherentBudget (sigma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ, logWeight sigma u *
    ENNReal.ofReal (coherentEnergy (fiveWindowPair (expScale u) N))

/-- Capacity conservation remains exact inside the weighted scale integral;
the retained outside is not discarded before applying the global bound. -/
theorem fiveCapacityBudget_conservation (sigma : ℝ) (N : ℕ) :
    capacityBudget sigma N =
      ∫⁻ u : ℝ, logWeight sigma u *
        (ENNReal.ofReal (CentrePair.capacity (fiveWindowPair (expScale u) N)) +
          ENNReal.ofReal (CentrePair.capacity (outsidePair 5 (expScale u) N))) := by
  apply lintegral_congr
  intro u
  change logWeight sigma u *
    ENNReal.ofReal (CentrePair.capacity (canonicalEndpointPair (expScale u) N)) = _
  obtain ⟨hvp, hvn⟩ := visiblePair_nonnegative 5 (expScale u) N
  obtain ⟨hop, hon⟩ := outsidePair_nonnegative 5 (expScale u) N
  have hv : 0 ≤ CentrePair.capacity (fiveWindowPair (expScale u) N) :=
    CentrePair.capacity_nonneg _ hvp hvn
  rw [← fiveWindow_capacity_conservation,
    ENNReal.ofReal_add hv
      (CentrePair.capacity_nonneg _ hop hon)]

theorem fiveWindow_capacity_le_full (L : PositiveScale) (N : ℕ) :
    CentrePair.capacity (fiveWindowPair L N) ≤
      CentrePair.capacity (canonicalEndpointPair L N) := by
  rw [five_window_complete, CentrePair.capacity_add]
  obtain ⟨hp, hn⟩ := outsidePair_nonnegative 5 L N
  exact le_add_of_nonneg_right (CentrePair.capacity_nonneg _ hp hn)

/-- The level-five cutoff and the real Gaussian weights give an all-scale
capacity estimate independent of how far the natural source is generated. -/
theorem fiveCapacityBudget_uniform (sigma : ℝ) (hsigma : 1 / 2 < sigma) (N : ℕ) :
    fiveCapacityBudget sigma N ≤ uniformCapacityBound sigma := by
  apply le_trans (lintegral_mono fun u =>
    mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal
      (fiveWindow_capacity_le_full (expScale u) N)) bot_le bot_le)
    (capacityBudget_uniform sigma hsigma N)

theorem fiveNormalizedBudget_uniform (sigma : ℝ) (hsigma : 1 / 2 < sigma) (N : ℕ) :
    fiveNormalizedBudget sigma N ≤ uniformCapacityBound sigma := by
  have hpoint : ∀ u : ℝ,
      CentrePair.quadraticPotential (fiveWindowPair (expScale u) N) ≤
        CentrePair.capacity (fiveWindowPair (expScale u) N) := by
    intro u
    obtain ⟨hp, hn⟩ := visiblePair_nonnegative 5 (expScale u) N
    exact sub_nonneg.mp (transverseCapacity_nonneg _ hp hn)
  apply le_trans (lintegral_mono fun u =>
    mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal (hpoint u)) bot_le bot_le)
    (fiveCapacityBudget_uniform sigma hsigma N)

theorem fiveCoherentBudget_capacity_restored (sigma : ℝ) (N : ℕ) :
    fiveCoherentBudget sigma N =
      ∫⁻ u : ℝ, logWeight sigma u * ENNReal.ofReal
        (CentrePair.capacity (fiveWindowPair (expScale u) N) ^ 2 *
          (1 - CentrePair.centreVariance (fiveWindowPair (expScale u) N))) := by
  apply lintegral_congr
  intro u
  rw [fiveWindow_capacity_restored]

structure Conclusions : Prop where
  window_capacity_conservation : ∀ L N,
    CentrePair.capacity (fiveWindowPair L N) +
        CentrePair.capacity (outsidePair 5 L N) =
      CentrePair.capacity (canonicalEndpointPair L N)
  joint_capacity_conservation : ∀ R p x,
    windowedGaussianMass R (jointFlip p x).2 (label (jointFlip p x).1) =
      windowedGaussianMass R x.2 (label x.1)
  generation_capacity_conservation : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    CentrePair.capacity (sectorPairOn w (stageAfter p N)) =
      CentrePair.capacity (pairedPair w p N) +
        CentrePair.capacity (returnPair w p N) +
        CentrePair.capacity (cutoffBoundaryPair w p N)
  closed_generation_capacity : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    CentrePair.capacity (beforePair w p N) +
        CentrePair.capacity (sectorPairOn w
          (SignedGaussianEnergy.rootRange N \ stageBefore p N)) =
      CentrePair.capacity (sectorPairOn w (stageAfter p N)) +
        CentrePair.capacity (sectorPairOn w
          (SignedGaussianEnergy.rootRange N \ stageAfter p N))
  transverse_capacity_transfer : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    (∀ n, 0 ≤ w n) →
    transverseCapacity (sectorPairOn w (stageAfter p N)) =
      transverseCapacity (beforePair w p N) +
        transverseCapacity (returnPair w p N) +
        CentrePair.mixingDissipation (beforePair w p N) (returnPair w p N)
  weighted_capacity_conservation : ∀ sigma N, capacityBudget sigma N =
    ∫⁻ u : ℝ, logWeight sigma u *
      (ENNReal.ofReal (CentrePair.capacity (fiveWindowPair (expScale u) N)) +
        ENNReal.ofReal (CentrePair.capacity (outsidePair 5 (expScale u) N)))
  finite_window_probabilities : ∀ L N,
    CentrePair.capacity (fiveWindowPair L N) ≠ 0 →
      CentrePair.positiveProbability (fiveWindowPair L N) +
        CentrePair.negativeProbability (fiveWindowPair L N) = 1
  capacity_restoration : ∀ L N,
    coherentEnergy (fiveWindowPair L N) =
      CentrePair.capacity (fiveWindowPair L N) ^ 2 *
        (1 - CentrePair.centreVariance (fiveWindowPair L N))
  uniform_window_capacity : ∀ sigma, 1 / 2 < sigma →
    (⨆ N : ℕ, fiveCapacityBudget sigma N) < ∞
  uniform_normalized_window : ∀ sigma, 1 / 2 < sigma →
    (⨆ N : ℕ, fiveNormalizedBudget sigma N) < ∞
  restored_window_budget : ∀ sigma N, fiveCoherentBudget sigma N =
    ∫⁻ u : ℝ, logWeight sigma u * ENNReal.ofReal
      (CentrePair.capacity (fiveWindowPair (expScale u) N) ^ 2 *
        (1 - CentrePair.centreVariance (fiveWindowPair (expScale u) N)))

theorem conclusions : Conclusions where
  window_capacity_conservation := fiveWindow_capacity_conservation
  joint_capacity_conservation := windowed_capacity_jointFlip
  generation_capacity_conservation := generated_capacity_conservation
  closed_generation_capacity := generated_closed_capacity_conservation
  transverse_capacity_transfer := generated_transverse_capacity_transfer
  weighted_capacity_conservation := fiveCapacityBudget_conservation
  finite_window_probabilities := fiveWindow_probabilities
  capacity_restoration := fiveWindow_capacity_restored
  uniform_window_capacity := fun sigma hsigma =>
    lt_of_le_of_lt (iSup_le fun N => fiveCapacityBudget_uniform sigma hsigma N)
      (uniformCapacityBound_lt_top sigma hsigma)
  uniform_normalized_window := fun sigma hsigma =>
    lt_of_le_of_lt (iSup_le fun N => fiveNormalizedBudget_uniform sigma hsigma N)
      (uniformCapacityBound_lt_top sigma hsigma)
  restored_window_budget := fiveCoherentBudget_capacity_restored

end GeneratedFoundations.Analysis.CapacityRestoredWindowBudget
