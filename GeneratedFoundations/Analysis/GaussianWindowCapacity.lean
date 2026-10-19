module

public import GeneratedFoundations.Analysis.CapacityEnergyLedger
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Finite Gaussian windows and the complete capacity ledger

An observation level partitions the generated square spectrum at
`n^2 < R * L^2`. Both parts retain the original Gaussian endpoint weights
and centre characters. The outside part remains in the response ledger.

The level-five instance has edge `n^2 < 5 * L^2`. Window level, observation
scale and finite natural cutoff index an observation of the same generated
source; none changes the root datum or supplies new arithmetic coefficients.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.GaussianWindowCapacity

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedMobiusObservation SignedGaussianEnergy
open CenterEndpointPotential CanonicalMobiusReadout CanonicalEndpointLedger
open MaximumPrimeFactorStage CapacityEnergyLedger
open NaturalCutoffPrimeDescent

/-- The dimensionless observation level is tested on the generated square
spectrum, with a strict boundary convention. -/
def InWindow (R : ℝ) (L : PositiveScale) (n : ℕ) : Prop :=
  (n : ℝ) ^ 2 < R * L.1 ^ 2

/-- The original endpoint weight restricted to the visible part. -/
def windowedGaussianMass (R : ℝ) (L : PositiveScale) (n : ℕ) : ℝ := by
  classical
  exact if InWindow R L n then gaussianWindowMass L.1 n else 0

theorem windowedGaussianMass_nonneg (R : ℝ) (L : PositiveScale) (n : ℕ) :
    0 ≤ windowedGaussianMass R L n := by
  classical
  unfold windowedGaussianMass
  split
  · exact endpointWeight_nonneg L.1 n
  · exact le_rfl

def visibleLabels (R : ℝ) (L : PositiveScale) (N : ℕ) : Finset ℕ := by
  classical
  exact (rootRange N).filter (InWindow R L)

def outsideLabels (R : ℝ) (L : PositiveScale) (N : ℕ) : Finset ℕ := by
  classical
  exact (rootRange N).filter fun n => ¬InWindow R L n

def visiblePair (R : ℝ) (L : PositiveScale) (N : ℕ) : CentrePair :=
  sectorPairOn (gaussianWindowMass L.1) (visibleLabels R L N)

def outsidePair (R : ℝ) (L : PositiveScale) (N : ℕ) : CentrePair :=
  sectorPairOn (gaussianWindowMass L.1) (outsideLabels R L N)

/-- Filtering the actual labels and restricting their Gaussian weights give
the same pair of positive centre sectors. -/
theorem visiblePair_eq_windowed_source (R : ℝ) (L : PositiveScale) (N : ℕ) :
    visiblePair R L N = sectorPair (windowedGaussianMass R L) N := by
  classical
  unfold visiblePair sectorPairOn visibleLabels sectorPair
    positiveSectorMass negativeSectorMass
  congr 1 <;> rw [Finset.sum_filter] <;> apply Finset.sum_congr rfl <;>
    intro n _ <;> by_cases hw : InWindow R L n <;>
    simp [windowedGaussianMass, hw]

/-- The concrete level-five window of the same positive arithmetic source. -/
def fiveWindowPair (L : PositiveScale) (N : ℕ) : CentrePair :=
  visiblePair 5 L N

/-- An explicit finite natural cutoff containing every visible mode. -/
def windowCutoff (R : ℝ) (L : PositiveScale) : ℕ :=
  Nat.ceil (Real.sqrt R * L.1)

theorem inWindow_iff_edge {R : ℝ} (hR : 0 ≤ R) (L : PositiveScale) (n : ℕ) :
    InWindow R L n ↔ (n : ℝ) < Real.sqrt R * L.1 := by
  have hedge : 0 ≤ Real.sqrt R * L.1 := mul_nonneg (Real.sqrt_nonneg _) L.2.le
  have hsq : (Real.sqrt R * L.1) ^ 2 = R * L.1 ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hR]
  rw [InWindow, ← hsq, sq_lt_sq₀ (Nat.cast_nonneg _) hedge]

theorem label_le_windowCutoff {R : ℝ} (hR : 0 ≤ R) (L : PositiveScale)
    {n : ℕ} (hn : InWindow R L n) : n ≤ windowCutoff R L := by
  have hedge := (inWindow_iff_edge hR L n).mp hn
  have hcast : (n : ℝ) ≤ (windowCutoff R L : ℝ) :=
    hedge.le.trans (Nat.le_ceil _)
  exact_mod_cast hcast

@[simp] theorem mem_visibleLabels (R : ℝ) (L : PositiveScale) (N n : ℕ) :
    n ∈ visibleLabels R L N ↔ n ∈ rootRange N ∧ InWindow R L n := by
  classical
  simp [visibleLabels]

@[simp] theorem mem_outsideLabels (R : ℝ) (L : PositiveScale) (N n : ℕ) :
    n ∈ outsideLabels R L N ↔ n ∈ rootRange N ∧ ¬InWindow R L n := by
  classical
  simp [outsideLabels]

theorem window_partition (R : ℝ) (L : PositiveScale) (N : ℕ) :
    visibleLabels R L N ∪ outsideLabels R L N = rootRange N := by
  classical
  ext n
  simp only [Finset.mem_union, mem_visibleLabels, mem_outsideLabels]
  tauto

theorem window_disjoint (R : ℝ) (L : PositiveScale) (N : ℕ) :
    Disjoint (visibleLabels R L N) (outsideLabels R L N) := by
  classical
  apply Finset.disjoint_left.mpr
  intro n hv ho
  exact ((mem_outsideLabels R L N n).mp ho).2
    ((mem_visibleLabels R L N n).mp hv).2

/-- Once the natural prefix contains the Gaussian window, its visible part
is independent of further generation. The retained outside still changes. -/
theorem visibleLabels_stabilize {R : ℝ} (hR : 0 ≤ R) (L : PositiveScale)
    {N : ℕ} (hN : windowCutoff R L ≤ N) :
    visibleLabels R L N = visibleLabels R L (windowCutoff R L) := by
  ext n
  simp only [mem_visibleLabels, rootRange, Finset.mem_Icc]
  constructor
  · intro h
    exact ⟨⟨h.1.1, label_le_windowCutoff hR L h.2⟩, h.2⟩
  · intro h
    exact ⟨⟨h.1.1, h.1.2.trans hN⟩, h.2⟩

theorem fiveWindowPair_stabilize (L : PositiveScale) {N : ℕ}
    (hN : windowCutoff 5 L ≤ N) :
    fiveWindowPair L N = fiveWindowPair L (windowCutoff 5 L) := by
  unfold fiveWindowPair visiblePair
  rw [visibleLabels_stabilize (by norm_num : (0 : ℝ) ≤ 5) L hN]

/-- Exact reconstruction of both nonnegative centre sectors. -/
theorem pair_reconstruction (R : ℝ) (L : PositiveScale) (N : ℕ) :
    canonicalEndpointPair L N =
      CentrePair.add (visiblePair R L N) (outsidePair R L N) := by
  have h := sectorPairOn_union (gaussianWindowMass L.1)
    (window_disjoint R L N)
  rw [window_partition] at h
  exact h

theorem visiblePair_nonnegative (R : ℝ) (L : PositiveScale) (N : ℕ) :
    0 ≤ (visiblePair R L N).positive ∧ 0 ≤ (visiblePair R L N).negative :=
  sectorPairOn_nonnegative _ _ (fun n _ => endpointWeight_nonneg L.1 n)

theorem outsidePair_nonnegative (R : ℝ) (L : PositiveScale) (N : ℕ) :
    0 ≤ (outsidePair R L N).positive ∧ 0 ≤ (outsidePair R L N).negative :=
  sectorPairOn_nonnegative _ _ (fun n _ => endpointWeight_nonneg L.1 n)

/-- Windowing redistributes the capacity without discarding the outside. -/
theorem capacity_conservation (R : ℝ) (L : PositiveScale) (N : ℕ) :
    CentrePair.capacity (visiblePair R L N) +
        CentrePair.capacity (outsidePair R L N) =
      finiteSupportCapacity (gaussianWindowMass L.1) N := by
  rw [← CentrePair.capacity_add, ← pair_reconstruction,
    canonicalEndpointPair_capacity]

theorem signed_reconstruction (R : ℝ) (L : PositiveScale) (N : ℕ) :
    CentrePair.signed (visiblePair R L N) +
        CentrePair.signed (outsidePair R L N) = canonicalOccupationAmplitude L N := by
  rw [← CentrePair.signed_add, ← pair_reconstruction, canonicalEndpointPair_signed]

/-- The full energy contains the visible--outside cross term. -/
theorem coherentEnergy_reconstruction (R : ℝ) (L : PositiveScale) (N : ℕ) :
    canonicalOccupationEnergy L N =
      coherentEnergy (visiblePair R L N) + coherentEnergy (outsidePair R L N) +
        2 * CentrePair.signed (visiblePair R L N) *
          CentrePair.signed (outsidePair R L N) := by
  have h := coherentEnergy_add (visiblePair R L N) (outsidePair R L N)
  rw [← pair_reconstruction] at h
  simpa only [coherentEnergy, canonicalEndpointPair_signed,
    canonicalOccupationEnergy] using h

/-- The normalized potential obeys the exact joining ledger, including an
empty visible or outside sector. -/
theorem window_potential_ledger (R : ℝ) (L : PositiveScale) (N : ℕ) :
    CentrePair.quadraticPotential (canonicalEndpointPair L N) =
      CentrePair.quadraticPotential (visiblePair R L N) +
        CentrePair.quadraticPotential (outsidePair R L N) -
        CentrePair.joinDissipation (visiblePair R L N) (outsidePair R L N) := by
  obtain ⟨hvp, hvn⟩ := visiblePair_nonnegative R L N
  obtain ⟨hop, hon⟩ := outsidePair_nonnegative R L N
  have h := quadraticPotential_join_identity_nonnegative
    (visiblePair R L N) (outsidePair R L N) hvp hvn hop hon
  rw [← pair_reconstruction] at h
  linarith

/-- The finite window uses the invariant ratio of occupation to scale. -/
theorem inWindow_iff_ratio (R : ℝ) (L : PositiveScale) (n : ℕ) :
    InWindow R L n ↔ ((n : ℝ) / L.1) ^ 2 < R := by
  rw [InWindow, div_pow, div_lt_iff₀ (sq_pos_of_pos L.2)]

theorem window_jointFlip (R : ℝ) (p : PrimeIndex)
    (x : Occupation × PositiveScale) :
    InWindow R (jointFlip p x).2 (label (jointFlip p x).1) ↔
      InWindow R x.2 (label x.1) := by
  rw [inWindow_iff_ratio, inWindow_iff_ratio]
  change ratio (jointFlip p x) ^ 2 < R ↔ ratio x ^ 2 < R
  rw [ratio_jointFlip]

/-- A genuine prime birth transports the observation scale by `L / p`.
The cutoff test has exactly the same covariance as the Gaussian weight. -/
theorem inWindow_prime_mul (R : ℝ) (L : PositiveScale) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    InWindow R L (p * n) ↔
      InWindow R ⟨L.1 / (p : ℝ), div_pos L.2 (by exact_mod_cast hp.pos)⟩ n := by
  rw [inWindow_iff_ratio, inWindow_iff_ratio]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hratio : (↑(p * n) : ℝ) / L.1 = (n : ℝ) / (L.1 / (p : ℝ)) := by
    push_cast
    field_simp [hp0]
  rw [hratio]

/-- The actual windowed response transports with the prime birth, including
the strict Gaussian-window boundary. -/
theorem windowedGaussianMass_prime_mul (R : ℝ) (L : PositiveScale) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    windowedGaussianMass R L (p * n) =
      windowedGaussianMass R
        ⟨L.1 / (p : ℝ), div_pos L.2 (by exact_mod_cast hp.pos)⟩ n := by
  classical
  simp only [windowedGaussianMass, inWindow_prime_mul R L hp n,
    gaussianWindowMass_prime_mul L hp n]

theorem windowed_returnPair_eq_transport (R : ℝ) (L : PositiveScale)
    {p N : ℕ} (hp : p.Prime) :
    returnPair (windowedGaussianMass R L) p N =
      pairedPair (windowedGaussianMass R
        ⟨L.1 / (p : ℝ), div_pos L.2 (by exact_mod_cast hp.pos)⟩) p N := by
  unfold returnPair pairedPair
  congr 1
  funext n
  exact windowedGaussianMass_prime_mul R L hp n

/-- Complete signed energy transport for the finite Gaussian window. The
returned amplitude has the transported scale, and its old--new cross term
is retained before any bound is applied. -/
theorem windowed_stage_coherentEnergy_correlation (R : ℝ) (L : PositiveScale)
    {p N : ℕ} (hp : p.Prime) :
    coherentEnergy (sectorPairOn (windowedGaussianMass R L) (stageAfter p N)) -
        coherentEnergy (beforePair (windowedGaussianMass R L) p N) =
      coherentEnergy (pairedPair (windowedGaussianMass R
        ⟨L.1 / (p : ℝ), div_pos L.2 (by exact_mod_cast hp.pos)⟩) p N) -
        2 * CentrePair.signed (beforePair (windowedGaussianMass R L) p N) *
          CentrePair.signed (pairedPair (windowedGaussianMass R
            ⟨L.1 / (p : ℝ), div_pos L.2 (by exact_mod_cast hp.pos)⟩) p N) := by
  have h := generated_stage_coherentEnergy_correlation
    (windowedGaussianMass R L) (N := N) hp
  rw [windowed_returnPair_eq_transport R L hp] at h
  exact h

/-- Gaussian attenuation beyond the actual square-spectrum boundary. -/
theorem outside_weight_le (R : ℝ) (L : PositiveScale) {n : ℕ}
    (hout : ¬InWindow R L n) : gaussianWindowMass L.1 n ≤ Real.exp (-R) := by
  have hsq : R ≤ (n : ℝ) ^ 2 / L.1 ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos L.2)).mpr
    exact le_of_not_gt hout
  calc
    gaussianWindowMass L.1 n ≤ gaussianRootMass 1 L.1 n :=
      sub_le_self _ (Real.exp_nonneg _)
    _ ≤ Real.exp (-R) := by
      unfold gaussianRootMass
      apply Real.exp_le_exp.mpr
      calc
        -1 * (n : ℝ) ^ 2 / L.1 ^ 2 = -((n : ℝ) ^ 2 / L.1 ^ 2) := by ring
        _ ≤ -R := neg_le_neg hsq

/-- The outside capacity is bounded using only the true squarefree support.
The cardinal factor is displayed explicitly. -/
theorem outside_capacity_le (R : ℝ) (L : PositiveScale) (N : ℕ) :
    CentrePair.capacity (outsidePair R L N) ≤
      ((outsideLabels R L N).card : ℝ) * Real.exp (-R) := by
  classical
  unfold outsidePair sectorPairOn CentrePair.capacity
  rw [← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _n ∈ outsideLabels R L N, Real.exp (-R) := by
      apply Finset.sum_le_sum
      intro n hn
      have hw := outside_weight_le R L ((mem_outsideLabels R L N n).mp hn).2
      by_cases hp : generatedMoebius n = 1
      · have hm : generatedMoebius n ≠ -1 := by omega
        simpa [hp, hm] using hw
      · by_cases hm : generatedMoebius n = -1
        · simpa [hp, hm] using hw
        · simp only [hp, hm, ↓reduceIte, add_zero]
          exact Real.exp_nonneg _
    _ = _ := by simp

/-- Centre signs cannot enlarge the positive outside capacity. -/
theorem outside_signed_abs_le_capacity (R : ℝ) (L : PositiveScale) (N : ℕ) :
    |CentrePair.signed (outsidePair R L N)| ≤
      CentrePair.capacity (outsidePair R L N) := by
  obtain ⟨hp, hn⟩ := outsidePair_nonnegative R L N
  rw [abs_le]
  dsimp [CentrePair.signed, CentrePair.capacity]
  constructor <;> linarith

/-- Finite energy error certified by the actual retained outside capacity.
The visible--outside interaction contributes the linear term. -/
theorem coherentEnergy_window_error (R : ℝ) (L : PositiveScale) (N : ℕ) :
    |canonicalOccupationEnergy L N - coherentEnergy (visiblePair R L N)| ≤
      CentrePair.capacity (outsidePair R L N) ^ 2 +
        2 * |CentrePair.signed (visiblePair R L N)| *
          CentrePair.capacity (outsidePair R L N) := by
  have he := coherentEnergy_reconstruction R L N
  have heq : canonicalOccupationEnergy L N - coherentEnergy (visiblePair R L N) =
      coherentEnergy (outsidePair R L N) +
        2 * CentrePair.signed (visiblePair R L N) *
          CentrePair.signed (outsidePair R L N) := by linarith
  obtain ⟨hop, hon⟩ := outsidePair_nonnegative R L N
  have hsq := CentrePair.signed_sq_le_capacity_sq (outsidePair R L N) hop hon
  have habs := outside_signed_abs_le_capacity R L N
  rw [heq, coherentEnergy]
  calc
    _ ≤ |CentrePair.signed (outsidePair R L N) ^ 2| +
        |2 * CentrePair.signed (visiblePair R L N) *
          CentrePair.signed (outsidePair R L N)| := abs_add_le _ _
    _ = CentrePair.signed (outsidePair R L N) ^ 2 +
        2 * |CentrePair.signed (visiblePair R L N)| *
          |CentrePair.signed (outsidePair R L N)| := by
      rw [abs_of_nonneg (sq_nonneg _), abs_mul, abs_mul]
      norm_num
    _ ≤ _ := add_le_add hsq (mul_le_mul_of_nonneg_left habs
      (mul_nonneg (by norm_num) (abs_nonneg _)))

theorem outside_amplitude_le (R : ℝ) (L : PositiveScale) (N : ℕ) :
    |canonicalOccupationAmplitude L N - CentrePair.signed (visiblePair R L N)| ≤
      ((outsideLabels R L N).card : ℝ) * Real.exp (-R) := by
  have hs := signed_reconstruction R L N
  have heq : canonicalOccupationAmplitude L N -
      CentrePair.signed (visiblePair R L N) =
      CentrePair.signed (outsidePair R L N) := by linarith
  rw [heq]
  exact (outside_signed_abs_le_capacity R L N).trans (outside_capacity_le R L N)

/-- The concrete level-five response and its retained outside reconstruct
the complete canonical endpoint source. -/
theorem five_window_complete (L : PositiveScale) (N : ℕ) :
    canonicalEndpointPair L N =
      CentrePair.add (fiveWindowPair L N) (outsidePair 5 L N) :=
  pair_reconstruction 5 L N

/-- The window construction is an output about the existing source. Its
parameters specify observations, not alternative generated sources. -/
structure Conclusions : Prop where
  full_source : ∀ (R : ℝ) (L : PositiveScale) (N : ℕ),
    canonicalEndpointPair L N =
      CentrePair.add (visiblePair R L N) (outsidePair R L N)
  capacity : ∀ (R : ℝ) (L : PositiveScale) (N : ℕ),
    CentrePair.capacity (visiblePair R L N) +
        CentrePair.capacity (outsidePair R L N) =
      finiteSupportCapacity (gaussianWindowMass L.1) N
  full_energy : ∀ (R : ℝ) (L : PositiveScale) (N : ℕ),
    canonicalOccupationEnergy L N =
      coherentEnergy (visiblePair R L N) + coherentEnergy (outsidePair R L N) +
        2 * CentrePair.signed (visiblePair R L N) *
          CentrePair.signed (outsidePair R L N)
  joint_covariance : ∀ (R : ℝ) (p : PrimeIndex)
      (x : Occupation × PositiveScale),
    InWindow R (jointFlip p x).2 (label (jointFlip p x).1) ↔
      InWindow R x.2 (label x.1)
  gaussian_tail : ∀ (R : ℝ) (L : PositiveScale) (N : ℕ),
    |canonicalOccupationAmplitude L N - CentrePair.signed (visiblePair R L N)| ≤
      ((outsideLabels R L N).card : ℝ) * Real.exp (-R)
  empty_safe_energy : ∀ (L : PositiveScale) (N : ℕ),
    CentrePair.capacity (canonicalEndpointPair L N) *
        CentrePair.quadraticPotential (canonicalEndpointPair L N) =
      canonicalOccupationEnergy L N

theorem conclusions : Conclusions where
  full_source := pair_reconstruction
  capacity := capacity_conservation
  full_energy := coherentEnergy_reconstruction
  joint_covariance := window_jointFlip
  gaussian_tail := outside_amplitude_le
  empty_safe_energy := canonical_energy_reconstruction

end GeneratedFoundations.Analysis.GaussianWindowCapacity
