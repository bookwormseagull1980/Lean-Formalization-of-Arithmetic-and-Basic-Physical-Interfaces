module

public import GeneratedFoundations.Analysis.PrimeCylinderScaleBudget
public import GeneratedFoundations.Analysis.CapacityEnergyLedger

/-!
# Scale budgets of the complete generated natural prefixes

Every squarefree occupation has its unique positive natural label. Translating
the logarithmic observation scale by the logarithm of that label gives its
exact Mellin return. Summing these returns controls the positive capacity and
the capacity-normalized central potential uniformly over all natural prefixes.

The coherent energy is reconstructed with its *actual capacity factor*.
Consequently the last identity below retains every signed cross term and
distinguishes the normalized budget from the complete quadratic observation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators

namespace GeneratedFoundations.Analysis.NaturalSourceScaleBudget

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedMobiusObservation SignedGaussianEnergy CanonicalMobiusReadout
open CanonicalEndpointLedger CenterEndpointPotential CapacityEnergyLedger
open PrimeCylinderScaleBudget

local instance (n : ℕ) : Decidable (GeneratedSquarefree n) := Classical.propDecidable _

/-- The same positive capacity, on logarithmic observation scale. -/
def capacityProfile (N : ℕ) (u : ℝ) : ℝ :=
  CentrePair.capacity (canonicalEndpointPair (expScale u) N)

def normalizedProfile (N : ℕ) (u : ℝ) : ℝ :=
  CentrePair.quadraticPotential (canonicalEndpointPair (expScale u) N)

def capacityBudget (sigma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ, logWeight sigma u * ENNReal.ofReal (capacityProfile N u)

def normalizedBudget (sigma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ, logWeight sigma u * ENNReal.ofReal (normalizedProfile N u)

def coherentBudget (sigma : ℝ) (N : ℕ) : ℝ≥0∞ :=
  ∫⁻ u : ℝ, logWeight sigma u *
    ENNReal.ofReal (canonicalOccupationEnergy (expScale u) N)

theorem capacityProfile_eq (N : ℕ) (u : ℝ) :
    capacityProfile N u = ∑ n ∈ rootRange N,
      if GeneratedSquarefree n then gaussianWindowMass (Real.exp u) n else 0 := by
  classical
  rw [capacityProfile, canonicalEndpointPair_capacity, finiteSupportCapacity]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hs : GeneratedSquarefree n <;> simp [squarefreeProjector, hs, expScale]

theorem gaussian_label_translation {n : ℕ} (hn : 0 < n) (u : ℝ) :
    gaussianWindowMass (Real.exp u) n =
      potentialProfile ∅ (u - Real.log (n : ℝ)) := by
  rw [potentialProfile_empty]
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have he := Real.exp_log hn'
  have heq : (Real.exp (u - Real.log (n : ℝ)))⁻¹ =
      (n : ℝ) / Real.exp u := by
    rw [Real.exp_sub, he]
    field_simp
  simp only [gaussianWindowMass, gaussianRootMass, gaussianResponse, ratio,
    expScale, label, Finset.prod_empty, Nat.cast_one, one_div, heq]
  congr 1 <;> field_simp

theorem root_scale_integral {n : ℕ} (hn : 0 < n) (sigma : ℝ) :
    (∫⁻ u : ℝ, logWeight sigma u *
      ENNReal.ofReal (gaussianWindowMass (Real.exp u) n)) =
      ENNReal.ofReal ((n : ℝ) ^ (-2 * sigma)) * potentialBudget sigma ∅ := by
  simp_rw [gaussian_label_translation hn]
  rw [weighted_lintegral_shift sigma (Real.log (n : ℝ))
    (fun u => ENNReal.ofReal (potentialProfile ∅ u))
    (measurable_potentialProfile ∅).ennreal_ofReal]
  congr 1
  unfold logWeight
  rw [Real.rpow_def_of_pos (Nat.cast_pos.mpr hn)]
  congr 2
  ring

/-- Exact generated-occupation formula, including the unit occupation and
excluding repeated prime occupation by the actual source projector. -/
theorem capacityBudget_eq (sigma : ℝ) (N : ℕ) :
    capacityBudget sigma N =
      (∑ n ∈ rootRange N, if GeneratedSquarefree n then
        ENNReal.ofReal ((n : ℝ) ^ (-2 * sigma)) else 0) *
          potentialBudget sigma ∅ := by
  classical
  unfold capacityBudget
  simp_rw [capacityProfile_eq]
  have hnonneg : ∀ (u : ℝ) (n : ℕ),
      0 ≤ (if GeneratedSquarefree n then gaussianWindowMass (Real.exp u) n else 0) := by
    intro u n
    split
    · exact endpointWeight_nonneg _ _
    · exact le_rfl
  simp_rw [ENNReal.ofReal_sum_of_nonneg (fun n _ => hnonneg _ n), Finset.mul_sum]
  rw [lintegral_finsetSum]
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs : GeneratedSquarefree n
    · simp only [hs, ↓reduceIte]
      exact root_scale_integral (by have := (Finset.mem_Icc.mp hn).1; omega) sigma
    · simp [hs]
  · intro n hn
    apply (measurable_logWeight sigma).mul
    by_cases hs : GeneratedSquarefree n
    · simp only [hs, ↓reduceIte]
      unfold gaussianWindowMass gaussianRootMass
      fun_prop
    · simp only [hs, ↓reduceIte, ENNReal.ofReal_zero]
      exact measurable_const

/-- An explicit prefix-independent bound. Its series runs over *all* natural
labels and therefore also bounds the generated squarefree occupation support. -/
def uniformCapacityBound (sigma : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (∑' n : ℕ, (n : ℝ) ^ (-2 * sigma)) * potentialBudget sigma ∅

theorem capacityBudget_uniform (sigma : ℝ) (hsigma : 1 / 2 < sigma) (N : ℕ) :
    capacityBudget sigma N ≤ uniformCapacityBound sigma := by
  classical
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * sigma)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  rw [capacityBudget_eq]
  unfold uniformCapacityBound
  apply mul_le_mul _ le_rfl bot_le bot_le
  calc
    _ ≤ ∑ n ∈ rootRange N, ENNReal.ofReal ((n : ℝ) ^ (-2 * sigma)) := by
      apply Finset.sum_le_sum
      intro n hn
      split <;> simp
    _ = ENNReal.ofReal (∑ n ∈ rootRange N, (n : ℝ) ^ (-2 * sigma)) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro n hn
      exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (hsum.sum_le_tsum (rootRange N) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))

theorem uniformCapacityBound_lt_top (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    uniformCapacityBound sigma < ∞ := by
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (potentialBudget_empty_lt_top sigma (by linarith))

theorem normalizedProfile_le_capacity (N : ℕ) (u : ℝ) :
    normalizedProfile N u ≤ capacityProfile N u := by
  obtain ⟨hp, hm⟩ := canonicalEndpointPair_nonnegative (expScale u) N
  have h := transverseCapacity_nonneg (canonicalEndpointPair (expScale u) N) hp hm
  exact sub_nonneg.mp h

theorem normalizedBudget_uniform (sigma : ℝ) (hsigma : 1 / 2 < sigma) (N : ℕ) :
    normalizedBudget sigma N ≤ uniformCapacityBound sigma := by
  apply le_trans (lintegral_mono fun u =>
    mul_le_mul le_rfl (ENNReal.ofReal_le_ofReal
      (normalizedProfile_le_capacity N u)) bot_le bot_le)
    (capacityBudget_uniform sigma hsigma N)

/-- The supremum over all complete natural prefixes is finite, rather than
only the budget of each individual finite prefix. -/
theorem capacityBudget_iSup_lt_top (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    (⨆ N : ℕ, capacityBudget sigma N) < ∞ :=
  lt_of_le_of_lt (iSup_le fun N => capacityBudget_uniform sigma hsigma N)
    (uniformCapacityBound_lt_top sigma hsigma)

theorem normalizedBudget_iSup_lt_top (sigma : ℝ) (hsigma : 1 / 2 < sigma) :
    (⨆ N : ℕ, normalizedBudget sigma N) < ∞ :=
  lt_of_le_of_lt (iSup_le fun N => normalizedBudget_uniform sigma hsigma N)
    (uniformCapacityBound_lt_top sigma hsigma)

/-- Exact conversion to the complete coherent observation. Capacity remains
inside the same scale integral and is not replaced by its normalized value. -/
theorem coherentBudget_eq_capacityWeightedPotential (sigma : ℝ) (N : ℕ) :
    coherentBudget sigma N =
      ∫⁻ u : ℝ, logWeight sigma u *
        (ENNReal.ofReal (capacityProfile N u) *
          ENNReal.ofReal (normalizedProfile N u)) := by
  apply lintegral_congr
  intro u
  have hc := CentrePair.capacity_nonneg _
    (canonicalEndpointPair_nonnegative (expScale u) N).1
    (canonicalEndpointPair_nonnegative (expScale u) N).2
  change 0 ≤ capacityProfile N u at hc
  congr 1
  rw [← ENNReal.ofReal_mul hc]
  congr 1
  exact (canonical_energy_reconstruction (expScale u) N).symm

structure Conclusions : Prop where
  exact_capacity : ∀ sigma N, capacityBudget sigma N =
    (∑ n ∈ rootRange N, if GeneratedSquarefree n then
      ENNReal.ofReal ((n : ℝ) ^ (-2 * sigma)) else 0) * potentialBudget sigma ∅
  uniform_capacity : ∀ sigma, 1 / 2 < sigma →
    (⨆ N : ℕ, capacityBudget sigma N) < ∞
  uniform_normalized_potential : ∀ sigma, 1 / 2 < sigma →
    (⨆ N : ℕ, normalizedBudget sigma N) < ∞
  coherent_reconstruction : ∀ sigma N, coherentBudget sigma N =
    ∫⁻ u : ℝ, logWeight sigma u *
      (ENNReal.ofReal (capacityProfile N u) * ENNReal.ofReal (normalizedProfile N u))

theorem conclusions : Conclusions where
  exact_capacity := capacityBudget_eq
  uniform_capacity := capacityBudget_iSup_lt_top
  uniform_normalized_potential := normalizedBudget_iSup_lt_top
  coherent_reconstruction := coherentBudget_eq_capacityWeightedPotential

end GeneratedFoundations.Analysis.NaturalSourceScaleBudget
