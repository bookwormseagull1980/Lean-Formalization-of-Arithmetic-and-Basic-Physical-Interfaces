module

public import GeneratedFoundations.Physical.SourceTTComparisonTransport

/-!
# Information retained by the TT capacity comparison

The complete powers of the capacity distinguish its response values, but
they do not distinguish all mass fractions. The actual logarithmic mass
variation supplies the missing directional information. These statements
concern a projection of the fixed source comparison; they assert no
nonuniqueness of the original source law.
-/

@[expose] public section
noncomputable section

namespace GeneratedFoundations.Physical.SourceTTComparisonInformation

open SourceTensorResponseEndpoint

/-- The generator already computed from the original precision change
`b ↦ exp(z) b`, written as a function of its mass fraction. -/
def massGenerator (y : ℝ) : ℝ := massWeightedResponse y * (1 - 3 * y)

theorem actual_capacity_hasDerivAt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b)
    (z u : ℝ) :
    HasDerivAt (fun t => SourceTTComparisonTransport.capacity a b t u)
      (massGenerator (SourceTTCollectiveVariance.fraction a b z u)) z :=
  SourceTTComparisonTransport.capacity_hasDerivAt ha hb z u

def firstFraction : ℝ := 1 / 4

def secondFraction : ℝ := (7 - Real.sqrt 13) / 8

theorem sqrt_thirteen_bounds : (3 : ℝ) < Real.sqrt 13 ∧ Real.sqrt 13 < 4 := by
  have hn := Real.sqrt_nonneg (13 : ℝ)
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  constructor <;> nlinarith

theorem firstFraction_mem : firstFraction ∈ Set.Icc (0 : ℝ) 1 := by
  norm_num [firstFraction]

theorem secondFraction_mem : secondFraction ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨h₀, h₁⟩ := sqrt_thirteen_bounds
  constructor <;> dsimp [secondFraction] <;> linarith

theorem secondFraction_gt_oneThird : (1 / 3 : ℝ) < secondFraction := by
  have hs := sqrt_thirteen_bounds.2
  dsimp [secondFraction]
  linarith

theorem first_capacity : massWeightedResponse firstFraction = (9 / 64 : ℝ) := by
  norm_num [firstFraction, massWeightedResponse]

theorem second_capacity : massWeightedResponse secondFraction = (9 / 64 : ℝ) := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hc := congrArg (fun x : ℝ => x * Real.sqrt 13) hs
  dsimp [secondFraction, massWeightedResponse]
  nlinarith

theorem all_capacity_powers_equal (n : ℕ) :
    massWeightedResponse firstFraction ^ n = massWeightedResponse secondFraction ^ n := by
  rw [first_capacity, second_capacity]

theorem first_massGenerator : massGenerator firstFraction = (9 / 256 : ℝ) := by
  norm_num [massGenerator, firstFraction, massWeightedResponse]

theorem first_massGenerator_pos : 0 < massGenerator firstFraction := by
  rw [first_massGenerator]
  norm_num

theorem second_massGenerator :
    massGenerator secondFraction = (-117 + 27 * Real.sqrt 13) / 512 := by
  rw [massGenerator, second_capacity]
  dsimp [secondFraction]
  ring

theorem second_massGenerator_neg : massGenerator secondFraction < 0 := by
  rw [massGenerator, second_capacity]
  have hs := secondFraction_gt_oneThird
  nlinarith

/-- Even all capacity powers can agree while the actual source variation
has opposite signs. The projection to the capacity is therefore not a
closed scalar coordinate for this variation. -/
theorem equal_powers_opposite_variation :
    (∀ n : ℕ, massWeightedResponse firstFraction ^ n =
      massWeightedResponse secondFraction ^ n) ∧
      0 < massGenerator firstFraction ∧ massGenerator secondFraction < 0 :=
  ⟨all_capacity_powers_equal, first_massGenerator_pos, second_massGenerator_neg⟩

theorem massGenerator_not_function_of_capacity :
    ¬ ∃ F : ℝ → ℝ, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      F (massWeightedResponse y) = massGenerator y := by
  rintro ⟨F, hF⟩
  have h₁ := hF firstFraction firstFraction_mem
  have h₂ := hF secondFraction secondFraction_mem
  rw [first_capacity] at h₁
  rw [second_capacity] at h₂
  have hpos := first_massGenerator_pos
  have hneg := second_massGenerator_neg
  linarith

/-- Away from zero capacity, adding the actual mass derivative recovers
the mass fraction exactly. No independent source parameter is added. -/
theorem fraction_reconstruction {y : ℝ} (hy : massWeightedResponse y ≠ 0) :
    y = (1 - massGenerator y / massWeightedResponse y) / 3 := by
  unfold massGenerator
  field_simp [hy]
  ring

/-- Joint capacity and derivative readouts distinguish every pair of
positive-capacity mass fractions. -/
theorem joint_readout_injective {y z : ℝ}
    (hy : massWeightedResponse y ≠ 0) (hz : massWeightedResponse z ≠ 0)
    (hcap : massWeightedResponse y = massWeightedResponse z)
    (hgen : massGenerator y = massGenerator z) : y = z := by
  rw [fraction_reconstruction hy, fraction_reconstruction hz, hcap, hgen]

end GeneratedFoundations.Physical.SourceTTComparisonInformation
