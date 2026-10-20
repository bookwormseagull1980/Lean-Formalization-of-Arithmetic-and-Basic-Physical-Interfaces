module

public import GeneratedFoundations.Geometry.SourceConformalResponse
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Variation of the complete common-source scalar response

The shellwise derivative and its summable uniform majorant identify the
curvature with the derivative of the complete response. Both branches use
this same scalar spectrum before dimensional or matter normalization.
-/

@[expose] public section

noncomputable section

open MeasureTheory Topology

namespace GeneratedFoundations.Geometry.SourceConformalVariation

open SourceConformalResponse

set_option backward.isDefEq.respectTransparency false in
/-- Exact derivative of one generated shell, before summing the tower. -/
theorem responseTerm_hasDerivAt (j : ℕ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (responseTerm j) (curvatureTerm j z) z := by
  have hc : conformalIndex j ≠ 0 := (conformalIndex_pos j).ne'
  have hcz : conformalIndex j + z ≠ 0 :=
    (add_pos (conformalIndex_pos j) hz).ne'
  have hd := ((hasDerivAt_id z).const_mul (conformalMultiplicity j)).div
    ((hasDerivAt_const z (conformalIndex j)).mul
      ((hasDerivAt_id z).const_add (conformalIndex j))) (mul_ne_zero hc hcz)
  change HasDerivAt
    (fun y => conformalMultiplicity j * y /
      (conformalIndex j * (conformalIndex j + y)))
    (conformalMultiplicity j / (conformalIndex j + z) ^ 2) z
  convert! hd using 1
  simp only [Pi.mul_apply, id_eq, mul_one, zero_mul, zero_add]
  field_simp
  ring

/-- The complete restoring response has the complete curvature as its actual
derivative. The same summable majorant works on the entire positive axis. -/
theorem completeResponse_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt completeResponse (completeCurvature z) z := by
  apply hasDerivAt_tsum_of_isPreconnected
    (u := fun j => curvatureTerm j 0)
    (g' := fun j y => curvatureTerm j y)
    (t := Set.Ioi (0 : ℝ))
    (y₀ := z) (curvatureTerm_summable (le_refl 0))
    isOpen_Ioi (convex_Ioi (0 : ℝ)).isPreconnected
  · intro j y hy
    exact responseTerm_hasDerivAt j hy
  · intro j y hy
    rw [Real.norm_eq_abs, abs_of_pos (curvatureTerm_pos j hy.le)]
    simp only [curvatureTerm, add_zero]
    apply div_le_div_of_nonneg_left (conformalMultiplicity_pos j).le
      (sq_pos_of_pos (conformalIndex_pos j))
    have hy0 : 0 < y := hy
    nlinarith [conformalIndex_pos j,
      mul_nonneg (conformalIndex_pos j).le hy0.le, sq_nonneg y]
  · exact hz
  · exact responseTerm_summable hz.le
  · exact hz

/-- The potential of the complete response, referenced at its uniquely
selected unit-response balance. The source normalization is the same as
in `canonicalAmplitude`; no second target or quadratic coefficient occurs. -/
def potential (z : ℝ) : ℝ :=
  ∫ t in canonicalAmplitude..z, completeResponse t - canonicalDrive

@[simp] theorem potential_canonical : potential canonicalAmplitude = 0 := by
  simp [potential]

/-- Actual first variation of the complete potential on the positive
intensity domain. Both ends of the integration interval lie in that domain. -/
theorem potential_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt potential (completeResponse z - canonicalDrive) z := by
  have hcont : ContinuousOn (fun t : ℝ => completeResponse t - canonicalDrive)
      (Set.Ioi 0) := by
    intro t ht
    exact ((completeResponse_hasDerivAt ht).sub_const canonicalDrive).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (fun t : ℝ => completeResponse t - canonicalDrive)
      volume canonicalAmplitude z := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hpos : 0 < t := by
      rcases le_total canonicalAmplitude z with h | h
      · rw [Set.uIcc_of_le h] at ht
        exact lt_of_lt_of_le canonicalAmplitude_spec.1 ht.1
      · rw [Set.uIcc_of_ge h] at ht
        exact lt_of_lt_of_le hz ht.1
    exact ((completeResponse_hasDerivAt hpos).sub_const canonicalDrive).continuousAt.continuousWithinAt
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hcont.stronglyMeasurableAtFilter isOpen_Ioi z hz)
    ((completeResponse_hasDerivAt hz).sub_const canonicalDrive).continuousAt

/-- The complete shell curvature is the second derivative of the integrated
potential, with termwise differentiation justified before taking the sum. -/
theorem potential_secondDeriv {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun t : ℝ => deriv potential t) (completeCurvature z) z := by
  apply ((completeResponse_hasDerivAt hz).sub_const canonicalDrive).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hz] with t ht
  exact (potential_hasDerivAt ht).deriv

/-- Stationarity selects exactly the already generated response balance. -/
theorem stationary_iff_canonical {z : ℝ} (hz : 0 < z) :
    deriv potential z = 0 ↔ z = canonicalAmplitude := by
  rw [(potential_hasDerivAt hz).deriv]
  constructor
  · intro h
    exact canonicalAmplitude_unique hz (sub_eq_zero.mp h)
  · intro h
    subst z
    exact sub_eq_zero.mpr canonicalAmplitude_spec.2

theorem potential_curvature_pos {z : ℝ} (hz : 0 < z) :
    0 < deriv (fun t : ℝ => deriv potential t) z := by
  rw [(potential_secondDeriv hz).deriv]
  exact completeCurvature_pos hz.le

/-- Uniqueness concerns positive intensities of this actual complete
potential, rather than a freely supplied stationary-point certificate. -/
theorem existsUnique_stationary :
    ∃! z : ℝ, 0 < z ∧ deriv potential z = 0 := by
  refine ⟨canonicalAmplitude, ⟨canonicalAmplitude_spec.1,
    (stationary_iff_canonical canonicalAmplitude_spec.1).2 rfl⟩, ?_⟩
  intro z hz
  exact (stationary_iff_canonical hz.1).1 hz.2

structure Conclusions : Prop where
  response_derivative : ∀ z, 0 < z →
    HasDerivAt completeResponse (completeCurvature z) z
  first_variation : ∀ z, 0 < z →
    HasDerivAt potential (completeResponse z - canonicalDrive) z
  second_variation : ∀ z, 0 < z →
    HasDerivAt (fun t : ℝ => deriv potential t) (completeCurvature z) z
  unique_stationary : ∃! z : ℝ, 0 < z ∧ deriv potential z = 0
  positive_curvature : ∀ z, 0 < z →
    0 < deriv (fun t : ℝ => deriv potential t) z

theorem generated : Conclusions where
  response_derivative := fun _ hz => completeResponse_hasDerivAt hz
  first_variation := fun _ hz => potential_hasDerivAt hz
  second_variation := fun _ hz => potential_secondDeriv hz
  unique_stationary := existsUnique_stationary
  positive_curvature := fun _ hz => potential_curvature_pos hz

end GeneratedFoundations.Geometry.SourceConformalVariation
