module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Radial second variation of the complete generated response

The positive shell sum is not assigned the name of a curvature without a
derivative calculation. The source shell response differentiates to its
curvature shell. A summable bound, uniform on the positive intensity axis,
then justifies differentiation of the complete generated tower.

In the normalized intensity coordinate the resulting restoring derivative
is the score variance times that complete curvature. It is therefore exactly
the radial mass coefficient already used by the response Hessian.
-/

@[expose] public section

noncomputable section

open MeasureTheory Topology

namespace GeneratedFoundations.Physical.SourceGeneratedRadialVariation

open SourceConformalResponse SourceRadialMassIntertwiner SourceGeneratedYangMillsGap

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

theorem scoreVariance_nonneg (z : ℝ) : 0 ≤ scoreVariance z := by
  exact div_nonneg (mul_nonneg (by norm_num) (sq_nonneg z))
    coefficientCount_pos.le

/-- Actual normalized source restoring force about a positive intensity.
The reference subtraction uses the same complete source at that intensity. -/
def sourceRadialForce (z radial : ℝ) : ℝ :=
  Real.sqrt (scoreVariance z) *
    (completeResponse (z + Real.sqrt (scoreVariance z) * radial) -
      completeResponse z)

@[simp] theorem sourceRadialForce_zero (z : ℝ) :
    sourceRadialForce z 0 = 0 := by
  simp [sourceRadialForce]

set_option backward.isDefEq.respectTransparency false in
/-- The radial mass is derived from the complete source restoring force,
including its normalization, rather than introduced as a quadratic input. -/
theorem sourceRadialForce_hasDerivAt_zero {z : ℝ} (hz : 0 < z) :
    HasDerivAt (sourceRadialForce z) (normalizedRadialMassSq z) 0 := by
  have ha := ((hasDerivAt_id (0 : ℝ)).const_mul
    (Real.sqrt (scoreVariance z))).const_add z
  have hr : HasDerivAt completeResponse (completeCurvature z)
      (z + Real.sqrt (scoreVariance z) * (0 : ℝ)) := by
    simpa using completeResponse_hasDerivAt hz
  have hs := hr.comp 0 ha
  have hf := (hs.sub_const (completeResponse z)).const_mul
    (Real.sqrt (scoreVariance z))
  have hderivative :
      Real.sqrt (scoreVariance z) *
        (completeCurvature z * (Real.sqrt (scoreVariance z) * 1)) =
        normalizedRadialMassSq z := by
    calc
      _ = Real.sqrt (scoreVariance z) ^ 2 * completeCurvature z := by ring
      _ = normalizedRadialMassSq z := by
        rw [Real.sq_sqrt (scoreVariance_nonneg z),
          normalizedRadialMassSq_eq_scoreVariance_mul_completeCurvature]
  convert! hf.congr_deriv hderivative using 1

/-- Differentiation of the full normalized restoring force at any point
where the source intensity remains positive. -/
theorem sourceRadialForce_hasDerivAt {z radial : ℝ}
    (hr : 0 < z + Real.sqrt (scoreVariance z) * radial) :
    HasDerivAt (sourceRadialForce z)
      (scoreVariance z * completeCurvature
        (z + Real.sqrt (scoreVariance z) * radial)) radial := by
  have ha := ((hasDerivAt_id radial).const_mul
    (Real.sqrt (scoreVariance z))).const_add z
  have h := (((completeResponse_hasDerivAt hr).comp radial ha).sub_const
    (completeResponse z)).const_mul (Real.sqrt (scoreVariance z))
  convert! h using 1
  rw [show Real.sqrt (scoreVariance z) *
      (completeCurvature (z + Real.sqrt (scoreVariance z) * radial) *
        (Real.sqrt (scoreVariance z) * 1)) =
      Real.sqrt (scoreVariance z) ^ 2 *
        completeCurvature (z + Real.sqrt (scoreVariance z) * radial) by ring,
    Real.sq_sqrt (scoreVariance_nonneg z)]

/-- The reference-subtracted radial potential is generated by integration
of the complete restoring force; its curvature is not prescribed. -/
def sourceRadialPotential (z radial : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..radial, sourceRadialForce z t

@[simp] theorem sourceRadialPotential_zero (z : ℝ) :
    sourceRadialPotential z 0 = 0 := by
  simp [sourceRadialPotential]

/-- The generated potential differentiates to the original full restoring
force on its positive-intensity interval. -/
theorem sourceRadialPotential_hasDerivAt {z radial : ℝ} (hz : 0 < z)
    (hr : 0 < z + Real.sqrt (scoreVariance z) * radial) :
    HasDerivAt (sourceRadialPotential z) (sourceRadialForce z radial) radial := by
  let S : Set ℝ := {r | 0 < z + Real.sqrt (scoreVariance z) * r}
  have hS : IsOpen S := isOpen_lt continuous_const (by fun_prop)
  have hcont : ContinuousOn (sourceRadialForce z) S := by
    intro r h
    exact (sourceRadialForce_hasDerivAt h).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (sourceRadialForce z) volume 0 radial := by
    apply ContinuousOn.intervalIntegrable
    intro r h
    apply (sourceRadialForce_hasDerivAt ?_).continuousAt.continuousWithinAt
    rcases le_total (0 : ℝ) radial with hpos | hneg
    · rw [Set.uIcc_of_le hpos] at h
      have hsqrt := Real.sqrt_nonneg (scoreVariance z)
      nlinarith [h.1]
    · rw [Set.uIcc_of_ge hneg] at h
      have hsqrt := Real.sqrt_nonneg (scoreVariance z)
      nlinarith [h.1]
  exact intervalIntegral.integral_hasDerivAt_right hint
    (hcont.stronglyMeasurableAtFilter hS radial hr)
    (sourceRadialForce_hasDerivAt hr).continuousAt

/-- The source-normalized radial mass is the actual second derivative of
the integrated complete potential at its generated equilibrium. -/
theorem sourceRadialPotential_secondDeriv_zero {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun r : ℝ => deriv (sourceRadialPotential z) r)
      (normalizedRadialMassSq z) 0 := by
  apply (sourceRadialForce_hasDerivAt_zero hz).congr_of_eventuallyEq
  have hS : IsOpen {r : ℝ | 0 < z + Real.sqrt (scoreVariance z) * r} :=
    isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℝ) ∈ {r : ℝ | 0 < z + Real.sqrt (scoreVariance z) * r} := by
    simpa using hz
  filter_upwards [hS.mem_nhds hzero] with r hr
  exact (sourceRadialPotential_hasDerivAt hz hr).deriv

/-- Arbitrary radial rays retain the derived curvature and its exact square
normalization. -/
theorem sourceRadialPotential_ray_secondDeriv_zero {z : ℝ} (hz : 0 < z)
    (radial : ℝ) :
    HasDerivAt (fun t : ℝ => deriv
      (fun u : ℝ => sourceRadialPotential z (u * radial)) t)
      (normalizedRadialMassSq z * radial ^ 2) 0 := by
  have hinner := (hasDerivAt_id (0 : ℝ)).mul_const radial
  have hf : HasDerivAt (fun t : ℝ => sourceRadialForce z (t * radial) * radial)
      (normalizedRadialMassSq z * radial ^ 2) 0 := by
    have hc : HasDerivAt (sourceRadialForce z) (normalizedRadialMassSq z)
        ((0 : ℝ) * radial) := by
      simpa using sourceRadialForce_hasDerivAt_zero hz
    convert! ((hc.comp 0 hinner).mul_const radial) using 1
    ring
  apply hf.congr_of_eventuallyEq
  have hS : IsOpen {t : ℝ |
      0 < z + Real.sqrt (scoreVariance z) * (t * radial)} :=
    isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℝ) ∈ {t : ℝ |
      0 < z + Real.sqrt (scoreVariance z) * (t * radial)} := by simpa using hz
  filter_upwards [hS.mem_nhds hzero] with t ht
  simpa only [Function.comp_def, id_eq, one_mul] using
    ((sourceRadialPotential_hasDerivAt hz ht).comp t
    ((hasDerivAt_id t).mul_const radial)).deriv

end GeneratedFoundations.Physical.SourceGeneratedRadialVariation
