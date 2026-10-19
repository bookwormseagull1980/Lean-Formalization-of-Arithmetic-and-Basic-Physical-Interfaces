module

public import GeneratedFoundations.Geometry.SourceSphereTangent
public import GeneratedFoundations.Geometry.SourceProjectiveCovering
public import GeneratedFoundations.Geometry.SourceQuotientHilbert
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Volume normalization from the original source amplitude

The source trace metric is the Euclidean metric on its quaternion amplitude.
Its unit sphere is the source group, and its central quotient has two sheets.
The angular normalization is obtained from the radial derivative of the
actual four-dimensional Lebesgue ball volume, divided by that sheet count.
Scaling the three angular directions then determines the quotient measure.

Thus the total angular volume is computed from the ambient measure and the
existing covering. It is not an independent geometric
constant. The radial-flux identity below is proved at every positive radius;
the polynomial extension to nonpositive radii is used only in algebraic
formulas, not as the mass of a positive measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Set Topology
open GeneratedFoundations.Geometry.SourceSphereTangent (Ambient)
open GeneratedFoundations.Geometry.SourceSpinCentre (CentralQuotient)
open GeneratedFoundations.Geometry.SourceCentralObservations (quotientContinuous)
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude (Sphere3 sourceSphereHomeomorph)

namespace GeneratedFoundations.Geometry.SourceProjectiveVolume

/-- The volume of an actual ball in the original trace-metric amplitude. -/
def amplitudeBallVolume (r : ℝ) : ℝ :=
  (volume (Metric.ball (0 : Ambient) r)).toReal

theorem amplitudeBallVolume_eq {r : ℝ} (hr : 0 ≤ r) :
    amplitudeBallVolume r = Real.pi ^ 2 * r ^ 4 / 2 := by
  have h := InnerProductSpace.volume_ball_of_dim_even
    (E := Ambient) (k := 2) (by simp [Ambient]) (0 : Ambient) r
  have hv := congrArg ENNReal.toReal h
  norm_num [amplitudeBallVolume, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr, ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ Real.pi ^ 2 / 2)] at hv ⊢
  nlinarith [hv]

/-- Radial flux is obtained by differentiating the measured ambient ball. -/
theorem amplitudeBallVolume_hasDerivAt {r : ℝ} (hr : 0 < r) :
    HasDerivAt amplitudeBallVolume (2 * Real.pi ^ 2 * r ^ 3) r := by
  have hpoly := (((hasDerivAt_id r).pow 4).const_mul (Real.pi ^ 2)).div_const 2
  simp only [id_eq] at hpoly
  have heq : amplitudeBallVolume =ᶠ[nhds r]
      fun s : ℝ => Real.pi ^ 2 * s ^ 4 / 2 := by
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact amplitudeBallVolume_eq hs.le
  convert hpoly.congr_of_eventuallyEq heq using 1
  ring

/-- The number of actual central sheets, not an independently chosen divisor. -/
def sheetCount : ℕ :=
  Nat.card (Subgroup.center Operations.SourceSpinCornerGroup.SU2)

theorem sheetCount_eq : sheetCount = 2 :=
  SourceSpinCentre.centre_card

theorem sheetCount_eq_fibre (p : SourceProjectiveGeometry.RP3) :
    sheetCount = Nat.card (SourceProjectiveGeometry.sourceProjection ⁻¹' {p}) := by
  rw [sheetCount_eq, SourceProjectiveCovering.sourceProjection_fibre_card]

/-- Angular measure obtained from the ambient Lebesgue measure by the actual
polar-coordinate decomposition. -/
def sphereMeasure : Measure Sphere3 := (volume : Measure Ambient).toSphere

theorem sphereMeasure_total :
    (sphereMeasure Set.univ).toReal = 2 * Real.pi ^ 2 := by
  have h := (volume : Measure Ambient).toSphere_real_apply_univ
  change ((volume : Measure Ambient).toSphere Set.univ).toReal = _
  change ((volume : Measure Ambient).toSphere Set.univ).toReal =
    (Module.finrank ℝ Ambient : ℝ) * amplitudeBallVolume 1 at h
  rw [h, amplitudeBallVolume_eq (by norm_num)]
  norm_num [Ambient]
  ring

theorem sphereMeasure_eq_radialFlux :
    (sphereMeasure Set.univ).toReal = deriv amplitudeBallVolume 1 := by
  rw [sphereMeasure_total,
    (amplitudeBallVolume_hasDerivAt (by norm_num : (0 : ℝ) < 1)).deriv]
  norm_num

/-- Three angular directions scale the unit polar measure; the quotient
removes exactly the central covering multiplicity. -/
def roundVolume (r : ℝ) : ℝ :=
  r ^ 3 * (sphereMeasure Set.univ).toReal / (sheetCount : ℝ)

theorem roundVolume_eq (r : ℝ) : roundVolume r = Real.pi ^ 2 * r ^ 3 := by
  rw [roundVolume, sphereMeasure_total, sheetCount_eq]
  norm_num
  ring

/-- The quotient normalization agrees with the radial flux at every positive
radius, with the multiplicity of the actual fibre over any projective point. -/
theorem roundVolume_eq_radialFlux {r : ℝ} (hr : 0 < r)
    (p : SourceProjectiveGeometry.RP3) :
    roundVolume r = deriv amplitudeBallVolume r /
      (Nat.card (SourceProjectiveGeometry.sourceProjection ⁻¹' {p}) : ℝ) := by
  rw [roundVolume_eq, (amplitudeBallVolume_hasDerivAt hr).deriv,
    SourceProjectiveCovering.sourceProjection_fibre_card]
  norm_num
  ring

theorem roundVolume_pos {r : ℝ} (hr : 0 < r) : 0 < roundVolume r := by
  rw [roundVolume_eq]
  positivity

/-- The same central observation applied to the actual unit-sphere amplitude. -/
def angularObservation : C(Sphere3, CentralQuotient) :=
  quotientContinuous.comp ⟨sourceSphereHomeomorph.symm, sourceSphereHomeomorph.symm.continuous⟩

/-- Push the ambient angular measure through the source's actual central
quotient, dividing by its covering multiplicity and scaling its three angles. -/
def roundMeasure (r : ℝ) : Measure CentralQuotient :=
  ENNReal.ofReal (r ^ 3 / (sheetCount : ℝ)) •
    Measure.map angularObservation sphereMeasure

theorem roundMeasure_univ {r : ℝ} (hr : 0 < r) :
    (roundMeasure r Set.univ).toReal = roundVolume r := by
  rw [roundMeasure, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    Measure.map_apply angularObservation.continuous.measurable MeasurableSet.univ]
  simp only [Set.preimage_univ]
  rw [sheetCount_eq]
  norm_num only [Nat.cast_ofNat]
  rw [ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ r ^ 3 / 2)]
  rw [roundVolume_eq, sphereMeasure_total]
  ring

theorem roundMeasure_total {r : ℝ} (hr : 0 < r) :
    (roundMeasure r Set.univ).toReal = Real.pi ^ 2 * r ^ 3 := by
  rw [roundMeasure_univ hr, roundVolume_eq]

end GeneratedFoundations.Geometry.SourceProjectiveVolume
