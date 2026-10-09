module

public import GeneratedFoundations.Spectral.ComplexIntervalSobolev
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Reflection of interval functions onto the even part of a circle

The quotient circle has period twice the interval length. Its group norm folds
it onto the interval. The folded measure is computed before constructing the
`L²` isometry, so the normalization is determined by the measures.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval ComplexConjugate

namespace GeneratedFoundations.Spectral

lemma map_abs_intervalMeasure {L : ℝ} (hL : 0 < L) :
    (intervalMeasure (-L) L).map abs = (2 : ℝ≥0∞) • intervalMeasure 0 L := by
  have hsplit : volume.restrict (Ioc (-L) L) =
      volume.restrict (Ioc (-L) 0) + volume.restrict (Ioc 0 L) := by
    rw [← Ioc_union_Ioc_eq_Ioc (neg_nonpos.mpr hL.le) hL.le,
      Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc]
  have hneg : (volume.restrict (Icc (-L) 0)).map (fun x : ℝ => -x) =
      intervalMeasure 0 L := by
    have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
      (s := Icc 0 L) measurableSet_Icc
    have hset : (fun x : ℝ => -x) ⁻¹' Icc 0 L = Icc (-L) 0 := by
      ext x
      simp only [mem_preimage, mem_Icc]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simpa only [hset, intervalMeasure] using h.map_eq
  have hleft : (volume.restrict (Icc (-L) 0)).map abs = intervalMeasure 0 L := by
    calc
      _ = (volume.restrict (Icc (-L) 0)).map (fun x : ℝ => -x) := by
        apply Measure.map_congr
        exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => abs_of_nonpos hx.2
      _ = _ := hneg
  have hright : (volume.restrict (Icc 0 L)).map abs = intervalMeasure 0 L := by
    calc
      _ = (volume.restrict (Icc 0 L)).map id := by
        apply Measure.map_congr
        exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => abs_of_nonneg hx.1
      _ = _ := Measure.map_id
  unfold intervalMeasure
  rw [← restrict_Ioc_eq_restrict_Icc, hsplit,
    Measure.map_add _ _ continuous_abs.measurable,
    restrict_Ioc_eq_restrict_Icc, restrict_Ioc_eq_restrict_Icc, hleft, hright]
  simp only [two_smul]
  rfl

section PositiveLength

variable (L : ℝ) [hL : Fact (0 < L)]

instance doubleLength_pos : Fact (0 < 2 * L) := ⟨mul_pos zero_lt_two hL.out⟩

/-- Half of the ordinary quotient volume has the same mass as the interval. -/
noncomputable def reflectionCircleMeasure : Measure (AddCircle (2 * L)) :=
  (2 : ℝ≥0∞)⁻¹ • volume

noncomputable abbrev ReflectionCircleL2 := Lp ℂ 2 (reflectionCircleMeasure L)

instance reflectionCircleMeasure_negInvariant :
    Measure.IsNegInvariant (reflectionCircleMeasure L) where
  neg_eq_self := by
    change (reflectionCircleMeasure L).map (fun z => -z) = reflectionCircleMeasure L
    rw [reflectionCircleMeasure, Measure.map_smul _ measurable_neg.aemeasurable,
      Measure.map_neg_eq_self]

theorem reflectionCircleMeasure_eq_haar :
    reflectionCircleMeasure L = ENNReal.ofReal L • AddCircle.haarAddCircle := by
  rw [reflectionCircleMeasure, AddCircle.volume_eq_smul_haarAddCircle, smul_smul,
    ENNReal.ofReal_mul zero_le_two]
  congr 1
  rw [ENNReal.ofReal_ofNat, ← mul_assoc,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

theorem circle_quotient_measurePreserving :
    MeasurePreserving (fun x : ℝ => (x : AddCircle (2 * L)))
      (intervalMeasure (-L) L) volume := by
  have h := AddCircle.measurePreserving_mk (2 * L) (-L)
  convert! h using 1
  rw [show -L + 2 * L = L by ring, restrict_Ioc_eq_restrict_Icc]
  rfl

theorem circle_norm_coe (x : ℝ) (hx : x ∈ Icc (-L) L) :
    ‖(x : AddCircle (2 * L))‖ = |x| := by
  apply (AddCircle.norm_coe_eq_abs_iff (2 * L) (ne_of_gt (Fact.out : 0 < 2 * L))).mpr
  rw [abs_of_pos (Fact.out : 0 < 2 * L)]
  have h := abs_le.mpr hx
  linarith

theorem circle_fold_measurePreserving_volume :
    MeasurePreserving (fun z : AddCircle (2 * L) => ‖z‖) volume
      ((2 : ℝ≥0∞) • intervalMeasure 0 L) := by
  refine ⟨continuous_norm.measurable, ?_⟩
  rw [← (circle_quotient_measurePreserving L).map_eq,
    Measure.map_map continuous_norm.measurable AddCircle.measurable_mk']
  calc
    _ = (intervalMeasure (-L) L).map abs := by
      apply Measure.map_congr
      exact ae_restrict_of_forall_mem measurableSet_Icc fun x hx => circle_norm_coe L x hx
    _ = _ := map_abs_intervalMeasure hL.out

theorem circle_fold_measurePreserving :
    MeasurePreserving (fun z : AddCircle (2 * L) => ‖z‖)
      (reflectionCircleMeasure L) (intervalMeasure 0 L) := by
  refine ⟨continuous_norm.measurable, ?_⟩
  rw [reflectionCircleMeasure, Measure.map_smul _ continuous_norm.measurable.aemeasurable,
    (circle_fold_measurePreserving_volume L).map_eq, smul_smul,
    ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_smul]

/-- Pullback by the folding map, on actual `L²` equivalence classes. -/
noncomputable def reflectingIsometry :
    ComplexIntervalL2 0 L →ₗᵢ[ℂ] ReflectionCircleL2 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z => ‖z‖) (circle_fold_measurePreserving L)

theorem reflectingIsometry_coe (f : ComplexIntervalL2 0 L) :
    reflectingIsometry L f =ᵐ[reflectionCircleMeasure L]
      fun z : AddCircle (2 * L) => f ‖z‖ :=
  Lp.coeFn_compMeasurePreserving f (circle_fold_measurePreserving L)

noncomputable def circleReflection : ReflectionCircleL2 L →ₗᵢ[ℂ] ReflectionCircleL2 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z => -z)
    (Measure.measurePreserving_neg (reflectionCircleMeasure L))

noncomputable def evenCircleL2 : Submodule ℂ (ReflectionCircleL2 L) :=
  LinearMap.ker ((circleReflection L).toLinearMap - LinearMap.id)

theorem mem_evenCircleL2 (f : ReflectionCircleL2 L) :
    f ∈ evenCircleL2 L ↔ ∀ᵐ z ∂reflectionCircleMeasure L, f (-z) = f z := by
  change circleReflection L f - f = 0 ↔ _
  rw [sub_eq_zero]
  constructor
  · intro h
    have hcoe := Lp.coeFn_compMeasurePreserving f
      (Measure.measurePreserving_neg (reflectionCircleMeasure L))
    change circleReflection L f =ᵐ[reflectionCircleMeasure L] (fun z => f (-z)) at hcoe
    rw [h] at hcoe
    exact hcoe.symm
  · intro h
    apply Lp.ext
    exact (Lp.coeFn_compMeasurePreserving f
      (Measure.measurePreserving_neg (reflectionCircleMeasure L))).trans h

theorem reflectingIsometry_mem_even (f : ComplexIntervalL2 0 L) :
    reflectingIsometry L f ∈ evenCircleL2 L := by
  apply (mem_evenCircleL2 L _).mpr
  have hneg := (Measure.measurePreserving_neg (reflectionCircleMeasure L)).quasiMeasurePreserving.ae
    (reflectingIsometry_coe L f)
  filter_upwards [hneg, reflectingIsometry_coe L f] with z hzneg hz
  rw [hzneg, hz, norm_neg]

theorem circle_fold_orbit (z : AddCircle (2 * L)) :
    (‖z‖ : AddCircle (2 * L)) = z ∨ (‖z‖ : AddCircle (2 * L)) = -z := by
  let r : ℝ := AddCircle.equivIoc (2 * L) (-L) z
  have hr : r ∈ Icc (-L) L := by
    have h := (AddCircle.equivIoc (2 * L) (-L) z).property
    dsimp only [r]
    constructor <;> linarith [h.1, h.2]
  have hcoe : (r : AddCircle (2 * L)) = z := AddCircle.coe_equivIoc
  have hnorm : ‖z‖ = |r| := by rw [← hcoe]; exact circle_norm_coe L r hr
  by_cases hnonneg : 0 ≤ r
  · left
    rw [hnorm, abs_of_nonneg hnonneg]
    exact hcoe
  · right
    rw [hnorm, abs_of_neg (lt_of_not_ge hnonneg)]
    simpa using congrArg Neg.neg hcoe

lemma circle_memLp_volume (f : ReflectionCircleL2 L) :
    MemLp f 2 (volume : Measure (AddCircle (2 * L))) := by
  have h := (Lp.memLp f).smul_measure (c := (2 : ℝ≥0∞)) (by norm_num)
  simpa only [reflectionCircleMeasure, smul_smul,
    ENNReal.mul_inv_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞), one_smul] using h

lemma circle_restriction_memLp (f : ReflectionCircleL2 L) :
    MemLp (fun x : ℝ => f (x : AddCircle (2 * L))) 2 (intervalMeasure 0 L) := by
  have h := (circle_memLp_volume L f).comp_measurePreserving (circle_quotient_measurePreserving L)
  apply h.mono_measure
  apply Measure.restrict_mono _ le_rfl
  intro x hx
  exact ⟨(neg_nonpos.mpr hL.out.le).trans hx.1, hx.2⟩

theorem reflectingIsometry_range_eq_even :
    LinearMap.range (reflectingIsometry L).toLinearMap = evenCircleL2 L := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact reflectingIsometry_mem_even L f
  · intro f hf
    let g : ComplexIntervalL2 0 L := (circle_restriction_memLp L f).toLp _
    refine ⟨g, ?_⟩
    apply Lp.ext
    have hg := (circle_fold_measurePreserving L).quasiMeasurePreserving.ae
      (circle_restriction_memLp L f).coeFn_toLp
    have heven := (mem_evenCircleL2 L f).mp hf
    filter_upwards [reflectingIsometry_coe L g, hg, heven] with z hreflect hg heven
    change (reflectingIsometry L g) z = f z
    change g ‖z‖ = f (‖z‖ : AddCircle (2 * L)) at hg
    rw [hreflect, hg]
    rcases circle_fold_orbit L z with hz | hz
    · rw [hz]
    · rw [hz, heven]

/-- Reflection identifies the interval with the usual even subspace of the circle. -/
noncomputable def reflectingDouble_unitary :
    ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] evenCircleL2 L :=
  (reflectingIsometry L).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (reflectingIsometry_range_eq_even L))

end PositiveLength

end GeneratedFoundations.Spectral
