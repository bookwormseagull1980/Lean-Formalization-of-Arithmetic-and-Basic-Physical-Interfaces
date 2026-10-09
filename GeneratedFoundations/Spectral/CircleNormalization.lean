module

public import GeneratedFoundations.Spectral.ReflectionEven

/-!
# Probability Haar normalization of the reflecting circle

The half-volume measure on the double has mass equal to the interval length.
Multiplication by the square root of this length identifies its actual `L²`
space with probability Haar `L²`. The measure calculation also determines the
normalization of the reflected interval functions.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ComplexConjugate

namespace GeneratedFoundations.Spectral

variable (L : ℝ) [hL : Fact (0 < L)]

abbrev HaarCircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := 2 * L))

theorem circle_ae_half_iff_haar {p : AddCircle (2 * L) → Prop} :
    (∀ᵐ z ∂reflectionCircleMeasure L, p z) ↔
      ∀ᵐ z ∂AddCircle.haarAddCircle, p z := by
  rw [reflectionCircleMeasure_eq_haar]
  exact Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hL.out))

theorem circle_integral_half_eq_haar (f : AddCircle (2 * L) → ℂ) :
    (∫ z, f z ∂reflectionCircleMeasure L) =
      (L : ℂ) * ∫ z, f z ∂AddCircle.haarAddCircle := by
  rw [reflectionCircleMeasure_eq_haar, integral_smul_measure,
    ENNReal.toReal_ofReal hL.out.le]
  exact RCLike.real_smul_eq_coe_mul L _

theorem circle_memLp_haar (f : ReflectionCircleL2 L) :
    MemLp f 2 AddCircle.haarAddCircle :=
  (circle_memLp_volume L f).haarAddCircle

theorem haarCircle_memLp_half (f : HaarCircleL2 L) :
    MemLp f 2 (reflectionCircleMeasure L) := by
  rw [reflectionCircleMeasure_eq_haar]
  exact (Lp.memLp f).smul_measure ENNReal.ofReal_ne_top

def circleHalfToHaar (f : ReflectionCircleL2 L) : HaarCircleL2 L :=
  ((circle_memLp_haar L f).const_mul (Real.sqrt L : ℂ)).toLp _

theorem circleHalfToHaar_coe (f : ReflectionCircleL2 L) :
    circleHalfToHaar L f =ᵐ[AddCircle.haarAddCircle]
      fun z => (Real.sqrt L : ℂ) * f z :=
  MemLp.coeFn_toLp _

def circleHaarToHalf (f : HaarCircleL2 L) : ReflectionCircleL2 L :=
  ((haarCircle_memLp_half L f).const_mul (Real.sqrt L : ℂ)⁻¹).toLp _

theorem circleHaarToHalf_coe (f : HaarCircleL2 L) :
    circleHaarToHalf L f =ᵐ[reflectionCircleMeasure L]
      fun z => (Real.sqrt L : ℂ)⁻¹ * f z :=
  MemLp.coeFn_toLp _

theorem circleHaarToHalf_halfToHaar (f : ReflectionCircleL2 L) :
    circleHaarToHalf L (circleHalfToHaar L f) = f := by
  apply Lp.ext
  have hf := (circle_ae_half_iff_haar L).mpr (circleHalfToHaar_coe L f)
  filter_upwards [circleHaarToHalf_coe L (circleHalfToHaar L f), hf] with z hz hfz
  rw [hz, hfz, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'

theorem circleHalfToHaar_haarToHalf (f : HaarCircleL2 L) :
    circleHalfToHaar L (circleHaarToHalf L f) = f := by
  apply Lp.ext
  have hf := (circle_ae_half_iff_haar L).mp (circleHaarToHalf_coe L f)
  filter_upwards [circleHalfToHaar_coe L (circleHaarToHalf L f), hf] with z hz hfz
  rw [hz, hfz, ← mul_assoc, mul_inv_cancel₀, one_mul]
  exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'

def circleNormalizationLinearEquiv : ReflectionCircleL2 L ≃ₗ[ℂ] HaarCircleL2 L where
  toFun := circleHalfToHaar L
  invFun := circleHaarToHalf L
  left_inv := circleHaarToHalf_halfToHaar L
  right_inv := circleHalfToHaar_haarToHalf L
  map_add' f g := by
    apply Lp.ext
    have hadd := (circle_ae_half_iff_haar L).mp (Lp.coeFn_add f g)
    filter_upwards [circleHalfToHaar_coe L (f + g), circleHalfToHaar_coe L f,
      circleHalfToHaar_coe L g, hadd,
      Lp.coeFn_add (circleHalfToHaar L f) (circleHalfToHaar L g)] with z hsum hf hg hfg hnorm
    change circleHalfToHaar L (f + g) z =
      (circleHalfToHaar L f + circleHalfToHaar L g) z
    simp only [Pi.add_apply] at hnorm hfg
    rw [hsum, hnorm, hf, hg]
    rw [hfg]
    exact mul_add _ _ _
  map_smul' c f := by
    apply Lp.ext
    have hsmul := (circle_ae_half_iff_haar L).mp (Lp.coeFn_smul c f)
    filter_upwards [circleHalfToHaar_coe L (c • f), circleHalfToHaar_coe L f,
      hsmul, Lp.coeFn_smul c (circleHalfToHaar L f)] with z hcf hf hcf' hnorm
    change circleHalfToHaar L (c • f) z = (c • circleHalfToHaar L f) z
    simp only [Pi.smul_apply, smul_eq_mul] at hcf' hnorm
    rw [hcf, hnorm, hf]
    rw [hcf']
    ring

theorem circleHalfToHaar_inner (f g : ReflectionCircleL2 L) :
    inner ℂ (circleHalfToHaar L f) (circleHalfToHaar L g) = inner ℂ f g := by
  rw [L2.inner_def, L2.inner_def]
  have hs : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt hL.out.le
  calc
    (∫ z, inner ℂ (circleHalfToHaar L f z) (circleHalfToHaar L g z)
        ∂AddCircle.haarAddCircle) =
        ∫ z, (L : ℂ) * (conj (f z) * g z) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [circleHalfToHaar_coe L f, circleHalfToHaar_coe L g] with z hf hg
      have hc : conj (Real.sqrt L : ℂ) = (Real.sqrt L : ℂ) := by simp
      rw [hf, hg, RCLike.inner_apply', map_mul, hc]
      calc
        ((Real.sqrt L : ℂ) * conj (f z)) * ((Real.sqrt L : ℂ) * g z) =
            ((Real.sqrt L : ℂ) * (Real.sqrt L : ℂ)) * (conj (f z) * g z) := by ring
        _ = _ := by rw [hs]
    _ = (L : ℂ) * ∫ z, conj (f z) * g z ∂AddCircle.haarAddCircle :=
      integral_const_mul _ _
    _ = ∫ z, inner ℂ (f z) (g z) ∂reflectionCircleMeasure L := by
      rw [circle_integral_half_eq_haar]
      simp only [RCLike.inner_apply']

/-- The multiplier is fixed by the ratio of the two measures. -/
def circleHaarNormalization : ReflectionCircleL2 L ≃ₗᵢ[ℂ] HaarCircleL2 L :=
  (circleNormalizationLinearEquiv L).isometryOfInner (circleHalfToHaar_inner L)

theorem circleHaarNormalization_coe (f : ReflectionCircleL2 L) :
    circleHaarNormalization L f =ᵐ[AddCircle.haarAddCircle]
      fun z => (Real.sqrt L : ℂ) * f z :=
  circleHalfToHaar_coe L f

theorem circleHaarNormalization_symm_coe (f : HaarCircleL2 L) :
    (circleHaarNormalization L).symm f =ᵐ[reflectionCircleMeasure L]
      fun z => (Real.sqrt L : ℂ)⁻¹ * f z :=
  circleHaarToHalf_coe L f

def haarCircleReflection : HaarCircleL2 L →ₗᵢ[ℂ] HaarCircleL2 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z => -z)
    (Measure.measurePreserving_neg AddCircle.haarAddCircle)

theorem haarCircleReflection_coe (f : HaarCircleL2 L) :
    haarCircleReflection L f =ᵐ[AddCircle.haarAddCircle] fun z => f (-z) :=
  Lp.coeFn_compMeasurePreserving f
    (Measure.measurePreserving_neg AddCircle.haarAddCircle)

theorem circleHalfToHaar_reflection_coe (f : ReflectionCircleL2 L) :
    circleHalfToHaar L (circleReflection L f) =ᵐ[AddCircle.haarAddCircle]
      fun z => (Real.sqrt L : ℂ) * f (-z) := by
  have hhalf : circleReflection L f =ᵐ[reflectionCircleMeasure L] fun z => f (-z) :=
    Lp.coeFn_compMeasurePreserving f
      (Measure.measurePreserving_neg (reflectionCircleMeasure L))
  have hhalfHaar : circleReflection L f =ᵐ[AddCircle.haarAddCircle] fun z => f (-z) :=
    (circle_ae_half_iff_haar L).mp hhalf
  apply (circleHalfToHaar_coe L (circleReflection L f)).trans
  exact hhalfHaar.mono fun z hz => congrArg (fun w : ℂ => (Real.sqrt L : ℂ) * w) hz

set_option maxHeartbeats 800000 in
theorem haarCircleReflection_halfToHaar_coe (f : ReflectionCircleL2 L) :
    haarCircleReflection L (circleHalfToHaar L f) =ᵐ[AddCircle.haarAddCircle]
      fun z => (Real.sqrt L : ℂ) * f (-z) := by
  let μH : Measure (AddCircle (2 * L)) := AddCircle.haarAddCircle
  have hnormal : circleHalfToHaar L f =ᵐ[μH] fun z => (Real.sqrt L : ℂ) * f z :=
    circleHalfToHaar_coe L f
  have hneg : (fun z => circleHalfToHaar L f (-z)) =ᵐ[μH]
      fun z => (Real.sqrt L : ℂ) * f (-z) :=
    (Measure.measurePreserving_neg μH).quasiMeasurePreserving.ae
      (p := fun z : AddCircle (2 * L) =>
        circleHalfToHaar L f z = (Real.sqrt L : ℂ) * f z) hnormal
  exact (haarCircleReflection_coe L (circleHalfToHaar L f)).trans hneg

theorem circleHaarNormalization_reflection (f : ReflectionCircleL2 L) :
    circleHaarNormalization L (circleReflection L f) =
      haarCircleReflection L (circleHaarNormalization L f) := by
  apply Lp.ext
  exact (circleHalfToHaar_reflection_coe L f).trans
    (haarCircleReflection_halfToHaar_coe L f).symm

def haarEvenCircleL2 : Submodule ℂ (HaarCircleL2 L) :=
  LinearMap.ker ((haarCircleReflection L).toLinearMap - LinearMap.id)

theorem circleHaarNormalization_mem_even_iff (f : ReflectionCircleL2 L) :
    circleHaarNormalization L f ∈ haarEvenCircleL2 L ↔ f ∈ evenCircleL2 L := by
  change haarCircleReflection L (circleHaarNormalization L f) - circleHaarNormalization L f = 0 ↔
    circleReflection L f - f = 0
  rw [sub_eq_zero, sub_eq_zero, ← circleHaarNormalization_reflection]
  exact (circleHaarNormalization L).injective.eq_iff

def reflectingHaarIsometry : ComplexIntervalL2 0 L →ₗᵢ[ℂ] HaarCircleL2 L :=
  (circleHaarNormalization L).toLinearIsometry.comp (reflectingIsometry L)

theorem reflectingHaarIsometry_coe (f : ComplexIntervalL2 0 L) :
    reflectingHaarIsometry L f =ᵐ[AddCircle.haarAddCircle]
      fun z : AddCircle (2 * L) => (Real.sqrt L : ℂ) * f ‖z‖ := by
  have hr := (circle_ae_half_iff_haar L).mp (reflectingIsometry_coe L f)
  filter_upwards [circleHaarNormalization_coe L (reflectingIsometry L f), hr] with z hn hrz
  change circleHaarNormalization L (reflectingIsometry L f) z = _
  rw [hn, hrz]

theorem reflectingHaarIsometry_range_eq_even :
    LinearMap.range (reflectingHaarIsometry L).toLinearMap = haarEvenCircleL2 L := by
  apply le_antisymm
  · rintro _ ⟨f, rfl⟩
    exact (circleHaarNormalization_mem_even_iff L (reflectingIsometry L f)).mpr
      (reflectingIsometry_mem_even L f)
  · intro f hf
    have heven : (circleHaarNormalization L).symm f ∈ evenCircleL2 L := by
      apply (circleHaarNormalization_mem_even_iff L _).mp
      simpa only [LinearIsometryEquiv.apply_symm_apply] using hf
    rw [← reflectingIsometry_range_eq_even] at heven
    rcases heven with ⟨g, hg⟩
    change reflectingIsometry L g = (circleHaarNormalization L).symm f at hg
    refine ⟨g, ?_⟩
    change circleHaarNormalization L (reflectingIsometry L g) = f
    rw [hg, LinearIsometryEquiv.apply_symm_apply]

/-- Normalized reflection onto the usual even part of probability Haar `L²`. -/
def reflectingHaar_unitary : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] haarEvenCircleL2 L :=
  (reflectingHaarIsometry L).equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ (reflectingHaarIsometry_range_eq_even L))

end GeneratedFoundations.Spectral
