module

public import GeneratedFoundations.Spectral.GaussianHeatConvolution
public import GeneratedFoundations.Spectral.NeumannHeatSemigroup

/-!
# The reflected Gaussian kernel of the original Neumann heat semigroup

The convolution integral on the double is transported through the actual
reflection isometry. Completeness of the cosine basis identifies it with the
semigroup of the original Sobolev Neumann operator. Positivity is inherited
from the positive Gaussian image sum, independently of operator positivity.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal NNReal ComplexConjugate

namespace GeneratedFoundations.Spectral.GaussianHeatKernel

variable (L : ℝ) [hL : Fact (0 < L)]

def variance (b : ℝ) : ℝ≥0 := ⟨b ^ 2, sq_nonneg b⟩

theorem circleMultiplier_eq_decay (b : ℝ) (n : ℕ) :
    Real.exp (-2 * Real.pi ^ 2 * (b / (2 * L)) ^ 2 * (n : ℝ) ^ 2) =
      NeumannHeatSemigroup.decay L (b ^ 2) n := by
  unfold NeumannHeatSemigroup.decay neumannEigenvalue
  congr 1
  field_simp [hL.out.ne']

theorem convolution_inner_cosine {b : ℝ} (hb : 0 < b) (f : HaarCircleL2 L) (n : ℕ) :
    inner ℂ (haarCosineMode L n) (GaussianHeatConvolution.convolution (2 * L) b f) =
      (NeumannHeatSemigroup.decay L (b ^ 2) n : ℂ) * inner ℂ (haarCosineMode L n) f := by
  cases n with
  | zero =>
    simp only [haarCosineMode, ← GaussianHeatConvolution.fourierCoeff_eq_inner,
      GaussianHeatConvolution.convolution_fourierCoeff_gaussian (2 * L) hb,
      Int.cast_zero, Complex.ofReal_one,
      NeumannHeatSemigroup.decay_mode_zero, one_mul]
    norm_num
  | succ n =>
    simp only [haarCosineMode, inner_smul_left, inner_add_left,
      ← GaussianHeatConvolution.fourierCoeff_eq_inner,
      GaussianHeatConvolution.convolution_fourierCoeff_gaussian (2 * L) hb,
      Int.cast_neg, Int.cast_natCast, neg_sq]
    rw [circleMultiplier_eq_decay L b (n + 1)]
    ring

theorem even_coe (f : HaarCircleL2 L) (hf : f ∈ haarEvenCircleL2 L) :
    ∀ᵐ z ∂AddCircle.haarAddCircle, f (-z) = f z := by
  have he : haarCircleReflection L f = f := by
    change haarCircleReflection L f - f = 0 at hf
    exact sub_eq_zero.mp hf
  have ha := haarCircleReflection_coe L f
  rw [he] at ha
  exact ha.symm

theorem convolution_mem_even {b : ℝ} (hb : 0 < b) (f : HaarCircleL2 L)
    (hf : f ∈ haarEvenCircleL2 L) :
    GaussianHeatConvolution.convolution (2 * L) b f ∈ haarEvenCircleL2 L := by
  change haarCircleReflection L _ - _ = 0
  apply sub_eq_zero.mpr
  apply Lp.ext
  have he := even_coe L f hf
  have hn := (Measure.measurePreserving_neg
    (AddCircle.haarAddCircle (T := 2 * L))).quasiMeasurePreserving.ae
      (p := fun z => GaussianHeatConvolution.convolution (2 * L) b f z =
        GaussianHeatConvolution.convolutionValue (2 * L) b f z)
      (GaussianHeatConvolution.convolution_coe (2 * L) b f)
  filter_upwards [haarCircleReflection_coe L
    (GaussianHeatConvolution.convolution (2 * L) b f), hn,
    GaussianHeatConvolution.convolution_coe (2 * L) b f] with z hr hnz hz
  change haarCircleReflection L (GaussianHeatConvolution.convolution (2 * L) b f) z =
    GaussianHeatConvolution.convolution (2 * L) b f z
  rw [hr, hnz, hz, GaussianHeatConvolution.convolutionValue_even (2 * L) hb f he]

/-- Equality in the original Hilbert space, via the actual reflection isometry. -/
theorem convolution_reflecting_eq_heat {b : ℝ} (hb : 0 < b) (f : ComplexIntervalL2 0 L) :
    GaussianHeatConvolution.convolution (2 * L) b (reflectingHaarIsometry L f) =
      reflectingHaarIsometry L (NeumannHeatSemigroup.heat L (variance b) f) := by
  have he (g : ComplexIntervalL2 0 L) : reflectingHaarIsometry L g ∈ haarEvenCircleL2 L := by
    rw [← reflectingHaarIsometry_range_eq_even]
    exact ⟨g, rfl⟩
  apply sub_eq_zero.mp
  apply haarEven_eq_zero_of_cosine_inner L _
    ((haarEvenCircleL2 L).sub_mem (convolution_mem_even L hb _ (he f)) (he _))
  intro n
  rw [inner_sub_right, convolution_inner_cosine L hb]
  rw [← reflectingHaar_neumannCosineMode, (reflectingHaarIsometry L).inner_map_map,
    (reflectingHaarIsometry L).inner_map_map, NeumannHeatSemigroup.heat_coefficient]
  exact sub_self _

/-- The real reflected kernel relative to interval Lebesgue measure. -/
def kernel (b x y : ℝ) : ℝ :=
  ((GaussianHeatConvolution.kernel (2 * L) b ((x - y : ℝ) : AddCircle (2 * L))).re +
    (GaussianHeatConvolution.kernel (2 * L) b ((x + y : ℝ) : AddCircle (2 * L))).re) /
      (2 * L)

theorem kernel_pos {b : ℝ} (hb : 0 < b) (x y : ℝ) : 0 < kernel L b x y :=
  div_pos (add_pos (GaussianHeatConvolution.kernel_pos (2 * L) hb _)
    (GaussianHeatConvolution.kernel_pos (2 * L) hb _)) (mul_pos (by norm_num) hL.out)

theorem ofReal_kernel {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    (kernel L b x y : ℂ) = (2 * (L : ℂ))⁻¹ *
      (GaussianHeatConvolution.kernel (2 * L) b ((x - y : ℝ) : AddCircle (2 * L)) +
        GaussianHeatConvolution.kernel (2 * L) b ((x + y : ℝ) : AddCircle (2 * L))) := by
  have hre (z : AddCircle (2 * L)) :
      (((GaussianHeatConvolution.kernel (2 * L) b z).re : ℝ) : ℂ) =
        GaussianHeatConvolution.kernel (2 * L) b z := by
    apply Complex.ext
    · rfl
    · exact (GaussianHeatConvolution.kernel_im_eq_zero (2 * L) hb z).symm
  unfold kernel
  push_cast
  rw [hre, hre]
  ring

theorem kernel_symmetric {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    kernel L b x y = kernel L b y x := by
  unfold kernel
  have hneg : ((y - x : ℝ) : AddCircle (2 * L)) = -((x - y : ℝ) : AddCircle (2 * L)) := by
    rw [← AddCircle.coe_neg]
    congr 1
    ring
  rw [hneg, GaussianHeatConvolution.kernel_even (2 * L) hb, add_comm y x]

theorem images_summable {b : ℝ} (hb : 0 < b) (x : ℝ) :
    Summable (fun n : ℤ =>
      GeneratedFoundations.Correlation.GaussianCorrelation.changeKernel b (x + (2 * L) * n)) := by
  have h := PeriodicGaussian.density_pointwise_summable
    (div_pos hb (mul_pos (by norm_num : (0 : ℝ) < 2) hL.out)) (x / (2 * L))
  simp_rw [GaussianHeatConvolution.density_rescale (2 * L) hb] at h
  have hc : ((2 * L : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) hL.out).ne'
  exact Complex.summable_ofReal.mp ((summable_mul_left_iff hc).mp h)

/-- The reflected kernel is the convergent two-image sum of the original source density. -/
theorem kernel_image_sum {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    kernel L b x y = ∑' n : ℤ,
      (GeneratedFoundations.Correlation.GaussianCorrelation.changeKernel b
        (x - y + (2 * L) * n) +
       GeneratedFoundations.Correlation.GaussianCorrelation.changeKernel b
        (x + y + (2 * L) * n)) := by
  apply Complex.ofReal_injective
  rw [ofReal_kernel L hb, GaussianHeatConvolution.kernel_image_sum (2 * L) hb,
    GaussianHeatConvolution.kernel_image_sum (2 * L) hb,
    (images_summable L hb (x - y)).tsum_add (images_summable L hb (x + y)),
    Complex.ofReal_add, Complex.ofReal_tsum, Complex.ofReal_tsum]
  simp only [PeriodicGaussian.density_apply]
  push_cast
  have hc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
  field_simp

theorem kernel_continuous_right (b x : ℝ) : Continuous (kernel L b x) := by
  have hq : Continuous (fun y : ℝ => (y : AddCircle (2 * L))) := continuous_quotient_mk'
  have hk := map_continuous (GaussianHeatConvolution.kernel (2 * L) b)
  exact ((Complex.continuous_re.comp (hk.comp (hq.comp (continuous_const.sub continuous_id)))).add
    (Complex.continuous_re.comp (hk.comp (hq.comp (continuous_const.add continuous_id))))).div_const _

theorem fold_integral {g : ℝ → ℂ} (hg : AEStronglyMeasurable g (intervalMeasure 0 L)) :
    (∫ z : AddCircle (2 * L), g ‖z‖ ∂AddCircle.haarAddCircle) =
      (L : ℂ)⁻¹ * ∫ y : ℝ, g y ∂intervalMeasure 0 L := by
  have hm : AEStronglyMeasurable g
      ((reflectionCircleMeasure L).map (fun z : AddCircle (2 * L) => ‖z‖)) := by
    rwa [(circle_fold_measurePreserving L).map_eq]
  have hi := integral_map (circle_fold_measurePreserving L).measurable.aemeasurable hm
  rw [(circle_fold_measurePreserving L).map_eq, circle_integral_half_eq_haar] at hi
  have hc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
  rw [hi, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

theorem kernel_fold_pair {b : ℝ} (hb : 0 < b) (x : ℝ) (z : AddCircle (2 * L)) :
    (2 * (L : ℂ)) * (kernel L b x ‖z‖ : ℂ) =
      GaussianHeatConvolution.kernel (2 * L) b ((x : AddCircle (2 * L)) - z) +
        GaussianHeatConvolution.kernel (2 * L) b ((x : AddCircle (2 * L)) + z) := by
  rw [ofReal_kernel L hb, ← mul_assoc, mul_inv_cancel₀, one_mul,
    AddCircle.coe_sub, AddCircle.coe_add]
  · rcases circle_fold_orbit L z with h | h
    · rw [h]
    · rw [h, sub_neg_eq_add, ← sub_eq_add_neg, add_comm]
  · exact_mod_cast (mul_pos (by norm_num : (0 : ℝ) < 2) hL.out).ne'

def integralValue (b : ℝ) (f : ComplexIntervalL2 0 L) (x : ℝ) : ℂ :=
  ∫ y : ℝ, f y * (kernel L b x y : ℂ) ∂intervalMeasure 0 L

/-- Folding the actual convolution integral gives the reflected interval integral. -/
theorem convolution_reflecting_value {b : ℝ} (hb : 0 < b)
    (f : ComplexIntervalL2 0 L) (x : ℝ) :
    GaussianHeatConvolution.convolutionValue (2 * L) b (reflectingHaarIsometry L f)
      (x : AddCircle (2 * L)) = (Real.sqrt L : ℂ) * integralValue L b f x := by
  let F := reflectingHaarIsometry L f
  let K := GaussianHeatConvolution.kernel (2 * L) b
  let xc : AddCircle (2 * L) := x
  have hFe : F ∈ haarEvenCircleL2 L := by
    rw [← reflectingHaarIsometry_range_eq_even]
    exact ⟨f, rfl⟩
  have hneg := even_coe L F hFe
  have hfirst : Integrable (fun z => F z * K (xc - z)) AddCircle.haarAddCircle :=
    GaussianHeatConvolution.convolution_integrable (2 * L) b F xc
  have hsecond : Integrable (fun z => F z * K (xc + z)) AddCircle.haarAddCircle :=
    (GaussianHeatConvolution.integrable_circleL2 (2 * L) F).mul_bdd
      ((map_continuous K).comp (continuous_const.add continuous_id)).aestronglyMeasurable
      (ae_of_all _ fun z => K.norm_coe_le_norm (xc + z))
  have hsecond_eq : (∫ z, F z * K (xc + z) ∂AddCircle.haarAddCircle) =
      GaussianHeatConvolution.convolutionValue (2 * L) b F xc := by
    rw [← integral_neg_eq_self (fun z => F z * K (xc + z))]
    apply integral_congr_ae
    filter_upwards [hneg] with z hz
    rw [hz, ← sub_eq_add_neg]
  have hgm : AEStronglyMeasurable
      (fun y : ℝ => f y * (kernel L b x y : ℂ)) (intervalMeasure 0 L) :=
    (Lp.aestronglyMeasurable f).mul
      (Complex.continuous_ofReal.comp (kernel_continuous_right L b x)).aestronglyMeasurable
  have htwo : 2 * GaussianHeatConvolution.convolutionValue (2 * L) b F xc =
      2 * ((Real.sqrt L : ℂ) * integralValue L b f x) := by
    calc
      _ = ∫ z, F z * (K (xc - z) + K (xc + z)) ∂AddCircle.haarAddCircle := by
        simp_rw [mul_add]
        rw [integral_add hfirst hsecond, hsecond_eq, two_mul]
        rfl
      _ = ((Real.sqrt L : ℂ) * (2 * (L : ℂ))) *
          ∫ z : AddCircle (2 * L), f ‖z‖ * (kernel L b x ‖z‖ : ℂ)
            ∂AddCircle.haarAddCircle := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards [reflectingHaarIsometry_coe L f] with z hz
        change F z = (Real.sqrt L : ℂ) * f ‖z‖ at hz
        rw [hz]
        rw [← kernel_fold_pair L hb x z]
        ring
      _ = _ := by
        rw [fold_integral L hgm]
        unfold integralValue
        have hc : (L : ℂ) ≠ 0 := by exact_mod_cast hL.out.ne'
        field_simp
  exact mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) htwo

/-- The image kernel represents the existing Neumann heat operator on every original `L²` input. -/
theorem heat_coe_integral {b : ℝ} (hb : 0 < b) (f : ComplexIntervalL2 0 L) :
    NeumannHeatSemigroup.heat L (variance b) f =ᵐ[intervalMeasure 0 L]
      integralValue L b f := by
  have hc := GaussianHeatConvolution.convolution_coe (2 * L) b (reflectingHaarIsometry L f)
  rw [convolution_reflecting_eq_heat L hb f] at hc
  have hci := haarCircle_ae_interval L hc
  have hr := haarCircle_ae_interval L
    (reflectingHaarIsometry_coe L (NeumannHeatSemigroup.heat L (variance b) f))
  have hs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'
  filter_upwards [hci, hr, ae_restrict_mem measurableSet_Icc] with x hx hrx hmem
  have hn : ‖(x : AddCircle (2 * L))‖ = x := by
    rw [circle_norm_coe L x ⟨(neg_nonpos.mpr hL.out.le).trans hmem.1, hmem.2⟩,
      abs_of_nonneg hmem.1]
  rw [hrx, hn, convolution_reflecting_value L hb] at hx
  exact mul_left_cancel₀ hs hx

theorem kernel_norm_bound {b : ℝ} (hb : 0 < b) (x y : ℝ) :
    ‖(kernel L b x y : ℂ)‖ ≤ ‖(2 * (L : ℂ))⁻¹‖ *
      (‖GaussianHeatConvolution.kernel (2 * L) b‖ +
        ‖GaussianHeatConvolution.kernel (2 * L) b‖) := by
  rw [ofReal_kernel L hb, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_add_le _ _).trans
    (add_le_add ((GaussianHeatConvolution.kernel (2 * L) b).norm_coe_le_norm _)
      ((GaussianHeatConvolution.kernel (2 * L) b).norm_coe_le_norm _))

theorem kernel_product_integrable {b : ℝ} (hb : 0 < b)
    (f : ComplexIntervalL2 0 L) (x : ℝ) :
    Integrable (fun y : ℝ => f y * (kernel L b x y : ℂ)) (intervalMeasure 0 L) :=
  ((Lp.memLp f).integrable (by norm_num)).mul_bdd
    (Complex.continuous_ofReal.comp (kernel_continuous_right L b x)).aestronglyMeasurable
    (ae_of_all _ (kernel_norm_bound L hb x))

/-- Every row of the reflected kernel has total mass one. -/
theorem kernel_integral {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (∫ y : ℝ, kernel L b x y ∂intervalMeasure 0 L) = 1 := by
  have h := convolution_reflecting_value L hb (neumannCosineMode L 0) x
  rw [reflectingHaar_neumannCosineMode] at h
  have hc : haarCosineMode L 0 =ᵐ[AddCircle.haarAddCircle] fun _ => (1 : ℂ) := by
    exact haarCosineMode_coe L 0
  rw [GaussianHeatConvolution.convolutionValue_const (2 * L) hb _ 1 hc] at h
  have hi : integralValue L b (neumannCosineMode L 0) x =
      (Real.sqrt L : ℂ)⁻¹ * ∫ y : ℝ, (kernel L b x y : ℂ) ∂intervalMeasure 0 L := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [neumannCosineMode_zero_coe L] with y hy
    rw [hy]
  have hs : (Real.sqrt L : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'
  rw [hi, ← mul_assoc, mul_inv_cancel₀ hs, one_mul, integral_complex_ofReal] at h
  exact_mod_cast h.symm

theorem integralValue_nonneg {b : ℝ} (hb : 0 < b) (f : ComplexIntervalL2 0 L)
    (hf : ∀ᵐ y ∂intervalMeasure 0 L, 0 ≤ (f y).re ∧ (f y).im = 0) (x : ℝ) :
    0 ≤ (integralValue L b f x).re ∧ (integralValue L b f x).im = 0 := by
  have heq : integralValue L b f x =
      ((∫ y : ℝ, (f y).re * kernel L b x y ∂intervalMeasure 0 L : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hy.2]
  rw [heq, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨integral_nonneg_of_ae ?_, rfl⟩
  filter_upwards [hf] with y hy
  exact mul_nonneg hy.1 (kernel_pos L hb x y).le

theorem integralValue_const {b : ℝ} (hb : 0 < b) (f : ComplexIntervalL2 0 L)
    (c : ℂ) (hf : f =ᵐ[intervalMeasure 0 L] fun _ => c) (x : ℝ) :
    integralValue L b f x = c := by
  calc
    _ = ∫ y : ℝ, c * (kernel L b x y : ℂ) ∂intervalMeasure 0 L := by
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    _ = c := by
      rw [integral_const_mul, integral_complex_ofReal, kernel_integral L hb,
        Complex.ofReal_one, mul_one]

theorem variance_sqrt (t : ℝ≥0) : variance (Real.sqrt (t : ℝ)) = t := by
  apply NNReal.eq
  exact Real.sq_sqrt t.property

/-- The actual original Neumann semigroup preserves nonnegative real functions, including at zero. -/
theorem heat_preserves_nonnegative (t : ℝ≥0) (f : ComplexIntervalL2 0 L)
    (hf : ∀ᵐ y ∂intervalMeasure 0 L, 0 ≤ (f y).re ∧ (f y).im = 0) :
    ∀ᵐ x ∂intervalMeasure 0 L,
      0 ≤ (NeumannHeatSemigroup.heat L t f x).re ∧
        (NeumannHeatSemigroup.heat L t f x).im = 0 := by
  by_cases ht : t = 0
  · simpa only [ht, NeumannHeatSemigroup.heat_zero] using hf
  · have hp : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    have hb : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr hp
    have h := heat_coe_integral L hb f
    rw [variance_sqrt] at h
    filter_upwards [h] with x hx
    rw [hx]
    exact integralValue_nonneg L hb f hf x

theorem heat_fixes_constants (t : ℝ≥0) (f : ComplexIntervalL2 0 L) (c : ℂ)
    (hf : f =ᵐ[intervalMeasure 0 L] fun _ => c) :
    NeumannHeatSemigroup.heat L t f = f := by
  by_cases ht : t = 0
  · simp only [ht, NeumannHeatSemigroup.heat_zero]
  · have hp : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
    have hb : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr hp
    have h := heat_coe_integral L hb f
    rw [variance_sqrt] at h
    apply Lp.ext
    filter_upwards [h, hf] with x hx hfx
    rw [hx, integralValue_const L hb f c hf x, hfx]

theorem constantMode_inner (f : ComplexIntervalL2 0 L) :
    inner ℂ (neumannCosineMode L 0) f =
      (Real.sqrt L : ℂ)⁻¹ * ∫ y : ℝ, f y ∂intervalMeasure 0 L := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [neumannCosineMode_zero_coe L] with y hy
  simp only [RCLike.inner_apply', hy, map_inv₀, Complex.conj_ofReal]

theorem heat_preserves_integral (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    (∫ y : ℝ, NeumannHeatSemigroup.heat L t f y ∂intervalMeasure 0 L) =
      ∫ y : ℝ, f y ∂intervalMeasure 0 L := by
  have h := NeumannHeatSemigroup.heat_coefficient L t f 0
  rw [NeumannHeatSemigroup.decay_mode_zero, Complex.ofReal_one, one_mul,
    constantMode_inner, constantMode_inner] at h
  apply mul_left_cancel₀ _ h
  apply inv_ne_zero
  exact_mod_cast (Real.sqrt_pos.mpr hL.out).ne'

end GeneratedFoundations.Spectral.GaussianHeatKernel
