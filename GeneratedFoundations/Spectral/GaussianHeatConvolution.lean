module

public import GeneratedFoundations.Spectral.PeriodicGaussian
public import Mathlib.Analysis.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Gaussian convolution on a circle

Rescaling the probability Haar circle preserves its measure. The operator
below is a Bochner convolution integral; its Fourier multiplier is obtained
by Fubini and translation invariance, rather than stipulated in its definition.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Topology ENNReal ComplexConjugate

namespace GeneratedFoundations.Spectral.GaussianHeatConvolution

variable (T : ℝ) [hT : Fact (0 < T)]

def unitCircleEquiv : AddCircle T ≃+ UnitAddCircle :=
  AddCircle.equivAddCircle T 1 hT.out.ne' one_ne_zero

theorem unitCircleEquiv_continuous : Continuous (unitCircleEquiv T) :=
  AddCircle.continuous_equivAddCircle _ _ _ _

theorem unitCircleEquiv_measurePreserving :
    MeasurePreserving (unitCircleEquiv T) AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  AddMonoidHom.measurePreserving (f := (unitCircleEquiv T).toAddMonoidHom)
    (unitCircleEquiv_continuous T) (unitCircleEquiv T).surjective (by simp)

theorem unitCircleEquiv_coe (x : ℝ) :
    unitCircleEquiv T (x : AddCircle T) = (x / T : ℝ) := by
  simp only [unitCircleEquiv, AddCircle.equivAddCircle_apply_mk, mul_one, div_eq_mul_inv]

theorem fourier_unitCircleEquiv (n : ℤ) (x : AddCircle T) :
    fourier n (unitCircleEquiv T x) = fourier n x := by
  induction x using QuotientAddGroup.induction_on with
  | H x =>
    rw [unitCircleEquiv_coe, fourier_coe_apply, fourier_coe_apply]
    congr 1
    push_cast
    ring

/-- A periodized Gaussian of variance `b²`, expressed relative to probability Haar. -/
def kernel (b : ℝ) : C(AddCircle T, ℂ) :=
  (PeriodicGaussian.kernel (b / T)).comp ⟨unitCircleEquiv T, unitCircleEquiv_continuous T⟩

theorem kernel_apply (b : ℝ) (x : AddCircle T) :
    kernel T b x = PeriodicGaussian.kernel (b / T) (unitCircleEquiv T x) := rfl

theorem kernel_coe {b : ℝ} (hb : 0 < b) (x : ℝ) :
    kernel T b (x : AddCircle T) =
      ∑' n : ℤ, PeriodicGaussian.density (b / T) (x / T + n) := by
  rw [kernel_apply, unitCircleEquiv_coe, PeriodicGaussian.kernel_coe (div_pos hb hT.out)]

theorem density_rescale {b : ℝ} (hb : 0 < b) (x : ℝ) (n : ℤ) :
    PeriodicGaussian.density (b / T) (x / T + n) =
      (T : ℂ) * PeriodicGaussian.density b (x + T * n) := by
  rw [PeriodicGaussian.density_apply, PeriodicGaussian.density_apply,
    ← Complex.ofReal_mul]
  congr 1
  unfold GeneratedFoundations.Correlation.GaussianCorrelation.changeKernel
    GeneratedFoundations.Correlation.GaussianCorrelation.profile
  have he : (x / T + (n : ℝ)) ^ 2 / (2 * (b / T) ^ 2) =
      (x + T * n) ^ 2 / (2 * b ^ 2) := by
    field_simp [hT.out.ne', hb.ne']
  rw [he]
  have hs : Real.sqrt (2 * Real.pi) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  field_simp [hT.out.ne', hb.ne', hs]

/-- The scale factor is the circumference, because Haar mass is one. -/
theorem kernel_image_sum {b : ℝ} (hb : 0 < b) (x : ℝ) :
    kernel T b (x : AddCircle T) =
      (T : ℂ) * ∑' n : ℤ, PeriodicGaussian.density b (x + T * n) := by
  rw [kernel_coe T hb]
  simp_rw [density_rescale T hb]
  exact tsum_mul_left

theorem kernel_pos {b : ℝ} (hb : 0 < b) (x : AddCircle T) :
    0 < (kernel T b x).re := PeriodicGaussian.kernel_re_pos (div_pos hb hT.out) _

theorem kernel_im_eq_zero {b : ℝ} (hb : 0 < b) (x : AddCircle T) :
    (kernel T b x).im = 0 := PeriodicGaussian.kernel_im_eq_zero (div_pos hb hT.out) _

theorem kernel_even {b : ℝ} (hb : 0 < b) (x : AddCircle T) :
    kernel T b (-x) = kernel T b x := by
  simp only [kernel_apply, map_neg, PeriodicGaussian.kernel_even (div_pos hb hT.out)]

theorem kernel_integral {b : ℝ} (hb : 0 < b) :
    (∫ x : AddCircle T, kernel T b x ∂AddCircle.haarAddCircle) = 1 := by
  rw [show (fun x : AddCircle T => kernel T b x) =
    (PeriodicGaussian.kernel (b / T)) ∘ unitCircleEquiv T from rfl]
  exact ((unitCircleEquiv_measurePreserving T).integral_comp
    (AddCircle.homeomorphAddCircle T 1 hT.out.ne' one_ne_zero).toMeasurableEquiv.measurableEmbedding
    (PeriodicGaussian.kernel (b / T))).trans
      (PeriodicGaussian.kernel_integral (div_pos hb hT.out))

theorem kernel_fourierCoeff {b : ℝ} (hb : 0 < b) (n : ℤ) :
    fourierCoeff (kernel T b) n =
      (Real.exp (-2 * Real.pi ^ 2 * (b / T) ^ 2 * (n : ℝ) ^ 2) : ℂ) := by
  have he : (fun x : AddCircle T => fourier (-n) x • kernel T b x) =
      (fun y : UnitAddCircle => fourier (-n) y • PeriodicGaussian.kernel (b / T) y) ∘
        unitCircleEquiv T := by
    funext x
    simp only [Function.comp_apply, fourier_unitCircleEquiv, kernel_apply]
  unfold fourierCoeff
  rw [he]
  exact ((unitCircleEquiv_measurePreserving T).integral_comp
    (AddCircle.homeomorphAddCircle T 1 hT.out.ne' one_ne_zero).toMeasurableEquiv.measurableEmbedding
    (fun y : UnitAddCircle => fourier (-n) y • PeriodicGaussian.kernel (b / T) y)).trans
      (PeriodicGaussian.kernel_fourierCoeff (div_pos hb hT.out) n)

abbrev CircleL2 := Lp ℂ 2 (AddCircle.haarAddCircle (T := T))

theorem integrable_circleL2 (f : CircleL2 T) : Integrable f AddCircle.haarAddCircle :=
  (Lp.memLp f).integrable (by norm_num)

/-- The integral defining convolution, evaluated at every circle point. -/
def convolutionValue (b : ℝ) (f : CircleL2 T) (x : AddCircle T) : ℂ :=
  ∫ y : AddCircle T, f y * kernel T b (x - y) ∂AddCircle.haarAddCircle

theorem convolution_integrable (b : ℝ) (f : CircleL2 T) (x : AddCircle T) :
    Integrable (fun y : AddCircle T => f y * kernel T b (x - y)) AddCircle.haarAddCircle :=
  (integrable_circleL2 T f).mul_bdd
    ((map_continuous (kernel T b)).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => (kernel T b).norm_coe_le_norm (x - y))

theorem convolutionValue_continuous (b : ℝ) (f : CircleL2 T) :
    Continuous (convolutionValue T b f) := by
  let B : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ
  have hbound : BddAbove (Set.range (fun x : AddCircle T => ‖kernel T b x‖)) :=
    ⟨‖kernel T b‖, by rintro r ⟨x, rfl⟩; exact (kernel T b).norm_coe_le_norm x⟩
  exact hbound.continuous_convolution_right_of_integrable B (integrable_circleL2 T f)
    (map_continuous (kernel T b))

def convolutionMap (b : ℝ) (f : CircleL2 T) : C(AddCircle T, ℂ) :=
  ⟨convolutionValue T b f, convolutionValue_continuous T b f⟩

def convolution (b : ℝ) (f : CircleL2 T) : CircleL2 T :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (convolutionMap T b f)

theorem convolution_coe (b : ℝ) (f : CircleL2 T) :
    convolution T b f =ᵐ[AddCircle.haarAddCircle] convolutionValue T b f :=
  ContinuousMap.coeFn_toLp _ _

omit hT in
theorem fourier_eval_add (n : ℤ) (x y : AddCircle T) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem translated_kernel_fourier (b : ℝ) (n : ℤ) (y : AddCircle T) :
    (∫ x : AddCircle T, fourier (-n) x * kernel T b (x - y) ∂AddCircle.haarAddCircle) =
      fourier (-n) y * fourierCoeff (kernel T b) n := by
  rw [← integral_add_right_eq_self
    (fun x : AddCircle T => fourier (-n) x * kernel T b (x - y)) y]
  simp only [add_sub_cancel_right, fourier_eval_add]
  calc
    _ = ∫ x : AddCircle T, fourier (-n) y * (fourier (-n) x * kernel T b x)
        ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = _ := by rw [integral_const_mul]; rfl

/-- Fubini computes the multiplier of the actual convolution integral. -/
theorem convolution_fourierCoeff (b : ℝ) (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (convolution T b f) n =
      fourierCoeff (kernel T b) n * fourierCoeff f n := by
  have hk : Integrable (kernel T b) AddCircle.haarAddCircle :=
    ((kernel T b).memLp AddCircle.haarAddCircle ℂ (p := 2)).integrable (by norm_num)
  have hprod := (integrable_circleL2 T f).convolution_integrand
    (ContinuousLinearMap.mul ℂ ℂ) hk
  have hm : AEStronglyMeasurable
      (fun p : AddCircle T × AddCircle T => fourier (-n) p.1)
      (AddCircle.haarAddCircle.prod AddCircle.haarAddCircle) :=
    ((map_continuous (fourier (-n))).comp continuous_fst).aestronglyMeasurable
  have hprod' := hprod.bdd_mul hm
    (ae_of_all _ fun p : AddCircle T × AddCircle T =>
      show ‖fourier (-n) p.1‖ ≤ 1 from (Circle.norm_coe _).le)
  rw [fourierCoeff_congr_ae (convolution_coe T b f)]
  unfold fourierCoeff convolutionValue
  simp_rw [smul_eq_mul, ← integral_const_mul]
  rw [integral_integral_swap hprod']
  calc
    (∫ y : AddCircle T, ∫ x : AddCircle T,
        fourier (-n) x * (f y * kernel T b (x - y)) ∂AddCircle.haarAddCircle
          ∂AddCircle.haarAddCircle) =
        ∫ y : AddCircle T, f y * (fourier (-n) y * fourierCoeff (kernel T b) n)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [← translated_kernel_fourier T b n y, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = fourierCoeff (kernel T b) n *
        ∫ y : AddCircle T, fourier (-n) y * f y ∂AddCircle.haarAddCircle := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = _ := by simp only [fourierCoeff, smul_eq_mul, integral_const_mul]

theorem convolution_fourierCoeff_gaussian {b : ℝ} (hb : 0 < b)
    (f : CircleL2 T) (n : ℤ) :
    fourierCoeff (convolution T b f) n =
      (Real.exp (-2 * Real.pi ^ 2 * (b / T) ^ 2 * (n : ℝ) ^ 2) : ℂ) *
        fourierCoeff f n := by
  rw [convolution_fourierCoeff, kernel_fourierCoeff T hb]

theorem fourierCoeff_eq_inner (f : CircleL2 T) (n : ℤ) :
    fourierCoeff f n = inner ℂ (fourierLp 2 n) f := by
  rw [← fourierBasis_repr, HilbertBasis.repr_apply_apply]
  rw [show fourierBasis (T := T) n = fourierLp 2 n from congrFun coe_fourierBasis n]

theorem convolutionValue_even {b : ℝ} (hb : 0 < b) (f : CircleL2 T)
    (hf : ∀ᵐ y ∂AddCircle.haarAddCircle, f (-y) = f y) (x : AddCircle T) :
    convolutionValue T b f (-x) = convolutionValue T b f x :=
  MeasureTheory.convolution_neg_of_neg_eq (ContinuousLinearMap.mul ℂ ℂ) hf
    (ae_of_all _ (kernel_even T hb))

theorem convolutionValue_const {b : ℝ} (hb : 0 < b) (f : CircleL2 T) (c : ℂ)
    (hf : f =ᵐ[AddCircle.haarAddCircle] fun _ => c) (x : AddCircle T) :
    convolutionValue T b f x = c := by
  calc
    _ = ∫ y : AddCircle T, c * kernel T b (x - y) ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [hf] with y hy
      rw [hy]
    _ = c := by
      rw [integral_const_mul, integral_sub_left_eq_self, kernel_integral T hb, mul_one]

/-- Positivity refers to pointwise nonnegative real values, not spectral positivity. -/
theorem convolutionValue_nonneg {b : ℝ} (hb : 0 < b) (f : CircleL2 T)
    (hf : ∀ᵐ y ∂AddCircle.haarAddCircle, 0 ≤ (f y).re ∧ (f y).im = 0)
    (x : AddCircle T) : 0 ≤ (convolutionValue T b f x).re ∧
      (convolutionValue T b f x).im = 0 := by
  have heq : convolutionValue T b f x =
      ((∫ y : AddCircle T, (f y).re * (kernel T b (x - y)).re
        ∂AddCircle.haarAddCircle : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [hf] with y hy
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, hy.2,
      kernel_im_eq_zero T hb]
  rw [heq, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨integral_nonneg_of_ae ?_, rfl⟩
  filter_upwards [hf] with y hy
  exact mul_nonneg hy.1 (kernel_pos T hb (x - y)).le

end GeneratedFoundations.Spectral.GaussianHeatConvolution
