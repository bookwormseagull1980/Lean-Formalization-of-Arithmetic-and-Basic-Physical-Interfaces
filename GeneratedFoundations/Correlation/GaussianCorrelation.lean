module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.OpenPos
public import GeneratedFoundations.Probability.CompositionalGaussian
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! The normalized overlap and total mass of the same Gaussian profile. -/

@[expose] public section

noncomputable section

open MeasureTheory

namespace GeneratedFoundations.Correlation.GaussianCorrelation

def profile (b d : ℝ) : ℝ := Real.exp (-(d ^ 2 / (2 * b ^ 2)))

def rawState (b x y : ℝ) : ℝ := Real.exp (-((y - x) ^ 2 / b ^ 2))

def normalizationMass (b : ℝ) : ℝ :=
  ∫ y : ℝ, Real.exp (-(2 / b ^ 2) * y ^ 2)

def state (b x y : ℝ) : ℝ := rawState b x y / Real.sqrt (normalizationMass b)

def overlap (b x z : ℝ) : ℝ := ∫ y : ℝ, state b x y * state b z y

theorem normalizationMass_eq (b : ℝ) :
    normalizationMass b = Real.sqrt (Real.pi / (2 / b ^ 2)) := by
  exact integral_gaussian (2 / b ^ 2)

theorem normalizationMass_pos {b : ℝ} (hb : 0 < b) : 0 < normalizationMass b := by
  rw [normalizationMass_eq]
  positivity

theorem raw_product {b : ℝ} (hb : 0 < b) (x z y : ℝ) :
    rawState b x y * rawState b z y =
      profile b (x - z) * Real.exp (-(2 / b ^ 2) * (y - (x + z) / 2) ^ 2) := by
  dsimp [rawState, profile]
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp [hb.ne']
  ring

theorem raw_overlap {b : ℝ} (hb : 0 < b) (x z : ℝ) :
    (∫ y : ℝ, rawState b x y * rawState b z y) =
      profile b (x - z) * normalizationMass b := by
  simp_rw [raw_product hb]
  rw [integral_const_mul]
  congr 1
  exact integral_sub_right_eq_self
    (fun y : ℝ => Real.exp (-(2 / b ^ 2) * y ^ 2)) ((x + z) / 2)

theorem overlap_eq_profile {b : ℝ} (hb : 0 < b) (x z : ℝ) :
    overlap b x z = profile b (x - z) := by
  have hm := normalizationMass_pos hb
  have hproduct (y : ℝ) : state b x y * state b z y =
      (normalizationMass b)⁻¹ * (rawState b x y * rawState b z y) := by
    dsimp [state]
    rw [div_mul_div_comm, Real.mul_self_sqrt hm.le]
    ring
  unfold overlap
  simp_rw [hproduct]
  rw [integral_const_mul, raw_overlap hb]
  field_simp [hm.ne']

theorem state_sq_integral {b : ℝ} (hb : 0 < b) (x : ℝ) :
    (∫ y : ℝ, state b x y ^ 2) = 1 := by
  simpa [overlap, profile, pow_two] using overlap_eq_profile hb x x

theorem profile_zero (b : ℝ) : profile b 0 = 1 := by
  simp [profile]

theorem profile_pos (b d : ℝ) : 0 < profile b d := Real.exp_pos _

theorem profile_le_one (b d : ℝ) : profile b d ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (div_nonneg (sq_nonneg d) (mul_nonneg (by norm_num) (sq_nonneg b)))

theorem profile_even (b d : ℝ) : profile b (-d) = profile b d := by
  simp [profile]

theorem profile_abs (b d : ℝ) : profile b |d| = profile b d := by
  simp [profile]

theorem profile_continuous (b : ℝ) : Continuous (profile b) :=
  Real.continuous_exp.comp (((continuous_id.pow 2).div_const (2 * b ^ 2)).neg)

theorem profile_essSup (b : ℝ) : eLpNormEssSup (profile b) volume = 1 := by
  apply le_antisymm
  · have hbound : ∀ᵐ d : ℝ, ‖profile b d‖ ≤ (1 : ℝ) :=
      ae_of_all _ fun d => by
        simpa only [Real.norm_eq_abs, abs_of_pos (profile_pos b d)] using profile_le_one b d
    simpa using eLpNormEssSup_le_of_ae_bound hbound
  · have hae : ∀ᵐ d : ℝ, ENNReal.ofReal (profile b d) ≤ eLpNormEssSup (profile b) volume := by
      filter_upwards [ae_le_eLpNormEssSup (f := profile b) (μ := volume)] with d hd
      simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (profile_pos b d)] using hd
    have hc : IsClosed {d : ℝ | ENNReal.ofReal (profile b d) ≤ eLpNormEssSup (profile b) volume} :=
      isClosed_le (ENNReal.continuous_ofReal.comp (profile_continuous b)) continuous_const
    have hd := Measure.dense_of_ae hae
    have hs : {d : ℝ | ENNReal.ofReal (profile b d) ≤ eLpNormEssSup (profile b) volume} = Set.univ := by
      rw [← hc.closure_eq]
      exact hd.closure_eq
    have hzero : (0 : ℝ) ∈ {d : ℝ | ENNReal.ofReal (profile b d) ≤ eLpNormEssSup (profile b) volume} := by
      rw [hs]
      trivial
    simpa only [Set.mem_ofPred_eq, profile_zero, ENNReal.ofReal_one] using hzero

theorem profile_eLpNorm_top (b : ℝ) : eLpNorm (profile b) ⊤ volume = 1 := by
  rw [eLpNorm_exponent_top (profile_continuous b).aestronglyMeasurable, profile_essSup]

theorem profile_integrable {b : ℝ} (hb : 0 < b) : Integrable (profile b) := by
  have hc : 0 < (1 : ℝ) / (2 * b ^ 2) := by positivity
  convert integrable_exp_neg_mul_sq hc using 1
  ext d
  dsimp [profile]
  congr 1
  ring

theorem profile_integral {b : ℝ} (hb : 0 < b) :
    (∫ d : ℝ, profile b d) = Real.sqrt (2 * Real.pi) * b := by
  have heq : profile b = fun d : ℝ => Real.exp (-(1 / (2 * b ^ 2)) * d ^ 2) := by
    funext d
    dsimp [profile]
    congr 1
    ring
  rw [heq, integral_gaussian]
  have hquot : Real.pi / (1 / (2 * b ^ 2)) = (2 * Real.pi) * b ^ 2 := by
    simp only [one_div, div_inv_eq_mul]
    ring
  rw [hquot, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hb]

theorem information_profile (b d : ℝ) :
    -Real.log (profile b d / profile b 0) = d ^ 2 / (2 * b ^ 2) := by
  rw [profile_zero, div_one]
  simp [profile, Real.log_exp]

theorem state_continuous (b x : ℝ) : Continuous (state b x) := by
  exact (Real.continuous_exp.comp
    ((((continuous_id.sub continuous_const).pow 2).div_const (b ^ 2)).neg)).div_const _

theorem state_memLp {b : ℝ} (hb : 0 < b) (x : ℝ) : MemLp (state b x) 2 volume := by
  apply (memLp_two_iff_integrable_sq (state_continuous b x).aestronglyMeasurable).mpr
  apply Integrable.of_integral_ne_zero
  rw [state_sq_integral hb]
  norm_num

def hilbertState {b : ℝ} (hb : 0 < b) (x : ℝ) : Lp ℝ 2 (volume : Measure ℝ) :=
  (state_memLp hb x).toLp (state b x)

theorem hilbertState_inner {b : ℝ} (hb : 0 < b) (x z : ℝ) :
    inner ℝ (hilbertState hb x) (hilbertState hb z) = profile b (x - z) := by
  rw [L2.inner_def, ← overlap_eq_profile hb x z]
  apply integral_congr_ae
  filter_upwards [(state_memLp hb x).coeFn_toLp, (state_memLp hb z).coeFn_toLp]
    with y hx hz
  change inner ℝ ((state_memLp hb x).toLp (state b x) y)
      ((state_memLp hb z).toLp (state b z) y) = state b x y * state b z y
  rw [hx, hz, Real.inner_apply]

theorem hilbertState_norm {b : ℝ} (hb : 0 < b) (x : ℝ) :
    ‖hilbertState hb x‖ = 1 := by
  have h := hilbertState_inner hb x x
  rw [real_inner_self_eq_norm_sq, sub_self, profile_zero] at h
  nlinarith [norm_nonneg (hilbertState hb x)]

def changeKernel (b d : ℝ) : ℝ := profile b d / (Real.sqrt (2 * Real.pi) * b)

theorem changeKernel_eq_gaussianPDFReal {b : ℝ} (hb : 0 < b) (d : ℝ) :
    changeKernel b d = ProbabilityTheory.gaussianPDFReal 0 (NNReal.mk (b ^ 2) (sq_nonneg b)) d := by
  have hsqrt : Real.sqrt (2 * Real.pi * b ^ 2) = Real.sqrt (2 * Real.pi) * b := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs, abs_of_pos hb]
  simp only [ProbabilityTheory.gaussianPDFReal, NNReal.coe_mk, sub_zero, hsqrt]
  dsimp [changeKernel, profile]
  rw [neg_div]
  ring

theorem sourceLaw_eq_profileDensity {μ : ℝ → Measure ℝ}
    (hμ : GeneratedFoundations.Probability.CompositionalGaussianAxioms μ)
    {b : ℝ} (hb : 0 < b) :
    μ (b ^ 2) = volume.withDensity (fun d => ENNReal.ofReal (changeKernel b d)) := by
  rw [hμ.law_eq_withDensity (sq_pos_of_pos hb)]
  congr 1
  funext d
  simp only [ProbabilityTheory.gaussianPDF, changeKernel_eq_gaussianPDFReal hb]

end GeneratedFoundations.Correlation.GaussianCorrelation
