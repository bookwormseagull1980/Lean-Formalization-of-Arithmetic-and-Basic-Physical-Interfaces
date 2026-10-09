module

public import GeneratedFoundations.Correlation.GaussianCorrelation
public import GeneratedFoundations.Correlation.LocalInformation
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Local distinguishability and global mass of the generated Gaussian profile

The endpoint readouts are constructed internally. The unit-information
threshold and peak-equivalent width define the two functionals; their endpoint
values and equation-based uniqueness are then proved. No endpoint value is
supplied to the root construction. The calibration and functional comparison
classes remain explicit and are not a classification of all possible readouts.
Additivity alone fixes information only up to a multiple; the unit calibration
at `exp (-1)` fixes that multiple. Normalized Haar uniqueness concerns the
underlying mass, from which the peak-equivalent width is defined and evaluated.
-/

@[expose] public section

noncomputable section

open MeasureTheory MeasureTheory.Measure
open GeneratedFoundations.Correlation.GaussianCorrelation
open GeneratedFoundations.Correlation.LocalInformation

namespace GeneratedFoundations.Correlation.Endpoints

theorem normalizedHaar_unique (μ : Measure ℝ) [IsAddLeftInvariant μ]
    [IsLocallyFiniteMeasure μ] (hμ : μ (Set.Icc (0 : ℝ) 1) = 1) : μ = volume := by
  rw [addHaarMeasure_unique μ TopologicalSpace.PositiveCompacts.Icc01]
  change μ (Set.Icc (0 : ℝ) 1) • addHaarMeasure TopologicalSpace.PositiveCompacts.Icc01 = volume
  rw [hμ, one_smul, addHaarMeasure_eq_volume]

def information (b d : ℝ) : ℝ := -Real.log (profile b d / profile b 0)

def correlationLevel (b d : ℝ) : CorrelationLevel :=
  ⟨profile b d, profile_pos b d, profile_le_one b d⟩

theorem information_eq (b d : ℝ) : information b d = d ^ 2 / (2 * b ^ 2) :=
  information_profile b d

theorem information_continuous (b : ℝ) : Continuous (information b) := by
  have hf : information b = fun d => d ^ 2 / (2 * b ^ 2) := funext (information_eq b)
  rw [hf]
  exact (continuous_id.pow 2).div_const _

theorem information_strictMonoOn {b : ℝ} (hb : 0 < b) :
    StrictMonoOn (information b) (Set.Ici 0) := by
  intro x hx y hy hxy
  rw [information_eq, information_eq]
  exact div_lt_div_of_pos_right ((sq_lt_sq₀ hx hy).mpr hxy) (by positivity)

theorem calibrated_information {F : CorrelationLevel → ℝ}
    (hF : AdditiveLocalInformation F) (hcal : F (expNeg 1) = 1) (b d : ℝ) :
    F (correlationLevel b d) = information b d := by
  rw [hF.eq_neg_log_of_calibration hcal]
  simp [correlationLevel, information, profile_zero]

def uvThresholdSet (b : ℝ) : Set ℝ := {d | 0 < d ∧ 1 ≤ information b d}

def uvEndpoint (b : ℝ) : ℝ := sInf (uvThresholdSet b)

def irEndpoint (b : ℝ) : ℝ := (∫ d : ℝ, profile b d) / profile b 0

def peakEquivalentWidth (K : ℝ → ℝ) : ℝ :=
  (∫ d : ℝ, K d) / (eLpNorm K ⊤ volume).toReal

theorem irEndpoint_eq_peakEquivalentWidth (b : ℝ) :
    irEndpoint b = peakEquivalentWidth (profile b) := by
  simp only [irEndpoint, peakEquivalentWidth, profile_zero, profile_eLpNorm_top,
    ENNReal.toReal_one]

theorem peakEquivalentWidth_amplitude (K : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    peakEquivalentWidth (fun d => a * K d) = peakEquivalentWidth K := by
  have hn : eLpNorm (fun d => a * K d) ⊤ volume = ‖a‖ₑ * eLpNorm K ⊤ volume := by
    have hf : (fun d => a * K d) = a • K := by
      funext d
      rfl
    rw [hf, eLpNorm_const_smul]
  unfold peakEquivalentWidth
  rw [integral_const_mul, hn, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs, abs_of_pos ha]
  exact mul_div_mul_left _ _ ha.ne'

theorem peakEquivalentWidth_translation {K : ℝ → ℝ} (hK : Continuous K) (a : ℝ) :
    peakEquivalentWidth (fun d => K (d - a)) = peakEquivalentWidth K := by
  have hn : eLpNorm (fun d => K (d - a)) ⊤ volume = eLpNorm K ⊤ volume :=
    eLpNorm_comp_measurePreserving hK.aestronglyMeasurable
      (measurePreserving_sub_right volume a)
  unfold peakEquivalentWidth
  rw [integral_sub_right_eq_self, hn]

theorem eLpNorm_top_dilation (K : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    eLpNorm (fun d => K (d / a)) ⊤ volume = eLpNorm K ⊤ volume := by
  have hm := (MeasurableEquiv.mulLeft₀ a⁻¹ (inv_ne_zero ha.ne')).measurableEmbedding.eLpNorm_map_measure
    (g := K) (p := ⊤) (μ := volume)
  simp only [MeasurableEquiv.coe_mulLeft₀] at hm
  rw [Real.map_volume_mul_left (inv_ne_zero ha.ne'), inv_inv, abs_of_pos ha,
    eLpNorm_smul_measure_of_ne_zero (by positivity : ENNReal.ofReal a ≠ 0) K ⊤ volume] at hm
  simpa [Function.comp_def, div_eq_mul_inv, mul_comm] using hm.symm

theorem peakEquivalentWidth_dilation (K : ℝ → ℝ) {a : ℝ} (ha : 0 < a) :
    peakEquivalentWidth (fun d => K (d / a)) = a * peakEquivalentWidth K := by
  unfold peakEquivalentWidth
  rw [Measure.integral_comp_div, abs_of_pos ha, smul_eq_mul, eLpNorm_top_dilation K ha]
  ring

theorem uvThreshold_iff {b d : ℝ} (hb : 0 < b) :
    d ∈ uvThresholdSet b ↔ Real.sqrt 2 * b ≤ d := by
  have hp : 0 < Real.sqrt 2 * b := by positivity
  have hden : 0 < 2 * b ^ 2 := by positivity
  have hsquare : (Real.sqrt 2 * b) ^ 2 = 2 * b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  constructor
  · intro hd
    have hsq : 2 * b ^ 2 ≤ d ^ 2 := by
      have hi := hd.2
      rw [information_eq, le_div_iff₀ hden, one_mul] at hi
      exact hi
    apply (sq_le_sq₀ hp.le hd.1.le).mp
    rwa [hsquare]
  · intro hd
    refine ⟨lt_of_lt_of_le hp hd, ?_⟩
    rw [information_eq, le_div_iff₀ hden, one_mul]
    rw [← hsquare]
    exact (sq_le_sq₀ hp.le (hp.le.trans hd)).mpr hd

theorem uvEndpoint_isLeast {b : ℝ} (hb : 0 < b) :
    IsLeast (uvThresholdSet b) (Real.sqrt 2 * b) := by
  refine ⟨(uvThreshold_iff hb).mpr le_rfl, ?_⟩
  intro d hd
  exact (uvThreshold_iff hb).mp hd

theorem uvEndpoint_eq {b : ℝ} (hb : 0 < b) :
    uvEndpoint b = Real.sqrt 2 * b := (uvEndpoint_isLeast hb).csInf_eq

theorem uvEndpoint_pos {b : ℝ} (hb : 0 < b) : 0 < uvEndpoint b := by
  rw [uvEndpoint_eq hb]
  positivity

theorem uvEndpoint_information {b : ℝ} (hb : 0 < b) :
    information b (uvEndpoint b) = 1 := by
  rw [information_eq, uvEndpoint_eq hb, mul_pow, Real.sq_sqrt (by norm_num)]
  exact div_self (by positivity)

theorem uvEndpoint_unique {b : ℝ} (hb : 0 < b) :
    ∃! d : ℝ, 0 < d ∧ information b d = 1 := by
  refine ⟨uvEndpoint b, ⟨uvEndpoint_pos hb, uvEndpoint_information hb⟩, ?_⟩
  intro d hd
  rw [uvEndpoint_eq hb]
  apply (sq_eq_sq₀ hd.1.le (by positivity)).mp
  have hi := hd.2
  rw [information_eq] at hi
  have heq := (div_eq_one_iff_eq (show 2 * b ^ 2 ≠ 0 by positivity)).mp
    hi
  rw [mul_pow, Real.sq_sqrt (by norm_num)]
  exact heq

theorem uvEndpoint_level {b : ℝ} (hb : 0 < b) :
    profile b (uvEndpoint b) = Real.exp (-1) := by
  have h := uvEndpoint_information hb
  rw [information_eq] at h
  simp only [profile, h]

theorem irEndpoint_eq {b : ℝ} (hb : 0 < b) :
    irEndpoint b = Real.sqrt (2 * Real.pi) * b := by
  rw [irEndpoint, profile_integral hb, profile_zero, div_one]

theorem irEndpoint_pos {b : ℝ} (hb : 0 < b) : 0 < irEndpoint b := by
  rw [irEndpoint_eq hb]
  positivity

theorem irEndpoint_unique {b : ℝ} (hb : 0 < b) :
    ∃! L : ℝ, 0 < L ∧ profile b 0 * L = ∫ d : ℝ, profile b d := by
  refine ⟨irEndpoint b, ⟨irEndpoint_pos hb, ?_⟩, ?_⟩
  · simp [irEndpoint, profile_zero]
  · intro L hL
    simpa [irEndpoint, profile_zero] using hL.2

theorem irEndpoint_information {b : ℝ} (hb : 0 < b) :
    information b (irEndpoint b) = Real.pi := by
  rw [information_eq, irEndpoint_eq hb, mul_pow, Real.sq_sqrt (by positivity)]
  field_simp [hb.ne']

theorem irEndpoint_level {b : ℝ} (hb : 0 < b) :
    profile b (irEndpoint b) = Real.exp (-Real.pi) := by
  have h := irEndpoint_information hb
  rw [information_eq] at h
  simp only [profile, h]

def windowLength (b : ℝ) : ℝ := irEndpoint b - uvEndpoint b

def activeWindow (b : ℝ) : Set ℝ := Set.Icc (uvEndpoint b) (irEndpoint b)

def separationScale (d : ℝ) : ℝ := d ^ 2 / 2

theorem endpoint_ratio {b : ℝ} (hb : 0 < b) :
    irEndpoint b / uvEndpoint b = Real.sqrt Real.pi := by
  rw [irEndpoint_eq hb, uvEndpoint_eq hb, Real.sqrt_mul (by norm_num)]
  field_simp [hb.ne', Real.sqrt_ne_zero'.mpr (by norm_num : (0 : ℝ) < 2)]

theorem windowLength_eq {b : ℝ} (hb : 0 < b) :
    windowLength b = b * (Real.sqrt (2 * Real.pi) - Real.sqrt 2) := by
  rw [windowLength, irEndpoint_eq hb, uvEndpoint_eq hb]
  ring

theorem windowLength_pos {b : ℝ} (hb : 0 < b) : 0 < windowLength b := by
  rw [windowLength_eq hb]
  apply mul_pos hb
  apply sub_pos.mpr
  apply Real.sqrt_lt_sqrt (by norm_num)
  nlinarith [Real.pi_gt_three]

theorem information_activeWindow {b : ℝ} (hb : 0 < b) :
    information b '' activeWindow b = Set.Icc (1 : ℝ) Real.pi := by
  have he : uvEndpoint b ≤ irEndpoint b := (sub_pos.mp (windowLength_pos hb)).le
  have hm : MonotoneOn (information b) (Set.Icc (uvEndpoint b) (irEndpoint b)) :=
    (information_strictMonoOn hb).monotoneOn.mono (fun _ hx => (uvEndpoint_pos hb).le.trans hx.1)
  have hi := (information_continuous b).continuousOn.image_Icc_of_monotoneOn he hm
  simpa only [activeWindow, uvEndpoint_information hb, irEndpoint_information hb] using hi

theorem uvEndpoint_dilation {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    uvEndpoint (a * b) = a * uvEndpoint b := by
  rw [uvEndpoint_eq (mul_pos ha hb), uvEndpoint_eq hb]
  ring

theorem irEndpoint_dilation {b a : ℝ} (hb : 0 < b) (ha : 0 < a) :
    irEndpoint (a * b) = a * irEndpoint b := by
  rw [irEndpoint_eq (mul_pos ha hb), irEndpoint_eq hb]
  ring

theorem uvEndpoint_scale {b : ℝ} (hb : 0 < b) :
    separationScale (uvEndpoint b) = b ^ 2 := by
  rw [separationScale, uvEndpoint_eq hb, mul_pow, Real.sq_sqrt (by norm_num)]
  ring

theorem irEndpoint_scale {b : ℝ} (hb : 0 < b) :
    separationScale (irEndpoint b) = Real.pi * b ^ 2 := by
  rw [separationScale, irEndpoint_eq hb, mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem endpoint_scale_ratio {b : ℝ} (hb : 0 < b) :
    separationScale (irEndpoint b) / separationScale (uvEndpoint b) = Real.pi := by
  rw [irEndpoint_scale hb, uvEndpoint_scale hb]
  field_simp [hb.ne']

theorem dimensionlessClosure_unique :
    ∃! c : ℝ, 0 < c ∧ Real.sqrt c - Real.sqrt Real.pi = 0 := by
  refine ⟨Real.pi, ⟨Real.pi_pos, sub_self _⟩, ?_⟩
  intro c hc
  have h := sub_eq_zero.mp hc.2
  have hs := congrArg (fun x : ℝ => x ^ 2) h
  simpa [Real.sq_sqrt hc.1.le, Real.sq_sqrt Real.pi_pos.le] using hs

/-- Readout laws are imposed only on pairs of positive scales. -/
structure ReadoutLaws (R : ℝ → ℝ → ℝ) : Prop where
  positive : ∀ x y, 0 < x → 0 < y → 0 < R x y
  continuous : ContinuousOn (fun p : ℝ × ℝ => R p.1 p.2)
    (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))
  scale : ∀ a x y, 0 < a → 0 < x → 0 < y → R (a * x) (a * y) = R x y
  serial : ∀ x y z, 0 < x → 0 < y → 0 < z → R x z = R x y * R y z

def logarithmicReadout (R : ℝ → ℝ → ℝ) (s : ℝ) : ℝ :=
  Real.log (R 1 (Real.exp s))

namespace ReadoutLaws

variable {R : ℝ → ℝ → ℝ} (hR : ReadoutLaws R)

include hR

theorem diagonal {x : ℝ} (hx : 0 < x) : R x x = 1 := by
  have h := hR.serial x x x hx hx hx
  have h' : R x x * 1 = R x x * R x x := by simpa using h
  exact (mul_left_cancel₀ (hR.positive x x hx hx).ne' h').symm

theorem exp_serial (s t : ℝ) :
    R 1 (Real.exp (s + t)) = R 1 (Real.exp s) * R 1 (Real.exp t) := by
  have hs := hR.scale (Real.exp s) 1 (Real.exp t)
    (Real.exp_pos _) (by norm_num) (Real.exp_pos _)
  simp only [mul_one] at hs
  rw [hR.serial 1 (Real.exp s) (Real.exp (s + t))
    (by norm_num) (Real.exp_pos _) (Real.exp_pos _), Real.exp_add, hs]

theorem logarithmic_continuous : Continuous (logarithmicReadout R) := by
  have hc : Continuous (fun s : ℝ => R 1 (Real.exp s)) :=
    hR.continuous.comp_continuous (continuous_const.prodMk Real.continuous_exp)
      (fun s => ⟨by norm_num, Real.exp_pos s⟩)
  exact hc.log (fun s => (hR.positive 1 (Real.exp s) (by norm_num) (Real.exp_pos s)).ne')

theorem logarithmic_add (s t : ℝ) :
    logarithmicReadout R (s + t) = logarithmicReadout R s + logarithmicReadout R t := by
  unfold logarithmicReadout
  rw [hR.exp_serial, Real.log_mul
    (hR.positive 1 (Real.exp s) (by norm_num) (Real.exp_pos s)).ne'
    (hR.positive 1 (Real.exp t) (by norm_num) (Real.exp_pos t)).ne']

theorem logarithmic_linear (s : ℝ) :
    logarithmicReadout R s = s * logarithmicReadout R 1 := by
  let G : ℝ →+ ℝ :=
    { toFun := logarithmicReadout R
      map_zero' := by simp [logarithmicReadout, hR.diagonal (by norm_num : (0 : ℝ) < 1)]
      map_add' := hR.logarithmic_add }
  have hg : Continuous G := hR.logarithmic_continuous
  simpa [G, smul_eq_mul] using map_real_smul G hg s (1 : ℝ)

theorem ratio_reduction {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    R x y = R 1 (y / x) := by
  have hs := hR.scale (1 / x) x y (by positivity) hx hy
  have hx' : 1 / x * x = 1 := by field_simp [hx.ne']
  have hy' : 1 / x * y = y / x := by ring
  rw [hx', hy'] at hs
  exact hs.symm

theorem eq_power {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    R x y = (y / x) ^ logarithmicReadout R 1 := by
  have hp : 0 < y / x := div_pos hy hx
  rw [hR.ratio_reduction hx hy, Real.rpow_def_of_pos hp]
  rw [← hR.logarithmic_linear (Real.log (y / x))]
  simp only [logarithmicReadout, Real.exp_log hp,
    Real.exp_log (hR.positive 1 (y / x) (by norm_num) hp)]

theorem exponent_unique :
    ∃! q : ℝ, ∀ x y, 0 < x → 0 < y → R x y = (y / x) ^ q := by
  refine ⟨logarithmicReadout R 1, ?_, ?_⟩
  · intro x y hx hy
    exact hR.eq_power hx hy
  · intro q hq
    have h := hq 1 (Real.exp 1) (by norm_num) (Real.exp_pos _)
    rw [div_one, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, one_mul] at h
    have hh := congrArg Real.log h
    simpa [logarithmicReadout, Real.log_exp] using hh.symm

/-- The logarithmic differential is normalized at equal positive scales. -/
theorem endpointReadout_unique
    (hunit : HasDerivAt (logarithmicReadout R) 1 0)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : R x y = y / x := by
  have hderiv : HasDerivAt (logarithmicReadout R) (logarithmicReadout R 1) 0 := by
    exact (hasDerivAt_mul_const (x := (0 : ℝ)) (logarithmicReadout R 1)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hR.logarithmic_linear)
  have hq : logarithmicReadout R 1 = 1 := hderiv.unique hunit
  rw [hR.eq_power hx hy, hq, Real.rpow_one]

end ReadoutLaws

theorem ratioReadout_laws : ReadoutLaws (fun x y => y / x) where
  positive x y hx hy := div_pos hy hx
  continuous := continuous_snd.continuousOn.div continuous_fst.continuousOn
    (fun p hp => hp.1.ne')
  scale a x y ha hx _ := by field_simp [ha.ne', hx.ne']
  serial x y z hx hy _ := by
    field_simp [hx.ne', hy.ne']

theorem ratioReadout_normalized :
    HasDerivAt (logarithmicReadout (fun x y => y / x)) 1 0 := by
  have hf : logarithmicReadout (fun x y => y / x) = id := by
    funext s
    simp [logarithmicReadout]
  rw [hf]
  exact hasDerivAt_id (0 : ℝ)

theorem normalized_readout_endpoint_value {R : ℝ → ℝ → ℝ}
    (hR : ReadoutLaws R) (hunit : HasDerivAt (logarithmicReadout R) 1 0)
    {b : ℝ} (hb : 0 < b) :
    R (separationScale (uvEndpoint b)) (separationScale (irEndpoint b)) = Real.pi := by
  rw [hR.endpointReadout_unique hunit]
  · exact endpoint_scale_ratio hb
  · rw [uvEndpoint_scale hb]
    positivity
  · rw [irEndpoint_scale hb]
    positivity

end GeneratedFoundations.Correlation.Endpoints
