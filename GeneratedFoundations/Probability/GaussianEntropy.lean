module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.Moments.Variance
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.Data.EReal.Operations
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Gaussian entropy and logarithmic densities

Differential entropy is defined by the positive and negative integrals of the
logarithmic density. The comparison class is the class of absolutely continuous
probability measures with prescribed first and second moments.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory InformationTheory Filter
open scoped ENNReal NNReal Real Topology

namespace GeneratedFoundations.Probability

/-- Differential entropy relative to Lebesgue measure, with extended-real values. -/
noncomputable def differentialEntropy (μ : Measure ℝ) : EReal :=
  ((∫⁻ x, ENNReal.ofReal (-llr μ volume x) ∂μ) : EReal) -
    ((∫⁻ x, ENNReal.ofReal (llr μ volume x) ∂μ) : EReal)

/-- The measure formulation equals the positive-minus-negative integral of
`−p log p` for every Lebesgue density. -/
lemma differentialEntropy_withDensity {p : ℝ → ℝ≥0∞} (hp : AEMeasurable p volume) :
    differentialEntropy (volume.withDensity p) =
      ((∫⁻ x, p x * ENNReal.ofReal (-Real.log (p x).toReal)) : EReal) -
        ((∫⁻ x, p x * ENNReal.ofReal (Real.log (p x).toReal)) : EReal) := by
  have hr := (withDensity_absolutelyContinuous volume p).ae_le
    (Measure.rnDeriv_withDensity₀ volume hp)
  have hn : (∫⁻ x, ENNReal.ofReal (-llr (volume.withDensity p) volume x)
      ∂volume.withDensity p) =
      ∫⁻ x, ENNReal.ofReal (-Real.log (p x).toReal) ∂volume.withDensity p := by
    apply lintegral_congr_ae
    filter_upwards [hr] with x hx
    simp only [llr, hx]
  have hpos : (∫⁻ x, ENNReal.ofReal (llr (volume.withDensity p) volume x)
      ∂volume.withDensity p) =
      ∫⁻ x, ENNReal.ofReal (Real.log (p x).toReal) ∂volume.withDensity p := by
    apply lintegral_congr_ae
    filter_upwards [hr] with x hx
    simp only [llr, hx]
  rw [differentialEntropy, hn, hpos,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun x => ENNReal.ofReal (-Real.log (p x).toReal))
      hp hp.ennreal_toReal.log.neg.ennreal_ofReal,
    lintegral_withDensity_eq_lintegral_mul₀ (g := fun x => ENNReal.ofReal (Real.log (p x).toReal))
      hp hp.ennreal_toReal.log.ennreal_ofReal]
  rfl

lemma log_gaussianPDFReal_zero {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) :
    Real.log (gaussianPDFReal 0 v x) =
      -Real.log (2 * Real.pi * v) / 2 - x ^ 2 / (2 * v) := by
  have hvpos : 0 < (v : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hcpos : 0 < 2 * Real.pi * (v : ℝ) :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) hvpos
  rw [gaussianPDFReal, sub_zero,
    Real.log_mul (inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr hcpos))) (Real.exp_pos _).ne',
    Real.log_inv, Real.log_sqrt hcpos.le, Real.log_exp]
  ring

lemma integrable_log_gaussianPDFReal_zero {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hX : MemLp (fun x : ℝ => x) 2 μ) {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => Real.log (gaussianPDFReal 0 v x)) μ := by
  simp_rw [log_gaussianPDFReal_zero hv]
  exact (integrable_const _).sub (hX.integrable_sq.div_const (2 * (v : ℝ)))

lemma integral_log_gaussianPDFReal_zero {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℝ => x) 2 μ) {v : ℝ≥0} (hv : v ≠ 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = v) :
    (∫ x, Real.log (gaussianPDFReal 0 v x) ∂μ) =
      -(Real.log (2 * Real.pi * v) + 1) / 2 := by
  simp_rw [log_gaussianPDFReal_zero hv]
  rw [integral_sub (integrable_const _) (hX.integrable_sq.div_const _)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [integral_div, hsecond]
  have hvreal : (v : ℝ) ≠ 0 := by simpa using hv
  field_simp [hvreal]
  ring

/-- The negative part of a log-likelihood ratio is integrable for finite measures. -/
lemma integrable_negPart_llr {μ ν : Measure ℝ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) : Integrable (fun x => max (-llr μ ν x) 0) μ := by
  have hexp : Integrable (fun x => Real.exp (-llr μ ν x)) μ :=
    (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ)).congr
      (exp_neg_llr hμν).symm
  apply hexp.mono_nonneg
    ((measurable_llr μ ν).neg.max measurable_const).aestronglyMeasurable
  · exact ae_of_all _ fun _ => le_max_right _ _
  · exact ae_of_all _ fun x => max_le (by
      change -llr μ ν x ≤ Real.exp (-llr μ ν x)
      have h := Real.add_one_le_exp (-llr μ ν x)
      linarith) (Real.exp_pos _).le

/-- The likelihood ratio against a Gaussian is the difference of log densities. -/
lemma llr_gaussian_eq_logDensity_sub {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) {v : ℝ≥0} (hv : v ≠ 0) :
    llr μ (gaussianReal 0 v) =ᵐ[μ]
      fun x => llr μ volume x - Real.log (gaussianPDFReal 0 v x) := by
  have hr := Measure.rnDeriv_withDensity_right μ volume
    (measurable_gaussianPDF 0 v).aemeasurable
    (ae_of_all _ fun x => (gaussianPDF_pos 0 hv x).ne')
    (ae_of_all _ fun x => (gaussianPDF_lt_top (μ := 0) (v := v) (x := x)).ne)
  rw [← gaussianReal_of_var_ne_zero 0 hv] at hr
  filter_upwards [hμ.ae_le hr, Measure.rnDeriv_pos hμ,
    hμ.ae_le (Measure.rnDeriv_lt_top μ volume)] with x hx hpos hfinite
  simp only [llr, hx, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hg : (gaussianPDF 0 v x).toReal = gaussianPDFReal 0 v x :=
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 v x)
  rw [hg, Real.log_mul (inv_ne_zero (gaussianPDFReal_pos 0 v x hv).ne')
    (ENNReal.toReal_pos hpos.ne' hfinite.ne).ne', Real.log_inv]
  ring

lemma integrable_llr_gaussian_iff {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr μ (gaussianReal 0 v)) μ ↔ Integrable (llr μ volume) μ := by
  rw [integrable_congr (llr_gaussian_eq_logDensity_sub hμ hv)]
  have hg := integrable_log_gaussianPDFReal_zero hX hv
  constructor
  · intro h
    exact (h.add hg).congr (ae_of_all _ fun x => sub_add_cancel _ _)
  · intro h
    exact h.sub hg

/-- Finite second moment controls the positive contribution to differential entropy. -/
lemma integrable_negPart_logDensity {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (fun x => max (-llr μ volume x) 0) μ := by
  have hac : μ ≪ gaussianReal 0 v := hμ.trans (gaussianReal_absolutelyContinuous' 0 hv)
  have hratio := integrable_negPart_llr hac
  have hlog := (integrable_log_gaussianPDFReal_zero hX hv).abs
  apply (hratio.add hlog).mono_nonneg
    ((measurable_llr μ volume).neg.max measurable_const).aestronglyMeasurable
  · exact ae_of_all _ fun _ => le_max_right _ _
  · filter_upwards [llr_gaussian_eq_logDensity_sub hμ hv] with x hx
    apply max_le
    · change -llr μ volume x ≤
        max (-llr μ (gaussianReal 0 v) x) 0 + |Real.log (gaussianPDFReal 0 v x)|
      have hratio_le := le_max_left (-llr μ (gaussianReal 0 v) x) 0
      have hlog_le := neg_le_abs (Real.log (gaussianPDFReal 0 v x))
      linarith
    · exact add_nonneg (le_max_right _ _) (abs_nonneg _)

lemma differentialEntropy_of_integrable {μ : Measure ℝ}
    (h : Integrable (llr μ volume) μ) :
    differentialEntropy μ = (-(∫ x, llr μ volume x ∂μ) : ℝ) := by
  have hp : (∫⁻ x, ENNReal.ofReal (llr μ volume x) ∂μ) ≠ ∞ :=
    ne_of_lt ((lintegral_ofReal_le_lintegral_enorm _).trans_lt h.2)
  have hn : (∫⁻ x, ENNReal.ofReal (-llr μ volume x) ∂μ) ≠ ∞ :=
    ne_of_lt ((lintegral_ofReal_le_lintegral_enorm _).trans_lt h.neg.2)
  rw [differentialEntropy, ← EReal.coe_ennreal_toReal hn,
    ← EReal.coe_ennreal_toReal hp, ← EReal.coe_sub]
  congr 1
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part h]
  ring

/-- Nonintegrable logarithmic density has entropy `−∞`, since its negative
part is controlled by the second moment. -/
lemma differentialEntropy_eq_bot_of_not_integrable {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    {v : ℝ≥0} (hv : v ≠ 0) (h : ¬ Integrable (llr μ volume) μ) :
    differentialEntropy μ = ⊥ := by
  have hn := integrable_negPart_logDensity hμ hX hv
  have hp : (∫⁻ x, ENNReal.ofReal (llr μ volume x) ∂μ) = ∞ := by
    by_contra hfinite
    have hpos : Integrable (fun x => max (llr μ volume x) 0) μ := by
      apply (lintegral_ofReal_ne_top_iff_integrable
        (f := fun x => max (llr μ volume x) 0)
        ((measurable_llr μ volume).max measurable_const).aestronglyMeasurable
        (ae_of_all _ fun _ => le_max_right _ _)).mp
      simpa only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left zero_le] using hfinite
    apply h
    exact (hpos.sub hn).congr (ae_of_all _ fun x => max_zero_sub_max_neg_zero_eq_self _)
  simp [differentialEntropy, hp]

lemma integral_llr_gaussian {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    {v : ℝ≥0} (hv : v ≠ 0) (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = v)
    (h : Integrable (llr μ volume) μ) :
    (∫ x, llr μ (gaussianReal 0 v) x ∂μ) =
      (∫ x, llr μ volume x ∂μ) + (Real.log (2 * Real.pi * v) + 1) / 2 := by
  rw [integral_congr_ae (llr_gaussian_eq_logDensity_sub hμ hv),
    integral_sub h (integrable_log_gaussianPDFReal_zero hX hv),
    integral_log_gaussianPDFReal_zero hX hv hsecond]
  ring

lemma gaussian_logDensity_integrable {v : ℝ≥0} (hv : v ≠ 0) :
    Integrable (llr (gaussianReal 0 v) volume) (gaussianReal 0 v) := by
  apply (integrable_llr_gaussian_iff (gaussianReal_absolutelyContinuous 0 hv)
    (memLp_id_gaussianReal' 2 (by norm_num)) hv).mp
  exact (integrable_zero _ _ _).congr (llr_self _).symm

/-- The Gaussian entropy is finite and has the usual logarithmic value. -/
theorem differentialEntropy_gaussian {v : ℝ≥0} (hv : v ≠ 0) :
    differentialEntropy (gaussianReal 0 v) =
      ((Real.log (2 * Real.pi * v) + 1) / 2 : ℝ) := by
  have hX : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 v) :=
    memLp_id_gaussianReal' 2 (by norm_num)
  have hsecond : (∫ x : ℝ, x ^ 2 ∂gaussianReal 0 v) = v := by
    have hvar := variance_eq_sub hX
    simpa using hvar.symm
  have h := integral_llr_gaussian (gaussianReal_absolutelyContinuous 0 hv)
    hX hv hsecond (gaussian_logDensity_integrable hv)
  have hself : (∫ x, llr (gaussianReal 0 v) (gaussianReal 0 v) x ∂gaussianReal 0 v) = 0 := by
    rw [integral_congr_ae (llr_self _)]
    simp
  rw [hself] at h
  rw [differentialEntropy_of_integrable (gaussian_logDensity_integrable hv)]
  congr 1
  linarith

/-- Maximum entropy at fixed second moment, including the entropy `−∞` case. -/
theorem gaussian_entropy_maximal_of_secondMoment {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    {v : ℝ≥0} (hv : v ≠ 0) (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = v) :
    differentialEntropy μ ≤ differentialEntropy (gaussianReal 0 v) := by
  rw [differentialEntropy_gaussian hv]
  by_cases hi : Integrable (llr μ volume) μ
  · have hac : μ ≪ gaussianReal 0 v :=
      hμ.trans (gaussianReal_absolutelyContinuous' 0 hv)
    have hir := (integrable_llr_gaussian_iff hμ hX hv).mpr hi
    have hnonneg := integral_llr_add_sub_measure_univ_nonneg hac hir
    simp only [probReal_univ, add_sub_cancel_right] at hnonneg
    rw [integral_llr_gaussian hμ hX hv hsecond hi] at hnonneg
    rw [differentialEntropy_of_integrable hi, EReal.coe_le_coe_iff]
    linarith
  · rw [differentialEntropy_eq_bot_of_not_integrable hμ hX hv hi]
    exact bot_le

/-- Equality in the entropy bound determines the probability measure. -/
theorem gaussian_entropy_equality_iff_of_secondMoment {μ : Measure ℝ}
    [IsProbabilityMeasure μ] (hμ : μ ≪ volume)
    (hX : MemLp (fun x : ℝ => x) 2 μ) {v : ℝ≥0} (hv : v ≠ 0)
    (hsecond : (∫ x : ℝ, x ^ 2 ∂μ) = v) :
    differentialEntropy μ = differentialEntropy (gaussianReal 0 v) ↔
      μ = gaussianReal 0 v := by
  constructor
  · intro heq
    have hi : Integrable (llr μ volume) μ := by
      by_contra hni
      rw [differentialEntropy_eq_bot_of_not_integrable hμ hX hv hni,
        differentialEntropy_gaussian hv] at heq
      exact (EReal.coe_ne_bot _).symm heq
    rw [differentialEntropy_of_integrable hi, differentialEntropy_gaussian hv,
      EReal.coe_eq_coe_iff] at heq
    have hac : μ ≪ gaussianReal 0 v :=
      hμ.trans (gaussianReal_absolutelyContinuous' 0 hv)
    have hir := (integrable_llr_gaussian_iff hμ hX hv).mpr hi
    apply klDiv_eq_zero_iff.mp
    rw [klDiv_of_ac_of_integrable hac hir,
      integral_llr_gaussian hμ hX hv hsecond hi]
    have hz : (∫ x, llr μ volume x ∂μ) +
        (Real.log (2 * Real.pi * v) + 1) / 2 = 0 := by linarith
    simp [hz]
  · rintro rfl
    rfl

lemma secondMoment_eq_variance_of_centered {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hX : MemLp (fun x : ℝ => x) 2 μ) (hmean : (∫ x : ℝ, x ∂μ) = 0) :
    (∫ x : ℝ, x ^ 2 ∂μ) = variance (fun x : ℝ => x) μ := by
  rw [variance_eq_sub hX, hmean]
  simp

/-- The centered Gaussian maximizes entropy among all absolutely continuous
probability laws with the prescribed finite variance. -/
theorem gaussian_entropy_maximal {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 0) {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : variance (fun x : ℝ => x) μ = v) :
    differentialEntropy μ ≤ differentialEntropy (gaussianReal 0 v) := by
  apply gaussian_entropy_maximal_of_secondMoment hμ hX hv
  rw [secondMoment_eq_variance_of_centered hX hmean, hvar]

/-- Uniqueness of the entropy maximizer in the complete centered comparison class. -/
theorem gaussian_entropy_equality_iff {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : μ ≪ volume) (hX : MemLp (fun x : ℝ => x) 2 μ)
    (hmean : (∫ x : ℝ, x ∂μ) = 0) {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : variance (fun x : ℝ => x) μ = v) :
    differentialEntropy μ = differentialEntropy (gaussianReal 0 v) ↔
      μ = gaussianReal 0 v := by
  apply gaussian_entropy_equality_iff_of_secondMoment hμ hX hv
  rw [secondMoment_eq_variance_of_centered hX hmean, hvar]

/-- For densities, uniqueness is equality almost everywhere relative to Lebesgue measure. -/
theorem gaussian_entropy_density_equality_iff {p : ℝ → ℝ≥0∞}
    (hp : AEMeasurable p volume) [IsProbabilityMeasure (volume.withDensity p)]
    (hX : MemLp (fun x : ℝ => x) 2 (volume.withDensity p))
    (hmean : (∫ x : ℝ, x ∂volume.withDensity p) = 0)
    {v : ℝ≥0} (hv : v ≠ 0)
    (hvar : variance (fun x : ℝ => x) (volume.withDensity p) = v) :
    differentialEntropy (volume.withDensity p) = differentialEntropy (gaussianReal 0 v) ↔
      p =ᵐ[volume] gaussianPDF 0 v := by
  rw [gaussian_entropy_equality_iff (withDensity_absolutelyContinuous volume p)
    hX hmean hv hvar, gaussianReal_of_var_ne_zero 0 hv]
  exact withDensity_eq_iff_of_sigmaFinite hp (measurable_gaussianPDF 0 v).aemeasurable

end GeneratedFoundations.Probability
