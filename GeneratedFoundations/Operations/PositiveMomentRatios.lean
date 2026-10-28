module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

/-!
# Adjacent ratios of positive moments

These are comparison readouts of a fixed finite positive source measure.
The results do not identify moment reweighting with a physical source update.
The positivity, log convexity and endpoint estimate are proved from the
underlying integrals, rather than postulated for the ratio sequence.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology

namespace GeneratedFoundations.Operations.PositiveMomentRatios

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def moment (μ : Measure X) (f : X → ℝ) (n : ℕ) : ℝ := ∫ x, f x ^ n ∂μ

def ratio (μ : Measure X) (f : X → ℝ) (n : ℕ) : ℝ :=
  moment μ f (n + 1) / moment μ f n

theorem integrable_pow_of_bound [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (n : ℕ) :
    Integrable (fun x => f x ^ n) μ := by
  refine (integrable_const (L ^ n)).mono' (hf.pow_const n).aestronglyMeasurable ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hbound x).1 n)]
    exact pow_le_pow_left₀ (hbound x).1 (hbound x).2 n

theorem moment_nonneg {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    0 ≤ moment μ f n := integral_nonneg fun x => pow_nonneg (hf x) n

/-- Positive mass above a positive level gives a quantitative lower moment bound. -/
theorem level_mul_pow_le_moment [IsFiniteMeasure μ] {f : X → ℝ} {L a : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (ha : 0 ≤ a) (n : ℕ) :
    μ.real {x | a ≤ f x} * a ^ n ≤ moment μ f n := by
  have hi := integrable_pow_of_bound (μ := μ) hf hbound n
  have hs : MeasurableSet {x | a ≤ f x} := measurableSet_le measurable_const hf
  calc
    _ = ∫ x in {x | a ≤ f x}, a ^ n ∂μ := by
      rw [setIntegral_const, smul_eq_mul]
    _ ≤ ∫ x in {x | a ≤ f x}, f x ^ n ∂μ := by
      apply integral_mono_ae (integrable_const _) hi.restrict
      filter_upwards [ae_restrict_mem hs] with x hx
      exact pow_le_pow_left₀ ha hx n
    _ ≤ moment μ f n := setIntegral_le_integral hi
      (ae_of_all _ fun x => pow_nonneg (hbound x).1 n)

theorem moment_pos_of_level_mass [IsFiniteMeasure μ] {f : X → ℝ} {L a : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (ha : 0 < a) (hmass : 0 < μ.real {x | a ≤ f x}) (n : ℕ) :
    0 < moment μ f n :=
  lt_of_lt_of_le (mul_pos hmass (pow_pos ha n))
    (level_mul_pow_le_moment hf hbound ha.le n)

/-- The bounded source gives an upper endpoint for every adjacent ratio. -/
theorem moment_succ_le [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (n : ℕ) :
    moment μ f (n + 1) ≤ L * moment μ f n := by
  simp only [moment]
  rw [← integral_const_mul]
  apply integral_mono (integrable_pow_of_bound hf hbound (n + 1))
    ((integrable_pow_of_bound hf hbound n).const_mul L)
  intro x
  change f x ^ (n + 1) ≤ L * f x ^ n
  rw [pow_succ]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (hbound x).2 (pow_nonneg (hbound x).1 n)

/-- A weighted square proves log convexity without changing the source law. -/
theorem moment_logconvex [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hpos : ∀ n, 0 < moment μ f n) (n : ℕ) :
    moment μ f (n + 1) ^ 2 ≤ moment μ f n * moment μ f (n + 2) := by
  let q := ratio μ f n
  have hi (k : ℕ) := integrable_pow_of_bound (μ := μ) hf hbound k
  have hsq : 0 ≤ ∫ x, f x ^ (n + 2) - (2 * q) * f x ^ (n + 1) +
      q ^ 2 * f x ^ n ∂μ := by
    apply integral_nonneg
    intro x
    have : 0 ≤ f x ^ n * (f x - q) ^ 2 :=
      mul_nonneg (pow_nonneg (hbound x).1 n) (sq_nonneg _)
    convert this using 1
    ring
  have hcalc := integral_add ((hi (n + 2)).sub ((hi (n + 1)).const_mul (2 * q)))
      ((hi n).const_mul (q ^ 2))
  simp only [Pi.sub_apply, integral_sub (hi (n + 2)) ((hi (n + 1)).const_mul (2 * q)),
    integral_const_mul] at hcalc
  rw [hcalc] at hsq
  change 0 ≤ moment μ f (n + 2) - 2 * q * moment μ f (n + 1) +
    q ^ 2 * moment μ f n at hsq
  have hq : q * moment μ f n = moment μ f (n + 1) := by
    dsimp [q, ratio]
    exact div_mul_cancel₀ _ (hpos n).ne'
  have hq₂ := congrArg (fun t : ℝ => t ^ 2) hq
  have hq₁ := congrArg (fun t : ℝ => t * moment μ f (n + 1)) hq
  nlinarith [mul_nonneg (hpos n).le hsq]

theorem ratio_monotone [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hpos : ∀ n, 0 < moment μ f n) : Monotone (ratio μ f) := by
  apply monotone_nat_of_le_succ
  intro n
  change moment μ f (n + 1) / moment μ f n ≤
    moment μ f (n + 1 + 1) / moment μ f (n + 1)
  rw [div_le_div_iff₀ (hpos n) (hpos (n + 1))]
  simpa only [pow_two, Nat.add_assoc, mul_comm] using
    moment_logconvex hf hbound hpos n

theorem ratio_le [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hpos : ∀ n, 0 < moment μ f n) (n : ℕ) : ratio μ f n ≤ L := by
  exact (div_le_iff₀ (hpos n)).2 (moment_succ_le hf hbound n)

/-- Splitting at a level is expressed as a single pointwise inequality. -/
theorem weighted_defect_le {z L ε : ℝ} (hz : 0 ≤ z) (hzL : z ≤ L)
    (hε : 0 ≤ ε) (hεL : ε ≤ L) (n : ℕ) :
    (L - z) * z ^ n ≤ ε * z ^ n + L * (L - ε) ^ n := by
  have hL : 0 ≤ L := hz.trans hzL
  have hzn : 0 ≤ z ^ n := pow_nonneg hz n
  by_cases hlow : z ≤ L - ε
  · calc
      (L - z) * z ^ n ≤ L * z ^ n :=
        mul_le_mul_of_nonneg_right (by linarith) hzn
      _ ≤ L * (L - ε) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hz hlow n) hL
      _ ≤ ε * z ^ n + L * (L - ε) ^ n :=
        le_add_of_nonneg_left (mul_nonneg hε hzn)
  · calc
      (L - z) * z ^ n ≤ ε * z ^ n :=
        mul_le_mul_of_nonneg_right (by linarith) hzn
      _ ≤ ε * z ^ n + L * (L - ε) ^ n :=
        le_add_of_nonneg_right (mul_nonneg hL (pow_nonneg (sub_nonneg.mpr hεL) n))

theorem moment_defect_le [IsFiniteMeasure μ] {f : X → ℝ} {L ε : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hε : 0 ≤ ε) (hεL : ε ≤ L) (n : ℕ) :
    L * moment μ f n - moment μ f (n + 1) ≤
      ε * moment μ f n + L * μ.real Set.univ * (L - ε) ^ n := by
  have hi (k : ℕ) := integrable_pow_of_bound (μ := μ) hf hbound k
  have hb := integral_mono
    (((hi n).const_mul L).sub (hi (n + 1)))
    (((hi n).const_mul ε).add (integrable_const (L * (L - ε) ^ n)))
    (fun x => by
      change L * f x ^ n - f x ^ (n + 1) ≤
        ε * f x ^ n + L * (L - ε) ^ n
      have h := weighted_defect_le (hbound x).1 (hbound x).2 hε hεL n
      convert h using 1
      ring)
  simp only [Pi.sub_apply, Pi.add_apply] at hb
  have hsub := integral_sub ((hi n).const_mul L) (hi (n + 1))
  have hadd := integral_add ((hi n).const_mul ε) (integrable_const (L * (L - ε) ^ n))
  rw [hsub, hadd] at hb
  simpa only [integral_const_mul, integral_const, smul_eq_mul, moment, mul_assoc, mul_comm,
    mul_left_comm] using hb

/-- A finite error bound in terms of actual mass near the endpoint. -/
theorem ratio_defect_le [IsFiniteMeasure μ] {f : X → ℝ} {L ε : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hε : 0 < ε) (hεL : ε < L)
    (hmass : 0 < μ.real {x | L - ε / 2 ≤ f x}) (n : ℕ) :
    L - ratio μ f n ≤ ε +
      (L * μ.real Set.univ / μ.real {x | L - ε / 2 ≤ f x}) *
        ((L - ε) / (L - ε / 2)) ^ n := by
  let a := L - ε / 2
  let b := μ.real {x | a ≤ f x}
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := hmass
  have hm : 0 < moment μ f n := moment_pos_of_level_mass hf hbound ha hb n
  have hlower := level_mul_pow_le_moment (μ := μ) hf hbound ha.le n
  have hdef := moment_defect_le (μ := μ) hf hbound hε.le hεL.le n
  have hnum : 0 ≤ L * μ.real Set.univ * (L - ε) ^ n := by
    have : 0 ≤ μ.real Set.univ := ENNReal.toReal_nonneg
    have : 0 ≤ L - ε := by linarith
    have : 0 ≤ L := by linarith
    positivity
  have hquot :
      L - ratio μ f n ≤ ε + (L * μ.real Set.univ * (L - ε) ^ n) /
        moment μ f n := by
    have hdiv := (div_le_div_iff_of_pos_right hm).2 hdef
    change L - moment μ f (n + 1) / moment μ f n ≤
      ε + (L * μ.real Set.univ * (L - ε) ^ n) / moment μ f n
    convert hdiv using 1 <;> field_simp [hm.ne']
  calc
    L - ratio μ f n ≤ ε + (L * μ.real Set.univ * (L - ε) ^ n) /
        moment μ f n := hquot
    _ ≤ ε + (L * μ.real Set.univ * (L - ε) ^ n) / (b * a ^ n) := by
      simpa only [add_comm] using add_le_add_left
        (div_le_div_of_nonneg_left hnum (mul_pos hb (pow_pos ha n)) hlower) ε
    _ = ε + (L * μ.real Set.univ / b) * ((L - ε) / a) ^ n := by
      rw [div_pow]
      ring

theorem moment_pos_of_peak_mass [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x})
    (n : ℕ) : 0 < moment μ f n := by
  apply moment_pos_of_level_mass hf hbound (a := L / 2) (by positivity)
  simpa only [sub_half] using hpeak (L / 2) (by positivity)

/-- Every positive-mass peak neighbourhood forces the ratio endpoint to be `L`. -/
theorem ratio_tendsto [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    Tendsto (ratio μ f) atTop (𝓝 L) := by
  have hpos := moment_pos_of_peak_mass (μ := μ) hf hbound hL hpeak
  apply tendsto_order.2
  constructor
  · intro a haL
    let ε := min ((L - a) / 2) (L / 2)
    have hε : 0 < ε := lt_min (by linarith) (by linarith)
    have hε₁ : ε ≤ (L - a) / 2 := min_le_left _ _
    have hε₂ : ε ≤ L / 2 := min_le_right _ _
    have hεL : ε < L := by linarith
    have hden : 0 < L - ε / 2 := by linarith
    have hr₀ : 0 ≤ (L - ε) / (L - ε / 2) :=
      div_nonneg (by linarith) hden.le
    have hr₁ : (L - ε) / (L - ε / 2) < 1 :=
      (div_lt_one hden).2 (by linarith)
    let C := L * μ.real Set.univ / μ.real {x | L - ε / 2 ≤ f x}
    have hgeom : Tendsto (fun n : ℕ =>
        C * ((L - ε) / (L - ε / 2)) ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul
        (tendsto_pow_atTop_nhds_zero_of_lt_one hr₀ hr₁) :
          Tendsto (fun n : ℕ => C * ((L - ε) / (L - ε / 2)) ^ n)
            atTop (𝓝 (C * 0)))
    have hevent := hgeom.eventually_lt_const (by linarith : 0 < L - a - ε)
    filter_upwards [hevent] with n hn
    have hd := ratio_defect_le (μ := μ) hf hbound hε hεL
      (hpeak (ε / 2) (by positivity)) n
    dsimp [C] at hn
    linarith
  · intro b hb
    exact Eventually.of_forall fun n => lt_of_le_of_lt (ratio_le hf hbound hpos n) hb

/-- The complete comparison result, with the same peak-mass condition throughout. -/
theorem positive_moment_ratio_endpoint [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    (∀ n, 0 < moment μ f n) ∧ Monotone (ratio μ f) ∧
      (∀ n, ratio μ f n ≤ L) ∧ Tendsto (ratio μ f) atTop (𝓝 L) := by
  have hp := moment_pos_of_peak_mass (μ := μ) hf hbound hL hpeak
  exact ⟨hp, ratio_monotone hf hbound hp, ratio_le hf hbound hp,
    ratio_tendsto hf hbound hL hpeak⟩

/-- On a source with full topological support, continuity and actual endpoint
attainment establish the peak-mass hypothesis used above. -/
theorem peak_mass_of_continuous_attainment [TopologicalSpace X]
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {f : X → ℝ} {L : ℝ}
    (hf : Continuous f) (hattain : ∃ x, f x = L) (ε : ℝ) (hε : 0 < ε) :
    0 < μ.real {x | L - ε ≤ f x} := by
  obtain ⟨x₀, hx₀⟩ := hattain
  have hopen : IsOpen {x | L - ε < f x} := isOpen_lt continuous_const hf
  have hnonempty : Set.Nonempty {x | L - ε < f x} := ⟨x₀, by simp [hx₀, hε]⟩
  have hstrict : 0 < μ {x | L - ε < f x} := hopen.measure_pos μ hnonempty
  have hweak : 0 < μ {x | L - ε ≤ f x} := by
    apply lt_of_lt_of_le hstrict
    apply measure_mono
    intro x hx
    change L - ε < f x at hx
    change L - ε ≤ f x
    exact hx.le
  exact ENNReal.toReal_pos hweak.ne' (measure_ne_top μ _)

theorem ratio_tendsto_of_continuous_attainment [TopologicalSpace X]
    [BorelSpace X] [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {f : X → ℝ} {L : ℝ}
    (hf : Continuous f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hL : 0 < L) (hattain : ∃ x, f x = L) :
    Tendsto (ratio μ f) atTop (𝓝 L) :=
  ratio_tendsto hf.measurable hbound hL
    (peak_mass_of_continuous_attainment hf hattain)

end GeneratedFoundations.Operations.PositiveMomentRatios
