module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.Probability.Moments.Variance
public import GeneratedFoundations.Analysis.NonnegativeAdditive
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.Linarith

/-!
# The Gaussian law from composition, square-root scaling, and unit variance

This is the real-coordinate form of the probability conditions in minimal
unbiased compositional change. The comparison class consists of arbitrary
probability measures on `ℝ`, indexed
by strictly positive real parameters. Centering and symmetry are conclusions,
not fields of the assumptions. No condition at the unused parameter zero is
imposed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Real Topology

namespace GeneratedFoundations.Probability

/-- The variance-level content of exact self-similarity before the scale
factor is identified. Independent composition adds variances; unit variance
fixes the remaining dimensional normalization. -/
structure SelfSimilarVarianceScale (a : ℝ≥0 → ℝ) : Prop where
  nonnegative : ∀ t, 0 ≤ a t
  unit : a 1 = 1
  variance_compose : ∀ s t, a (s + t) ^ 2 = a s ^ 2 + a t ^ 2

namespace SelfSimilarVarianceScale

variable {a : ℝ≥0 → ℝ} (h : SelfSimilarVarianceScale a)

include h

/-- Additive variance and unit normalization force the square-root scale.
Thus the exponent `1/2` is a consequence of compositional self-similarity,
not an adjustable member of the comparison class. -/
theorem eq_sqrt (t : ℝ≥0) : a t = Real.sqrt (t : ℝ) := by
  have hlinear := Analysis.NonnegativeAdditive.eq_mul_one
    (fun u : ℝ≥0 => a u ^ 2) (fun u => sq_nonneg (a u)) h.variance_compose t
  have hsq : a t ^ 2 = (t : ℝ) := by
    simpa [h.unit] using hlinear
  have hsqrt : Real.sqrt (t : ℝ) ^ 2 = (t : ℝ) := Real.sq_sqrt t.property
  nlinarith [h.nonnegative t, Real.sqrt_nonneg (t : ℝ)]

end SelfSimilarVarianceScale

/-- The one-dimensional C/S/V hypotheses. Finite second moment is stated
separately from unit variance, so that the totalized real-valued variance
cannot conceal an integrability assumption. -/
structure CompositionalGaussianAxioms (μ : ℝ → Measure ℝ) : Prop where
  probability : ∀ t, 0 < t → IsProbabilityMeasure (μ t)
  compose : ∀ s t, 0 < s → 0 < t → μ (s + t) = μ s ∗ μ t
  scale : ∀ t, 0 < t → μ t = (μ 1).map (fun x : ℝ => Real.sqrt t * x)
  memLp_two : MemLp (fun x : ℝ => x) 2 (μ 1)
  variance_one : variance (fun x : ℝ => x) (μ 1) = 1

namespace CompositionalGaussianAxioms

variable {μ ν : ℝ → Measure ℝ} (h : CompositionalGaussianAxioms μ)

include h

lemma integrable_id {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => x) (μ t) := by
  let : IsProbabilityMeasure (μ 1) := h.probability 1 zero_lt_one
  rw [h.scale t ht]
  apply (integrable_map_measure measurable_id.aestronglyMeasurable
    (measurable_const.mul measurable_id).aemeasurable).2
  exact (h.memLp_two.integrable (by norm_num)).const_mul (Real.sqrt t)

lemma mean_scale {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ, x ∂μ t) = Real.sqrt t * ∫ x : ℝ, x ∂μ 1 := by
  rw [h.scale t ht]
  rw [integral_map_of_stronglyMeasurable
    (φ := fun x : ℝ => Real.sqrt t * x) (f := fun x : ℝ => x)
    (measurable_const.mul measurable_id) stronglyMeasurable_id]
  exact integral_const_mul _ _

lemma mean_add {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (∫ x : ℝ, x ∂μ (s + t)) =
      (∫ x : ℝ, x ∂μ s) + ∫ x : ℝ, x ∂μ t := by
  let : IsProbabilityMeasure (μ s) := h.probability s hs
  let : IsProbabilityMeasure (μ t) := h.probability t ht
  have hint : Integrable (fun x : ℝ => x) (μ s ∗ μ t) := by
    rw [← h.compose s t hs ht]
    exact h.integrable_id (add_pos hs ht)
  rw [h.compose s t hs ht, integral_conv hint]
  have hinner : (fun x : ℝ => ∫ y : ℝ, x + y ∂μ t) =
      (fun x : ℝ => x + ∫ y : ℝ, y ∂μ t) := by
    funext x
    rw [integral_add (integrable_const x) (h.integrable_id ht)]
    simp
  rw [hinner, integral_add (h.integrable_id hs) (integrable_const _)]
  simp

/-- Composition and square-root scaling force centering. -/
theorem mean_one_eq_zero : (∫ x : ℝ, x ∂μ 1) = 0 := by
  have htwo := h.mean_add (s := 1) (t := 1) (by norm_num) (by norm_num)
  have hfour := h.mean_add (s := 2) (t := 2) (by norm_num) (by norm_num)
  have hscale := h.mean_scale (t := 4) (by norm_num)
  have hsqrt : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hsqrt] at hscale
  norm_num at htwo hfour hscale
  linarith

theorem mean_eq_zero {t : ℝ} (ht : 0 < t) : (∫ x : ℝ, x ∂μ t) = 0 := by
  rw [h.mean_scale ht, h.mean_one_eq_zero, mul_zero]

lemma secondMoment_one : (∫ x : ℝ, x ^ 2 ∂μ 1) = 1 := by
  let : IsProbabilityMeasure (μ 1) := h.probability 1 zero_lt_one
  have hv := h.variance_one
  rw [variance_eq_sub h.memLp_two] at hv
  change (∫ x : ℝ, x ^ 2 ∂μ 1) - (∫ x : ℝ, x ∂μ 1) ^ 2 = 1 at hv
  simpa [h.mean_one_eq_zero] using hv

lemma charFun_nat (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    charFun (μ (n : ℝ)) r = (charFun (μ 1) r) ^ n := by
  let : IsProbabilityMeasure (μ 1) := h.probability 1 zero_lt_one
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
    let : IsProbabilityMeasure (μ (n : ℝ)) := h.probability n hnpos
    rw [Nat.cast_add, Nat.cast_one, h.compose n 1 hnpos zero_lt_one,
      charFun_conv, ih, pow_succ]

/-- Exact stability of the normalized convolution powers, before any limit. -/
lemma charFun_normalized_pow (n : ℕ) (hn : 1 ≤ n) (r : ℝ) :
    (charFun (μ 1) ((Real.sqrt n)⁻¹ * r)) ^ n = charFun (μ 1) r := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnpos)
  rw [← h.charFun_nat n hn, h.scale n hnpos, charFun_map_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hsqrt, one_mul]

theorem charFun_one (r : ℝ) :
    charFun (μ 1) r = Complex.exp (- (r : ℂ) ^ 2 / 2) := by
  let : IsProbabilityMeasure (μ 1) := h.probability 1 zero_lt_one
  have hlimit : Tendsto
      (fun n : ℕ => (charFun (μ 1) ((Real.sqrt n)⁻¹ * r)) ^ n)
      atTop (𝓝 (Complex.exp (- (r : ℂ) ^ 2 / 2))) := by
    simpa only [Measure.map_id] using
      (tendsto_charFun_inv_sqrt_mul_pow (P := μ 1) (X := id)
        measurable_id.aemeasurable h.mean_one_eq_zero h.secondMoment_one r)
  have hconstant : Tendsto
      (fun n : ℕ => (charFun (μ 1) ((Real.sqrt n)⁻¹ * r)) ^ n)
      atTop (𝓝 (charFun (μ 1) r)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (h.charFun_normalized_pow n hn r).symm
  exact tendsto_nhds_unique hconstant hlimit

/-- Uniqueness at the normalized parameter among all real probability laws. -/
theorem law_one_eq_gaussian : μ 1 = gaussianReal 0 1 := by
  let : IsProbabilityMeasure (μ 1) := h.probability 1 zero_lt_one
  apply Measure.ext_of_charFun
  funext r
  rw [h.charFun_one, charFun_gaussianReal]
  congr 1
  simp [neg_div]

/-- Characterization of the positive-parameter family. -/
theorem law_eq_gaussian {t : ℝ} (ht : 0 < t) :
    μ t = gaussianReal 0 (NNReal.mk t ht.le) := by
  rw [h.scale t ht, h.law_one_eq_gaussian, gaussianReal_map_const_mul]
  congr 1
  · simp
  · apply Subtype.ext
    simp [Real.sq_sqrt ht.le]

theorem law_eq_withDensity {t : ℝ} (ht : 0 < t) :
    μ t = volume.withDensity (gaussianPDF 0 (NNReal.mk t ht.le)) := by
  rw [h.law_eq_gaussian ht]
  apply gaussianReal_of_var_ne_zero
  intro hz
  exact (ne_of_gt ht) (congrArg (fun v : ℝ≥0 => (v : ℝ)) hz)

theorem reflection_invariant {t : ℝ} (ht : 0 < t) :
    (μ t).map (fun x : ℝ => -x) = μ t := by
  rw [h.law_eq_gaussian ht, gaussianReal_map_neg]
  simp

theorem variance_eq_parameter {t : ℝ} (ht : 0 < t) :
    variance (fun x : ℝ => x) (μ t) = t := by
  rw [h.law_eq_gaussian ht]
  simp

theorem unique (hν : CompositionalGaussianAxioms ν) {t : ℝ} (ht : 0 < t) :
    μ t = ν t := by
  rw [h.law_eq_gaussian ht, hν.law_eq_gaussian ht]

end CompositionalGaussianAxioms

/-- A concrete family witnessing consistency of the C/S/V comparison class.
Only its strictly positive parameters enter the characterization. -/
noncomputable def gaussianFamily (t : ℝ) : Measure ℝ :=
  gaussianReal 0 t.toNNReal

theorem gaussianFamily_axioms : CompositionalGaussianAxioms gaussianFamily := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    change IsProbabilityMeasure (gaussianReal 0 t.toNNReal)
    infer_instance
  · intro s t hs ht
    simpa [gaussianFamily, Real.toNNReal_add hs.le ht.le] using
      (gaussianReal_conv_gaussianReal (m₁ := 0) (m₂ := 0)
        (v₁ := s.toNNReal) (v₂ := t.toNNReal)).symm
  · intro t ht
    have hvariance :
        NNReal.mk ((Real.sqrt t) ^ 2) (sq_nonneg (Real.sqrt t)) = t.toNNReal := by
      apply Subtype.ext
      simp [Real.sq_sqrt ht.le, Real.coe_toNNReal t ht.le]
    simpa [gaussianFamily, hvariance] using
      (gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt t)).symm
  · simp only [gaussianFamily, Real.toNNReal_one]
    convert! (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)) using 1
  · simp [gaussianFamily]

/-- Existence and uniqueness on the positive-parameter domain. No claim is
made that the unconstrained values at nonpositive parameters are unique. -/
theorem gaussianFamily_exists_unique :
    ∃ μ : ℝ → Measure ℝ, CompositionalGaussianAxioms μ ∧
      ∀ ν : ℝ → Measure ℝ, CompositionalGaussianAxioms ν →
        ∀ t : ℝ, 0 < t → μ t = ν t := by
  refine ⟨gaussianFamily, gaussianFamily_axioms, ?_⟩
  intro ν hν t ht
  exact gaussianFamily_axioms.unique hν ht

end GeneratedFoundations.Probability
