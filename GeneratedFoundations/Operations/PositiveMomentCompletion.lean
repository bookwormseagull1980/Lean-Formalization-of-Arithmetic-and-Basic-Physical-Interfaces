module

public import GeneratedFoundations.Operations.PositiveMomentRatios
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Complete positive-response comparisons

The drift of adjacent moment ratios is the variance computed in the
original source integral with its normalized product weight.  The same
moments characterize their least common exponential budget.  Neither
statement identifies comparison order with physical time or supplies an
endpoint rule for a different source update.
-/

@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace GeneratedFoundations.Operations.PositiveMomentCompletion

open PositiveMomentRatios

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

def centeredMoment (μ : Measure X) (f : X → ℝ) (n : ℕ) : ℝ :=
  ∫ x, f x ^ n * (f x - ratio μ f n) ^ 2 ∂μ

def weightedVariance (μ : Measure X) (f : X → ℝ) (n : ℕ) : ℝ :=
  centeredMoment μ f n / moment μ f n

theorem product_weight_integral {f : X → ℝ} (n : ℕ)
    (hm : moment μ f n ≠ 0) :
    (∫ x, f x ^ n / moment μ f n ∂μ) = 1 := by
  rw [integral_div]
  exact div_self hm

theorem product_weight_mean {f : X → ℝ} (n : ℕ) :
    (∫ x, f x * (f x ^ n / moment μ f n) ∂μ) = ratio μ f n := by
  have he : (fun x => f x * (f x ^ n / moment μ f n)) =
      (fun x => f x ^ (n + 1) / moment μ f n) := by
    funext x
    ring
  rw [he, integral_div]
  rfl

/-- The variance is integrated against the normalized product weight,
with the original source measure unchanged. -/
theorem weightedVariance_eq_integral {f : X → ℝ} (n : ℕ) :
    weightedVariance μ f n =
      ∫ x, (f x - ratio μ f n) ^ 2 * (f x ^ n / moment μ f n) ∂μ := by
  unfold weightedVariance centeredMoment
  rw [← integral_div]
  congr 1
  funext x
  ring

theorem centeredMoment_nonneg {f : X → ℝ} (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    0 ≤ centeredMoment μ f n :=
  integral_nonneg fun x => mul_nonneg (pow_nonneg (hf x) n) (sq_nonneg _)

theorem centeredMoment_eq [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (n : ℕ) :
    centeredMoment μ f n = moment μ f (n + 2) -
      2 * ratio μ f n * moment μ f (n + 1) +
        ratio μ f n ^ 2 * moment μ f n := by
  have hi (k : ℕ) := integrable_pow_of_bound (μ := μ) hf hbound k
  have he : (fun x => f x ^ n * (f x - ratio μ f n) ^ 2) =
      (fun x => f x ^ (n + 2) - (2 * ratio μ f n) * f x ^ (n + 1) +
        ratio μ f n ^ 2 * f x ^ n) := by
    funext x
    ring
  unfold centeredMoment
  rw [he, integral_add
    (f := fun x => f x ^ (n + 2) - (2 * ratio μ f n) * f x ^ (n + 1))
    (g := fun x => ratio μ f n ^ 2 * f x ^ n)
    ((hi (n + 2)).sub ((hi (n + 1)).const_mul _)) ((hi n).const_mul _),
    integral_sub (f := fun x => f x ^ (n + 2))
      (g := fun x => (2 * ratio μ f n) * f x ^ (n + 1))
      (hi (n + 2)) ((hi (n + 1)).const_mul _)]
  simp only [integral_const_mul, moment]

/-- Exact variance identity in the original source integral. -/
theorem ratio_drift_eq_variance [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L)
    (hpos : ∀ n, 0 < moment μ f n) (n : ℕ) :
    ratio μ f (n + 1) - ratio μ f n =
      weightedVariance μ f n / ratio μ f n := by
  rw [weightedVariance, centeredMoment_eq hf hbound n]
  simp only [ratio, Nat.add_assoc]
  field_simp [(hpos n).ne', (hpos (n + 1)).ne']
  ring

theorem moment_le_endpoint_budget [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 ≤ L)
    (n : ℕ) : moment μ f n ≤ moment μ f 0 * L ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      moment μ f (n + 1) ≤ L * moment μ f n := moment_succ_le hf hbound n
      _ ≤ L * (moment μ f 0 * L ^ n) := mul_le_mul_of_nonneg_left ih hL
      _ = moment μ f 0 * L ^ (n + 1) := by ring

/-- A proposed bound must control every response order on the same source. -/
def IsMomentBudget (μ : Measure X) (f : X → ℝ) (r : ℝ) : Prop :=
  0 ≤ r ∧ ∀ n : ℕ, moment μ f n ≤ moment μ f 0 * r ^ n

theorem endpoint_le_of_budget [IsFiniteMeasure μ] {f : X → ℝ} {L r : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x})
    (hbudget : IsMomentBudget μ f r) : L ≤ r := by
  by_contra hnot
  have hrL : r < L := lt_of_not_ge hnot
  let a := (r + L) / 2
  have ha : 0 < a := by dsimp [a]; linarith [hbudget.1]
  have hra : r < a := by dsimp [a]; linarith
  have haL : a < L := by dsimp [a]; linarith
  let b := μ.real {x | a ≤ f x}
  have hb : 0 < b := by
    have hp := hpeak (L - a) (by linarith)
    simpa only [sub_sub_cancel] using hp
  have hg : Tendsto (fun n : ℕ => moment μ f 0 * (r / a) ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (div_nonneg hbudget.1 ha.le) ((div_lt_one ha).2 hra)) :
      Tendsto (fun n : ℕ => moment μ f 0 * (r / a) ^ n) atTop
        (𝓝 (moment μ f 0 * 0)))
  have hevent := hg.eventually_lt_const hb
  obtain ⟨n, hn⟩ := Filter.Eventually.exists hevent
  have hlow := level_mul_pow_le_moment (μ := μ) hf hbound ha.le n
  have hboth : b * a ^ n ≤ moment μ f 0 * r ^ n :=
    hlow.trans (hbudget.2 n)
  have hquot : b ≤ moment μ f 0 * (r / a) ^ n := by
    rw [div_pow, ← mul_div_assoc]
    apply (le_div_iff₀ (pow_pos ha n)).2
    exact hboth
  exact (not_lt_of_ge hquot) hn

/-- The entire hierarchy characterizes a unique least capacity; no
threshold is included in the definition of a budget. -/
theorem moment_budget_iff [IsFiniteMeasure μ] {f : X → ℝ} {L r : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    IsMomentBudget μ f r ↔ L ≤ r := by
  constructor
  · exact endpoint_le_of_budget hf hbound hL hpeak
  · intro hr
    refine ⟨hL.le.trans hr, fun n => ?_⟩
    exact (moment_le_endpoint_budget hf hbound hL.le n).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL.le hr n)
        (moment_nonneg (fun x => (hbound x).1) 0))

theorem least_moment_budget [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    IsLeast {r : ℝ | IsMomentBudget μ f r} L := by
  exact ⟨(moment_budget_iff hf hbound hL hpeak).2 le_rfl,
    fun r hr => (moment_budget_iff hf hbound hL hpeak).1 hr⟩

/-- Every positive comparison order detects the same upper edge.
This concerns the algebra generated by this response, not all source
observables or a physical stopping operation. -/
theorem moment_successor_bound_iff [IsFiniteMeasure μ] {f : X → ℝ} {L r : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    (∀ n : ℕ, moment μ f (n + 1) ≤ r * moment μ f n) ↔ L ≤ r := by
  have hpos := moment_pos_of_peak_mass (μ := μ) hf hbound hL hpeak
  constructor
  · intro hr
    apply le_of_tendsto (ratio_tendsto (μ := μ) hf hbound hL hpeak)
    exact Eventually.of_forall fun n => (div_le_iff₀ (hpos n)).2 (hr n)
  · intro hr n
    exact (moment_succ_le hf hbound n).trans
      (mul_le_mul_of_nonneg_right hr (hpos n).le)

theorem positive_test_integral_eq [IsFiniteMeasure μ] {f : X → ℝ} {L : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (r : ℝ) (n : ℕ) :
    (∫ x, f x ^ n * (r - f x) ∂μ) =
      r * moment μ f n - moment μ f (n + 1) := by
  have he : (fun x => f x ^ n * (r - f x)) =
      (fun x => r * f x ^ n - f x ^ (n + 1)) := by
    funext x
    ring
  rw [he, integral_sub (f := fun x => r * f x ^ n)
    (g := fun x => f x ^ (n + 1))
    ((integrable_pow_of_bound hf hbound n).const_mul r)
    (integrable_pow_of_bound hf hbound (n + 1)), integral_const_mul]
  rfl

/-- Positivity of the complete product-weight comparison family uniquely
characterizes the response upper edge. No endpoint level is prescribed. -/
theorem positive_tests_iff [IsFiniteMeasure μ] {f : X → ℝ} {L r : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    (∀ n : ℕ, 0 ≤ ∫ x, f x ^ n * (r - f x) ∂μ) ↔ L ≤ r := by
  rw [← moment_successor_bound_iff hf hbound hL hpeak]
  constructor
  · intro hr n
    have h := hr n
    rw [positive_test_integral_eq hf hbound r n] at h
    linarith
  · intro hr n
    rw [positive_test_integral_eq hf hbound r n]
    linarith [hr n]

/-- Positivity against every polynomial square recovers exactly the same
response upper edge. These are tests in the algebra generated by `f`. -/
theorem polynomial_tests_iff [IsFiniteMeasure μ] {f : X → ℝ} {L r : ℝ}
    (hf : Measurable f) (hbound : ∀ x, 0 ≤ f x ∧ f x ≤ L) (hL : 0 < L)
    (hpeak : ∀ ε : ℝ, 0 < ε → 0 < μ.real {x | L - ε ≤ f x}) :
    (∀ p : Polynomial ℝ,
      0 ≤ ∫ x, (r - f x) * (p.eval (f x)) ^ 2 ∂μ) ↔ L ≤ r := by
  have hpos := moment_pos_of_peak_mass (μ := μ) hf hbound hL hpeak
  constructor
  · intro hp
    have hsub : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
      tendsto_atTop_mono (f := fun n : ℕ => n) (fun n => by omega) tendsto_id
    apply le_of_tendsto ((ratio_tendsto (μ := μ) hf hbound hL hpeak).comp hsub)
    refine Eventually.of_forall fun n => ?_
    apply (div_le_iff₀ (hpos (2 * n))).2
    have h := hp (Polynomial.X ^ n)
    have he : (fun x => (r - f x) * ((Polynomial.X ^ n : Polynomial ℝ).eval (f x)) ^ 2) =
        (fun x => f x ^ (2 * n) * (r - f x)) := by
      funext x
      simp only [Polynomial.eval_pow, Polynomial.eval_X]
      ring
    rw [he, positive_test_integral_eq hf hbound r (2 * n)] at h
    linarith
  · intro hr p
    exact integral_nonneg fun x =>
      mul_nonneg (sub_nonneg.mpr ((hbound x).2.trans hr)) (sq_nonneg _)

end GeneratedFoundations.Operations.PositiveMomentCompletion
