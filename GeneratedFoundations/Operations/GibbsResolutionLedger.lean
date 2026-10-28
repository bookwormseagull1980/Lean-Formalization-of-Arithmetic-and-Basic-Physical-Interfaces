module

public import GeneratedFoundations.Operations.GibbsTraceForm
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Complete Gibbs response under a decrease of the reference intensities

The exponential divided difference is treated by its complete integral, also
at repeated eigenvalues. The response ledger retains every matrix entry and
the change of its actual mean. The contraction concerns the unnormalized
connected response; the reference partition is never replaced by one.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.GibbsResolutionLedger

open PreparedTraceForm (Mat)
open GibbsExponentialDifferentiation (expDividedDifference expDividedDifference_self)
open GibbsTraceForm

/-- The full logarithmic-mean kernel, including coincident intensities. -/
theorem divided_difference_integral (a b : ℝ) :
    expDividedDifference a b = ∫ u : ℝ in 0..1, Real.exp ((1 - u) * a + u * b) := by
  by_cases h : a = b
  · subst b
    simp only [expDividedDifference_self]
    have he : (fun u : ℝ => Real.exp ((1 - u) * a + u * a)) = fun _ => Real.exp a := by
      funext u
      congr 1
      ring
    rw [he]
    simp
  · have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    have D : ∀ u : ℝ, HasDerivAt
        (fun v : ℝ => Real.exp ((1 - v) * a + v * b) / (b - a))
        (Real.exp ((1 - u) * a + u * b)) u := by
      intro u
      have hl : HasDerivAt (fun v : ℝ => (1 - v) * a + v * b) (b - a) u := by
        have he : (fun v : ℝ => (1 - v) * a + v * b) = fun v => (b - a) * v + a := by
          funext v
          ring
        rw [he]
        simpa only [mul_one] using! ((hasDerivAt_id u).const_mul (b - a)).add_const a
      convert hl.exp.div_const (b - a) using 1
      field_simp [hd]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => D u)
      ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((1-u)*a+u*b))).intervalIntegrable 0 1)]
    simp [expDividedDifference, h]
    ring

/-- A common decrease in both actual log intensities controls the complete
kernel; no endpoint or interpolation parameter is discarded. -/
theorem divided_difference_le_shift {a b c d r : ℝ}
    (hc : c ≤ a - r) (hd : d ≤ b - r) :
    expDividedDifference c d ≤ Real.exp (-r) * expDividedDifference a b := by
  rw [divided_difference_integral, divided_difference_integral,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp ((1-u)*c+u*d))).intervalIntegrable 0 1)
    ((by fun_prop : Continuous (fun u : ℝ => Real.exp (-r) *
      Real.exp ((1-u)*a+u*b))).intervalIntegrable 0 1)
  intro u hu
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h0 := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hu.2)
  have h1 := mul_le_mul_of_nonneg_left hd hu.1
  nlinarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem shifted_pairing (a : ι → ℝ) (K J : Mat ι) (r s : ℝ) :
    responsePairing a (K - r • (1 : Mat ι)) (J - s • (1 : Mat ι)) =
      Z a * gibbsForm a K J + Z a * (mean a K - r) * (mean a J - s) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, responsePairing_one_right, responsePairing_one_left, weightedTrace_one]
  change responsePairing a K J - r * weightedTrace a J -
      s * (weightedTrace a K - r * Z a) = _
  change _ = Z a * (responsePairing a K J / Z a - mean a K * mean a J) + _
  simp only [mean_apply]
  field_simp [Z_ne_zero a]
  ring

/-- Exact mixed-response ledger. The final term is the actual mean change,
not an independently chosen compensating direction. -/
theorem restored_difference (a b : ι → ℝ) (K J : Mat ι) :
    Z a * gibbsForm a K J - Z b * gibbsForm b K J =
      responsePairing a (centered a K) (centered a J) -
        responsePairing b (centered a K) (centered a J) +
          Z b * (mean b K - mean a K) * (mean b J - mean a J) := by
  have ha := shifted_pairing a K J (mean a K) (mean a J)
  have hb := shifted_pairing b K J (mean a K) (mean a J)
  simp only [sub_self, mul_zero, add_zero] at ha
  change responsePairing a (centered a K) (centered a J) = _ at ha
  change responsePairing b (centered a K) (centered a J) = _ at hb
  rw [ha, hb]
  ring

def kernelLoss (a b : ι → ℝ) (K : Mat ι) : ℝ :=
  ∑ i, ∑ j, (expDividedDifference (a i) (a j) - expDividedDifference (b i) (b j)) *
    Complex.normSq (centered a K i j)

omit [Nonempty ι] in
theorem kernelLoss_eq {a b : ι → ℝ} {K : Mat ι} (hK : K.IsHermitian) :
    kernelLoss a b K = responsePairing a (centered a K) (centered a K) -
      responsePairing b (centered a K) (centered a K) := by
  rw [responsePairing_self_normSq a (centered_isHermitian a hK),
    responsePairing_self_normSq b (centered_isHermitian a hK)]
  simp only [kernelLoss, weightedNormSq, sub_mul, Finset.sum_sub_distrib]

theorem restored_square_ledger {a b : ι → ℝ} {K : Mat ι} (hK : K.IsHermitian) :
    Z a * gibbsForm a K K = Z b * gibbsForm b K K + kernelLoss a b K +
      Z b * (mean b K - mean a K) ^ 2 := by
  have h := restored_difference a b K K
  rw [← kernelLoss_eq hK] at h
  nlinarith

omit [Nonempty ι] in
theorem kernelLoss_nonneg {a b : ι → ℝ} (h : ∀ i, b i ≤ a i) (K : Mat ι) :
    0 ≤ kernelLoss a b K := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  apply mul_nonneg _ (Complex.normSq_nonneg _)
  apply sub_nonneg.mpr
  simpa only [sub_zero, neg_zero, Real.exp_zero, one_mul] using
    divided_difference_le_shift (r := 0) (by simpa using h i) (by simpa using h j)

omit [DecidableEq ι] [Nonempty ι] in
theorem weightedNormSq_le {a b : ι → ℝ} {q : ℝ}
    (h : ∀ i j, expDividedDifference (b i) (b j) ≤
      q * expDividedDifference (a i) (a j)) (K : Mat ι) :
    weightedNormSq b K ≤ q * weightedNormSq a K := by
  simp only [weightedNormSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (h i j) (Complex.normSq_nonneg _)

/-- Unnormalized contraction in the full matrix response. All cross-label
entries are estimated in their original logarithmic-mean metric. -/
theorem restored_contraction {a b : ι → ℝ} {q : ℝ}
    (h : ∀ i j, expDividedDifference (b i) (b j) ≤
      q * expDividedDifference (a i) (a j)) {K : Mat ι} (hK : K.IsHermitian) :
    Z b * gibbsForm b K K ≤ q * (Z a * gibbsForm a K K) := by
  have hc := shifted_pairing b K K (mean a K) (mean a K)
  change responsePairing b (centered a K) (centered a K) = _ at hc
  rw [responsePairing_self_normSq b (centered_isHermitian a hK)] at hc
  have ha := gibbsForm_self_normSq a hK
  have he : Z a * gibbsForm a K K = weightedNormSq a (centered a K) := by
    rw [ha, mul_div_cancel₀ _ (Z_ne_zero a)]
  have hp : 0 ≤ Z b * (mean b K - mean a K) ^ 2 :=
    mul_nonneg (Z_pos b).le (sq_nonneg _)
  have hm := weightedNormSq_le h (centered a K)
  rw [he]
  nlinarith

end GeneratedFoundations.Operations.GibbsResolutionLedger
