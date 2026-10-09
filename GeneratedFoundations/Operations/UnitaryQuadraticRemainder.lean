module

public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Module

/-!
# A quadratic bound for a unitary exponential remainder

The global estimate uses the actual unitary exponential and the fundamental
theorem of calculus on the fixed interval `[0,1]`.  Its dominating quantity
is quadratic in the operator norm.  The local normalized remainder tends
to zero by the second-order Taylor theorem.  These are separate statements:
neither an exponential moment nor a third moment is required by the bound.
-/

@[expose] public section

noncomputable section

open Filter MeasureTheory Set
open scoped Topology Interval

namespace GeneratedFoundations.Operations.UnitaryQuadraticRemainder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Operator := H →L[ℂ] H

def curve (A : Operator (H := H)) (t : ℝ) : Operator (H := H) :=
  NormedSpace.exp (t • A)

omit [CompleteSpace H] in
@[simp] theorem curve_zero (A : Operator (H := H)) : curve A 0 = 1 := by
  simp [curve]

theorem curve_hasDerivAt (A : Operator (H := H)) (t : ℝ) :
    HasDerivAt (curve A) (curve A t * A) t :=
  _root_.hasDerivAt_exp_smul_const A t

theorem curve_deriv (A : Operator (H := H)) : deriv (curve A) = fun t => curve A t * A :=
  funext (fun t => (curve_hasDerivAt A t).deriv)

theorem curve_continuous (A : Operator (H := H)) : Continuous (curve A) :=
  continuous_iff_continuousAt.mpr (fun t => (curve_hasDerivAt A t).continuousAt)

theorem curve_second_deriv (A : Operator (H := H)) (t : ℝ) :
    deriv (deriv (curve A)) t = curve A t * A ^ 2 := by
  rw [curve_deriv]
  simpa only [mul_assoc, pow_two] using ((curve_hasDerivAt A t).mul_const A).deriv

theorem curve_contDiff_two (A : Operator (H := H)) : ContDiff ℝ 2 (curve A) := by
  have hd : Differentiable ℝ (curve A) := fun t => (curve_hasDerivAt A t).differentiableAt
  have hfirst : ContDiff ℝ 1 (curve A) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨hd, ?_⟩
    rw [curve_deriv]
    exact (curve_continuous A).mul continuous_const
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨hd, by simp, ?_⟩
  rw [curve_deriv]
  exact hfirst.mul contDiff_const

theorem real_smul_skew (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) :
    star (t • A) = -(t • A) := by
  simp only [star_smul, star_trivial, hA, smul_neg]

/-- Membership in the actual operator unitary group follows from the
skew-adjoint identity. -/
theorem curve_mem_unitary (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) :
    curve A t ∈ unitary (Operator (H := H)) := by
  let +nondep : NormedAlgebra ℚ (Operator (H := H)) := .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_mem_unitary_of_mem_skewAdjoint
    (skewAdjoint.mem_iff.mpr (real_smul_skew A hA t))

theorem curve_norm_map (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) (x : H) :
    ‖curve A t x‖ = ‖x‖ :=
  ContinuousLinearMap.norm_map_of_mem_unitary (curve_mem_unitary A hA t) x

private theorem curve_mul_norm (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) :
    ‖curve A t * A‖ = ‖A‖ :=
  CStarRing.norm_mem_unitary_mul A (curve_mem_unitary A hA t)

theorem norm_curve_sub_one_le (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) :
    ‖curve A t - 1‖ ≤ ‖t‖ * ‖A‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s (_hs : s ∈ (Set.univ : Set ℝ)) => (curve_hasDerivAt A s).hasDerivWithinAt)
    (fun s _ => (curve_mul_norm A hA s).le) convex_univ
    (mem_univ (0 : ℝ)) (mem_univ t)
  simpa only [curve_zero, sub_zero, mul_comm] using h

/-- The first-order remainder is an integral of actual exponential
increments.  The fixed interval also handles negative external scales. -/
theorem first_remainder_integral (A : Operator (H := H)) :
    NormedSpace.exp A - 1 - A = ∫ s in (0 : ℝ)..1, (curve A s - 1) * A := by
  have hd (s : ℝ) : HasDerivAt (fun r : ℝ => curve A r - 1 - r • A)
      ((curve A s - 1) * A) s := by
    simpa only [one_smul, sub_mul, one_mul, Pi.sub_apply, Function.id_def] using!
      ((curve_hasDerivAt A s).sub_const 1).sub ((hasDerivAt_id s).smul_const A)
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_hs : s ∈ uIcc (0 : ℝ) 1) => hd s)
    ((show Continuous (fun s : ℝ => (curve A s - 1) * A) from
      ((curve_continuous A).sub continuous_const).mul continuous_const).intervalIntegrable 0 1)
  simpa only [curve, zero_smul, one_smul, NormedSpace.exp_zero,
    sub_self, sub_zero] using hi.symm

theorem norm_first_remainder_le_half (A : Operator (H := H)) (hA : star A = -A) :
    ‖NormedSpace.exp A - 1 - A‖ ≤ ‖A‖ ^ 2 / 2 := by
  rw [first_remainder_integral]
  have hbound : ∀ᵐ s : ℝ, s ∈ Ioc (0 : ℝ) 1 →
      ‖(curve A s - 1) * A‖ ≤ s * ‖A‖ ^ 2 := by
    filter_upwards [] with s hs
    calc
      ‖(curve A s - 1) * A‖ ≤ ‖curve A s - 1‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ (‖s‖ * ‖A‖) * ‖A‖ :=
        mul_le_mul_of_nonneg_right (norm_curve_sub_one_le A hA s) (norm_nonneg A)
      _ = s * ‖A‖ ^ 2 := by
        rw [Real.norm_eq_abs, abs_of_nonneg hs.1.le]
        ring
  have hi := intervalIntegral.norm_integral_le_of_norm_le (f := fun s => (curve A s - 1) * A)
    (g := fun s : ℝ => s * ‖A‖ ^ 2) zero_le_one hbound
    ((show Continuous (fun s : ℝ => s * ‖A‖ ^ 2) from
      continuous_id.mul continuous_const).intervalIntegrable 0 1)
  calc
    _ ≤ ∫ s in (0 : ℝ)..1, s * ‖A‖ ^ 2 := hi
    _ = ‖A‖ ^ 2 / 2 := by
      rw [intervalIntegral.integral_mul_const, integral_id]
      norm_num
      ring

def remainder (A : Operator (H := H)) (t : ℝ) : Operator (H := H) :=
  curve A t - 1 - t • A - (t ^ 2 / 2) • (A ^ 2)

omit [CompleteSpace H] in
@[simp] theorem remainder_zero (A : Operator (H := H)) : remainder A 0 = 0 := by
  simp [remainder]

/-- The dominating bound is quadratic, uniformly for every real scale. -/
theorem norm_remainder_le (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) :
    ‖remainder A t‖ ≤ t ^ 2 * ‖A‖ ^ 2 := by
  have hfirst : ‖curve A t - 1 - t • A‖ ≤ t ^ 2 * ‖A‖ ^ 2 / 2 := by
    simpa only [curve, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] using
      norm_first_remainder_le_half (t • A) (real_smul_skew A hA t)
  have ht : 0 ≤ t ^ 2 / 2 := div_nonneg (sq_nonneg t) (by norm_num)
  have hquadratic : ‖(t ^ 2 / 2) • (A ^ 2)‖ ≤ (t ^ 2 / 2) * ‖A‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
    exact mul_le_mul_of_nonneg_left (norm_pow_le' A (by norm_num : 0 < (2 : ℕ))) ht
  calc
    ‖remainder A t‖ ≤ ‖curve A t - 1 - t • A‖ + ‖(t ^ 2 / 2) • (A ^ 2)‖ :=
      norm_sub_le _ _
    _ ≤ t ^ 2 * ‖A‖ ^ 2 / 2 + (t ^ 2 / 2) * ‖A‖ ^ 2 := add_le_add hfirst hquadratic
    _ = t ^ 2 * ‖A‖ ^ 2 := by ring

/-- The normalized remainder has a common quadratic bound, including the
zero scale under the usual total inverse convention. -/
theorem norm_scaled_remainder_le (A : Operator (H := H)) (hA : star A = -A) (t : ℝ) :
    ‖(t ^ 2)⁻¹ • remainder A t‖ ≤ ‖A‖ ^ 2 := by
  by_cases ht : t = 0
  · subst t
    simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (sq_nonneg t))]
  calc
    (t ^ 2)⁻¹ * ‖remainder A t‖ ≤ (t ^ 2)⁻¹ * (t ^ 2 * ‖A‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (norm_remainder_le A hA t)
        (inv_nonneg.mpr (sq_nonneg t))
    _ = ‖A‖ ^ 2 := inv_mul_cancel_left₀ (pow_ne_zero 2 ht) _

theorem norm_remainder_apply_le (A : Operator (H := H)) (hA : star A = -A)
    (t : ℝ) (x : H) : ‖remainder A t x‖ ≤ t ^ 2 * ‖A‖ ^ 2 * ‖x‖ :=
  ((remainder A t).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (norm_remainder_le A hA t) (norm_nonneg x))

private theorem curve_taylor_two (A : Operator (H := H)) (t : ℝ) :
    taylorWithinEval (curve A) 2 univ 0 t = 1 + t • A + (t ^ 2 / 2) • (A ^ 2) := by
  have hd0 : deriv (curve A) 0 = A := by
    simpa only [curve_zero, one_mul] using (curve_hasDerivAt A 0).deriv
  have hdd0 : iteratedDeriv 2 (curve A) 0 = A ^ 2 := by
    rw [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      curve_second_deriv, curve_zero, one_mul]
  norm_num [taylor_within_apply, Finset.sum_range_succ, iteratedDerivWithin_univ,
    iteratedDeriv_zero, iteratedDeriv_one, curve_zero, hd0, hdd0, div_eq_mul_inv, mul_comm]

/-- Local second-order approximation for each fixed bounded operator.
Skew-adjointness is needed for the global bound, not for this Taylor limit. -/
theorem remainder_scaled_tendsto_zero (A : Operator (H := H)) :
    Tendsto (fun t : ℝ => (t ^ 2)⁻¹ • remainder A t) (𝓝 0) (𝓝 0) := by
  have ht := taylor_tendsto (f := curve A) (x₀ := 0) (n := 2)
    convex_univ (mem_univ (0 : ℝ)) (curve_contDiff_two A).contDiffOn
  have hr (t : ℝ) : curve A t - taylorWithinEval (curve A) 2 univ 0 t = remainder A t := by
    rw [curve_taylor_two]
    unfold remainder
    abel
  simpa only [nhdsWithin_univ, sub_zero, hr] using ht

end GeneratedFoundations.Operations.UnitaryQuadraticRemainder
