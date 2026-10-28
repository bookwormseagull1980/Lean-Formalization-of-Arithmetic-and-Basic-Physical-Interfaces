module

public import GeneratedFoundations.Operations.GaussianPrecisionKL

/-!
# Quadratic score moments of the actual precision Gaussian

The observable `q * x^2 / 2` is evaluated on the same probability law as
the Gaussian likelihood ratio. Its variance is calculated from the fourth
moment, rather than assigned as a response coefficient. The derivative
calculation below is an exact moment identity, with no truncation of the
Gaussian law or its precision variation.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace GeneratedFoundations.Operations.GaussianPrecisionMoments

open GaussianPrecisionKL (law)

private theorem fourth_gaussian (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  let g : ℝ → ℝ := fun t => Real.exp ((v : ℝ) * t ^ 2 / 2)
  have he (t : ℝ) : HasDerivAt g ((v : ℝ) * t * g t) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul (v : ℝ)).div_const 2).exp using 1
    dsimp [g]
    ring
  have h1 : deriv g = fun t => (v : ℝ) * t * g t := funext (fun t => (he t).deriv)
  have h2 : deriv (fun t => (v : ℝ) * t * g t) =
      fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * g t := by
    funext t
    apply HasDerivAt.deriv
    convert! ((hasDerivAt_id t).const_mul (v : ℝ)).mul (he t) using 1
    dsimp
    ring
  have h3 : deriv (fun t => ((v : ℝ) + (v : ℝ) ^ 2 * t ^ 2) * g t) =
      fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * g t := by
    funext t
    apply HasDerivAt.deriv
    convert! ((((hasDerivAt_id t).pow 2).const_mul ((v : ℝ) ^ 2)).const_add
      (v : ℝ)).mul (he t) using 1
    dsimp
    ring
  have h4 : deriv (fun t => (3 * (v : ℝ) ^ 2 * t + (v : ℝ) ^ 3 * t ^ 3) * g t) =
      fun t => (3 * (v : ℝ) ^ 2 + 6 * (v : ℝ) ^ 3 * t ^ 2 +
        (v : ℝ) ^ 4 * t ^ 4) * g t := by
    funext t
    apply HasDerivAt.deriv
    convert! (((hasDerivAt_id t).const_mul (3 * (v : ℝ) ^ 2)).add
      (((hasDerivAt_id t).pow 3).const_mul ((v : ℝ) ^ 3))).mul (he t) using 1
    dsimp
    ring
  have hm := iteratedDeriv_mgf_zero
    (X := fun x : ℝ => x) (μ := gaussianReal 0 v) (by simp) 4
  rw [mgf_fun_id_gaussianReal] at hm
  simp only [zero_mul, zero_add] at hm
  change iteratedDeriv 4 g 0 = _ at hm
  rw [show (4 : ℕ) = 3 + 1 by rfl, iteratedDeriv_succ,
    show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ,
    show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ,
    iteratedDeriv_one, h1, h2, h3, h4] at hm
  simpa [g] using hm.symm

/-- Includes zero variance, needed for linear combinations with a kernel. -/
theorem centered_fourth_integral (v : ℝ≥0) :
    (∫ x : ℝ, x ^ 4 ∂gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 :=
  fourth_gaussian v

theorem fourth_integrable (p : ℝ) : Integrable (fun x : ℝ => x ^ 4) (law p) := by
  exact integrable_pow_of_mem_interior_integrableExpSet
    (X := fun x : ℝ => x) (by simp [GaussianPrecisionKL.law]) 4

theorem fourth_integral {p : ℝ} (hp : 0 < p) :
    (∫ x : ℝ, x ^ 4 ∂law p) = 3 * (p⁻¹) ^ 2 := by
  simpa [GaussianPrecisionKL.law, GaussianPrecisionKL.variance_coe hp] using
    fourth_gaussian (GaussianPrecisionKL.variance p)

theorem square_memLp_two (p : ℝ) : MemLp (fun x : ℝ => x ^ 2) 2 (law p) := by
  apply (memLp_two_iff_integrable_sq (by fun_prop)).mpr
  simpa only [← pow_mul] using fourth_integrable p

theorem square_variance {p : ℝ} (hp : 0 < p) :
    ProbabilityTheory.variance (fun x : ℝ => x ^ 2) (law p) = 2 * (p⁻¹) ^ 2 := by
  rw [variance_eq_sub (square_memLp_two p)]
  change (∫ x : ℝ, (x ^ 2) ^ 2 ∂law p) - (∫ x : ℝ, x ^ 2 ∂law p) ^ 2 = _
  simp only [← pow_mul, show (2 : ℕ) * 2 = 4 by rfl]
  rw [fourth_integral hp, GaussianPrecisionKL.square_integral hp]
  ring

def score (q x : ℝ) : ℝ := (q / 2) * x ^ 2

theorem score_mean {p : ℝ} (hp : 0 < p) (q : ℝ) :
    (∫ x : ℝ, score q x ∂law p) = q / (2 * p) := by
  change (∫ x : ℝ, (q / 2) * x ^ 2 ∂law p) = _
  rw [integral_const_mul, GaussianPrecisionKL.square_integral hp]
  ring

theorem score_variance {p : ℝ} (hp : 0 < p) (q : ℝ) :
    ProbabilityTheory.variance (score q) (law p) = q ^ 2 / (2 * p ^ 2) := by
  change ProbabilityTheory.variance (fun x : ℝ => (q / 2) * x ^ 2) (law p) = _
  rw [variance_const_mul, square_variance hp]
  ring

end GeneratedFoundations.Operations.GaussianPrecisionMoments
