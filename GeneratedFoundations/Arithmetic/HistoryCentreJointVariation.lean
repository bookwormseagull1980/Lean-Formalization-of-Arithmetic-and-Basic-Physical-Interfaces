module

public import GeneratedFoundations.Arithmetic.HistoryCentreCurvatureResponse

/-!
# Joint variation of the actual centre potential and weighted curvature

The source displacement and the connection vary together in the same
functional. The exponential weight is retained, including its nonlinear
dependence on the source. At an unbiased flat configuration the field energy
starts at degree two; differentiating the exponential therefore first
contributes in degree three. This proves the vacuum Hessian splitting from
the complete action, rather than defining a block-diagonal surrogate.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCentreJointVariation

open HistoryGaugeJets
open HistoryCliffordAction (Index Space)
open HistoryCentreCurvatureResponse
open Geometry.HilbertPolynomialVariation

def polynomial (a b c t : ℝ) : ℝ := t ^ 2 * a + t ^ 3 * b + t ^ 4 * c

def polynomialDerivative (a b c t : ℝ) : ℝ :=
  2 * t * a + 3 * t ^ 2 * b + 4 * t ^ 3 * c

theorem polynomial_hasDerivAt (a b c t : ℝ) :
    HasDerivAt (polynomial a b c) (polynomialDerivative a b c t) t := by
  change HasDerivAt (fun s : ℝ => s ^ 2 * a + s ^ 3 * b + s ^ 4 * c)
    (2 * t * a + 3 * t ^ 2 * b + 4 * t ^ 3 * c) t
  simpa only [polynomial, polynomialDerivative, zero_add, add_zero, mul_zero] using
    Geometry.HilbertTraceVariation.quartic_hasDerivAt 0 0 a b c t

theorem polynomialDerivative_hasDerivAt_zero (a b c : ℝ) :
    HasDerivAt (polynomialDerivative a b c) (2 * a) 0 := by
  convert! Geometry.HilbertTraceVariation.quartic_hasDerivAt 0 (2 * a) (3 * b)
    (4 * c) 0 0 using 1
  · funext t
    unfold polynomialDerivative
    ring
  · simp

def exponentialRayDerivative (k a b c t : ℝ) : ℝ :=
  Real.exp (t * k) * (k * polynomial a b c t + polynomialDerivative a b c t)

theorem exponentialRay_hasDerivAt (k a b c t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (u * k) * polynomial a b c u)
      (exponentialRayDerivative k a b c t) t := by
  convert! (((hasDerivAt_id t).mul_const k).exp).mul
    (polynomial_hasDerivAt a b c t) using 1
  unfold exponentialRayDerivative
  simp only [id_eq]
  ring

theorem exponentialRayDerivative_hasDerivAt_zero (k a b c : ℝ) :
    HasDerivAt (exponentialRayDerivative k a b c) (2 * a) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).mul_const k).exp).mul
    (((polynomial_hasDerivAt a b c 0).const_mul k).add
      (polynomialDerivative_hasDerivAt_zero a b c))
  convert! h using 1
  simp [polynomial, polynomialDerivative]

def columnDerivative (N : ℕ) (v : ℝ) (A V : ConnectionJet N)
    (μ ν : CoordinateIndex N) (i : Index N) (t : ℝ) : ℝ :=
  exponentialRayDerivative (v * centreSign i)
    (energy (HistoryCurvatureVariation.linearized N A V μ ν (basis N i)))
    (inner ℝ (HistoryCurvatureVariation.linearized N A V μ ν (basis N i))
      (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i)))
    (energy (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i))) t

theorem columnRay_hasDerivAt (N : ℕ) (v t : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) (μ ν : CoordinateIndex N) (i : Index N) :
    HasDerivAt (fun u : ℝ => weight (u * v) i * energy
      (curvature (HistoryCurvatureVariation.line N A V (u : ℂ)) μ ν (basis N i)))
      (columnDerivative N v A V μ ν i t) t := by
  convert! exponentialRay_hasDerivAt (v * centreSign i)
    (energy (HistoryCurvatureVariation.linearized N A V μ ν (basis N i)))
    (inner ℝ (HistoryCurvatureVariation.linearized N A V μ ν (basis N i))
      (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i)))
    (energy (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i))) t using 1
  funext u
  rw [HistoryCurvatureVariation.curvature_line, hA]
  simp only [LinearMap.add_apply, LinearMap.smul_apply,
    ← Complex.ofReal_pow, Complex.coe_smul, zero_add]
  have hp := energy_quadratic_path
    (0 : Space N) (HistoryCurvatureVariation.linearized N A V μ ν (basis N i))
    (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i)) u
  simp only [zero_add, inner_zero_left, mul_zero, add_zero] at hp
  have he : energy (0 : Space N) = 0 := by simp [energy]
  rw [he, zero_add] at hp
  rw [hp]
  unfold weight polynomial energy
  rw [mul_assoc]

def rayDerivative (N : ℕ) (v : ℝ) (A V : ConnectionJet N) (t : ℝ) : ℝ :=
  HistoryCentrePotential.force N (t * v) * v +
    ∑ μ, ∑ ν, ∑ i, columnDerivative N v A V μ ν i t

theorem action_ray_hasDerivAt (N : ℕ) (v t : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) :
    HasDerivAt (fun u : ℝ => action N (u * v)
      (HistoryCurvatureVariation.line N A V (u : ℂ))) (rayDerivative N v A V t) t := by
  have hp := (HistoryCentrePotential.potential_hasDerivAt N (t * v)).comp t
    ((hasDerivAt_id t).mul_const v)
  have hs := hp.add (HasDerivAt.sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.sum (u := Finset.univ) fun ν _ =>
      HasDerivAt.sum (u := Finset.univ) fun i _ =>
        columnRay_hasDerivAt N v t A V hA μ ν i)
  convert! hs using 1
  · funext u
    simp only [action, weightedEnergy, Function.comp_def, Pi.add_apply, Finset.sum_apply, id_eq]
  · simp [rayDerivative]

/-- The second derivative of the complete source/field ray. Its source
coefficient is calculated from the actual partition and its field coefficient
retains all matrix columns and all ordered curvature slots. -/
theorem action_ray_secondDeriv_zero (N : ℕ) (v : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) :
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => action N (u * v)
      (HistoryCurvatureVariation.line N A V (u : ℂ))) t)
      (v ^ 2 + hessian N 0 A V V) 0 := by
  have hp := ((HistoryCentrePotential.force_hasDerivAt N ((0 : ℝ) * v)).comp 0
    ((hasDerivAt_id (0 : ℝ)).mul_const v)).mul_const v
  have hs := hp.add (HasDerivAt.sum (u := Finset.univ) fun μ _ =>
    HasDerivAt.sum (u := Finset.univ) fun ν _ =>
      HasDerivAt.sum (u := Finset.univ) fun i _ =>
        exponentialRayDerivative_hasDerivAt_zero (v * centreSign i)
          (energy (HistoryCurvatureVariation.linearized N A V μ ν (basis N i)))
          (inner ℝ (HistoryCurvatureVariation.linearized N A V μ ν (basis N i))
            (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i)))
          (energy (HistoryCurvatureVariation.quadraticTerm N V μ ν (basis N i))))
  convert! hs using 1
  · funext t
    rw [(action_ray_hasDerivAt N v t A V hA).deriv]
    simp only [rayDerivative, columnDerivative, Pi.add_apply, Finset.sum_apply,
      Function.comp_def, id_eq]
  · simp only [hessian, weightedPair, hA, LinearMap.zero_apply,
      inner_zero_left, mul_zero, Finset.sum_const_zero, add_zero, weight_zero, one_mul,
      real_inner_self_eq_norm_sq, energy, HistoryJointCentreResponse.closed_susceptibility,
      zero_mul]
    apply congrArg₂ (fun a b : ℝ => a + b)
    · ring
    · apply Finset.sum_congr rfl
      intro μ _
      apply Finset.sum_congr rfl
      intro ν _
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem joint_hessian_nonneg (N : ℕ) (v : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) : 0 ≤ v ^ 2 + hessian N 0 A V V :=
  add_nonneg (sq_nonneg _) (hessian_flat_nonneg N 0 A V hA)

/-- The joint source direction is strictly restored; field null directions
are precisely the kernel of the actual linearized curvature. -/
theorem joint_hessian_zero_iff (N : ℕ) (v : ℝ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) :
    v ^ 2 + hessian N 0 A V V = 0 ↔
      v = 0 ∧ ∀ μ ν, HistoryCurvatureVariation.linearized N A V μ ν = 0 := by
  rw [hessian_unbiased]
  have hnonneg := HistoryCurvatureVariation.hessian_flat_nonneg N A V hA
  constructor
  · intro he
    have hv : v ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    refine ⟨sq_eq_zero_iff.mp hv, ?_⟩
    apply (HistoryCurvatureVariation.hessian_flat_eq_zero_iff N A V hA).mp
    linarith
  · rintro ⟨rfl, hV⟩
    rw [(HistoryCurvatureVariation.hessian_flat_eq_zero_iff N A V hA).mpr hV]
    norm_num

structure Conclusions : Prop where
  actual_joint_second_derivative : ∀ N v A V,
    (∀ μ ν, curvature A μ ν = 0) →
    HasDerivAt (fun t : ℝ => deriv (fun u : ℝ => action N (u * v)
      (HistoryCurvatureVariation.line N A V (u : ℂ))) t)
      (v ^ 2 + hessian N 0 A V V) 0
  joint_nonnegative : ∀ N v A V, (∀ μ ν, curvature A μ ν = 0) →
    0 ≤ v ^ 2 + hessian N 0 A V V
  exact_joint_kernel : ∀ N v A V, (∀ μ ν, curvature A μ ν = 0) →
    (v ^ 2 + hessian N 0 A V V = 0 ↔
      v = 0 ∧ ∀ μ ν, HistoryCurvatureVariation.linearized N A V μ ν = 0)

theorem generated : Conclusions where
  actual_joint_second_derivative := action_ray_secondDeriv_zero
  joint_nonnegative := joint_hessian_nonneg
  exact_joint_kernel := joint_hessian_zero_iff

end GeneratedFoundations.Arithmetic.HistoryCentreJointVariation
