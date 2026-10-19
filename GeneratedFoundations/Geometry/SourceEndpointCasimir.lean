module

public import GeneratedFoundations.Geometry.SourceQuotientCasimir
public import GeneratedFoundations.Correlation.Endpoints
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Tactic.FieldSimp

/-!
# Endpoint scaling of the original source differential operator

The radius is the global correlation endpoint. Scaling the trace metric by
`R²` replaces its unit source directions by their `R⁻¹` multiples. The
derivatives below use the corresponding reparametrized source curves;
their negative square sum is `R⁻²` times the original round Casimir.

On the actual central quotient, this identity holds on the full finite
coefficient core. Its unique self-adjoint closure has exactly the original
closed domain at every positive radius, with the same scalar factor in its
action. The construction uses probability Haar measure at every radius.
It does not introduce a new diagonal spectrum in place of a differential
operator or assert a separate manifold curvature theorem.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators LinearPMap Quaternion Matrix.Norms.Elementwise
open GeneratedFoundations.Operations
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceCasimirClosure (energy)
open GeneratedFoundations.Correlation.Endpoints

namespace GeneratedFoundations.Geometry.SourceEndpointCasimir

def inverseSquare (R : ℝ) : ℝ := R⁻¹ ^ 2

theorem inverseSquare_pos {R : ℝ} (hR : 0 < R) : 0 < inverseSquare R := by
  unfold inverseSquare
  positivity

theorem inverseSquare_ne_zero {R : ℝ} (hR : R ≠ 0) : inverseSquare R ≠ 0 :=
  pow_ne_zero 2 (inv_ne_zero hR)

theorem inverseSquare_eq (R : ℝ) : inverseSquare R = (R ^ 2)⁻¹ := by
  rw [inverseSquare, inv_pow]

theorem inverseSquare_mul (c R : ℝ) :
    inverseSquare (c * R) = inverseSquare c * inverseSquare R := by
  simp only [inverseSquare, mul_inv_rev, mul_pow]
  ring

/-- The three velocities are normalized in the rescaled trace metric. -/
theorem scaled_axis_inner {R : ℝ} (hR : R ≠ 0) (a b : Fin 3) :
    R ^ 2 * inner ℝ (R⁻¹ • SourceAxisMetric.unitQuaternion a)
      (R⁻¹ • SourceAxisMetric.unitQuaternion b) = if a = b then 1 else 0 := by
  rw [real_inner_smul_left, real_inner_smul_right, SourceAxisMetric.unitQuaternion_inner]
  split_ifs <;> field_simp [hR]

theorem scaled_axis_matrix_hasDerivAt_zero (R : ℝ) (a : Fin 3) :
    HasDerivAt (fun t : ℝ =>
      (SourceAxisMetric.axisCurve a (2 * (R⁻¹ * t)) : Operations.SourceSpinCorner.Mat2))
      (R⁻¹ • SourceAxisMetric.unitAxis a) 0 := by
  have ht : HasDerivAt (fun t : ℝ => R⁻¹ * t) R⁻¹ 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul R⁻¹
  simpa only [Function.comp_def] using!
    (SourceAxisMetric.unit_axis_matrix_hasDerivAt_zero a).scomp_of_eq 0 ht (by simp)

/-- Differentiation along the actual source curve at the rescaled unit speed. -/
def axisDerivative (R : ℝ) (a : Fin 3) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  deriv (fun t : ℝ => f (g * SourceAxisMetric.axisCurve a (2 * (R⁻¹ * t)))) 0

theorem axisDerivative_eq (R : ℝ) (a : Fin 3) (f : SU2 → ℂ) :
    axisDerivative R a f = fun g =>
      ((R⁻¹ : ℝ) : ℂ) * SourceAxisMetric.unitAxisDerivative a f g := by
  funext g
  have h := deriv_comp_mul_left R⁻¹
    (fun t => f (g * SourceAxisMetric.axisCurve a (2 * t))) (0 : ℝ)
  simpa only [axisDerivative, SourceAxisMetric.unitAxisDerivative, mul_zero,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_eq_mul] using! h

private theorem unitAxisDerivative_const_mul (a : Fin 3) (c : ℂ) (f : SU2 → ℂ) :
    SourceAxisMetric.unitAxisDerivative a (fun g => c * f g) =
      fun g => c * SourceAxisMetric.unitAxisDerivative a f g := by
  funext g
  simp only [SourceAxisMetric.unitAxisDerivative_eq,
    SourceCoefficientDifferentiation.axisDerivative_const_mul]
  ring

theorem axisDerivative_twice_eq (R : ℝ) (a : Fin 3) (f : SU2 → ℂ) :
    axisDerivative R a (axisDerivative R a f) = fun g =>
      (inverseSquare R : ℂ) *
        SourceAxisMetric.unitAxisDerivative a (SourceAxisMetric.unitAxisDerivative a f) g := by
  funext g
  simp only [axisDerivative_eq, unitAxisDerivative_const_mul, inverseSquare,
    Complex.ofReal_pow]
  ring

def differential (R : ℝ) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  -(∑ a : Fin 3, axisDerivative R a (axisDerivative R a f) g)

theorem differential_eq (R : ℝ) (f : SU2 → ℂ) :
    differential R f = fun g => (inverseSquare R : ℂ) * SourceAxisMetric.roundCasimir f g := by
  funext g
  simp only [differential, axisDerivative_twice_eq, SourceAxisMetric.roundCasimir]
  rw [← Finset.mul_sum]
  ring

def scaledEnergy (R : ℝ) (m : ℕ) : ℝ := inverseSquare R * energy m

def finiteCore (R : ℝ) : QuotientL2 →ₗ.[ℂ] QuotientL2 :=
  FiniteEigenbasisCore.finiteMultiplier quotientBasis (fun a => scaledEnergy R a.val.1)

theorem finiteCore_domain (R : ℝ) :
    (finiteCore R).domain = SourceQuotientCasimir.finiteCore.domain := rfl

theorem finiteCore_apply (R : ℝ) (f : (finiteCore R).domain) :
    finiteCore R f = (inverseSquare R : ℂ) •
      SourceQuotientCasimir.finiteCore ⟨f, f.property⟩ := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro a
  have hleft : inner ℂ (quotientBasis a) (finiteCore R f) =
      (scaledEnergy R a.val.1 : ℂ) * inner ℂ (quotientBasis a) (f : QuotientL2) :=
    FiniteEigenbasisCore.coefficients quotientBasis (fun j => scaledEnergy R j.val.1)
      ⟨f, f.property⟩ a
  have hright : inner ℂ (quotientBasis a)
      (SourceQuotientCasimir.finiteCore ⟨f, f.property⟩) =
        (energy a.val.1 : ℂ) * inner ℂ (quotientBasis a) (f : QuotientL2) :=
    FiniteEigenbasisCore.coefficients quotientBasis (fun j => energy j.val.1)
      ⟨f, f.property⟩ a
  rw [inner_smul_right (𝕜 := ℂ), hleft, hright]
  simp only [scaledEnergy, Complex.ofReal_mul, mul_assoc]

/-- The finite core acts by the actual rescaled second derivatives of quotient observations. -/
theorem finiteCore_is_differential (R : ℝ) (f : (finiteCore R).domain) :
    ∃ F H : C(SourceSpinCentre.CentralQuotient, ℂ),
      ContinuousMap.toLp 2 quotientHaar ℂ F = (f : QuotientL2) ∧
      ContinuousMap.toLp 2 quotientHaar ℂ H = finiteCore R f ∧
      ∀ g : SU2, H (SourceCentralObservations.quotientContinuous g) =
        differential R (F.comp SourceCentralObservations.quotientContinuous) g := by
  obtain ⟨F, H, hF, hH, hd⟩ :=
    SourceQuotientCasimir.finiteCore_is_roundCasimir ⟨f, f.property⟩
  refine ⟨F, (inverseSquare R : ℂ) • H, hF, ?_, ?_⟩
  · rw [map_smul, hH, finiteCore_apply]
  · intro g
    rw [ContinuousMap.smul_apply, smul_eq_mul, hd, differential_eq]

def operator (R : ℝ) : QuotientL2 →ₗ.[ℂ] QuotientL2 := (finiteCore R).closure

theorem operator_selfAdjoint (R : ℝ) : IsSelfAdjoint (operator R) :=
  FiniteEigenbasisCore.closure_selfAdjoint quotientBasis (fun a => scaledEnergy R a.val.1)

theorem selfAdjoint_extension_unique (R : ℝ) (T : QuotientL2 →ₗ.[ℂ] QuotientL2)
    (hT : IsSelfAdjoint T) (hcore : finiteCore R ≤ T) : T = operator R :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique quotientBasis
    (fun a => scaledEnergy R a.val.1) T hT hcore

theorem operator_domain_iff_memℓp (R : ℝ) (f : QuotientL2) :
    f ∈ (operator R).domain ↔
      Memℓp (fun a : EvenIndex =>
        (scaledEnergy R a.val.1 : ℂ) * inner ℂ (quotientBasisVector a) f) 2 := by
  simpa only [operator, finiteCore, quotientBasis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_memℓp quotientBasis
      (fun a => scaledEnergy R a.val.1) f

theorem operator_coefficients (R : ℝ) (f : (operator R).domain) (a : EvenIndex) :
    inner ℂ (quotientBasisVector a) (operator R f) =
      (scaledEnergy R a.val.1 : ℂ) * inner ℂ (quotientBasisVector a) (f : QuotientL2) := by
  simpa only [operator, finiteCore, quotientBasis_apply] using
    FiniteEigenbasisCore.closure_coefficients quotientBasis
      (fun a => scaledEnergy R a.val.1) f a

/-- A nonzero metric scaling preserves the entire closed differential domain. -/
theorem operator_domain_iff {R : ℝ} (hR : R ≠ 0) (f : QuotientL2) :
    f ∈ (operator R).domain ↔ f ∈ SourceQuotientCasimir.operator.domain := by
  rw [operator_domain_iff_memℓp, SourceQuotientCasimir.operator_domain_iff_memℓp]
  simp only [scaledEnergy, Complex.ofReal_mul, mul_assoc]
  have hc : (inverseSquare R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (inverseSquare_ne_zero hR)
  constructor
  · intro hf
    simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using
      hf.const_mul (inverseSquare R : ℂ)⁻¹
  · intro hf
    exact hf.const_mul (inverseSquare R : ℂ)

theorem operator_apply {R : ℝ} (hR : R ≠ 0) (f : (operator R).domain) :
    operator R f = (inverseSquare R : ℂ) •
      SourceQuotientCasimir.operator ⟨f, (operator_domain_iff hR f).mp f.property⟩ := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro a
  simp only [quotientBasis_apply, operator_coefficients, inner_smul_right,
    SourceQuotientCasimir.operator_coefficients, scaledEnergy, Complex.ofReal_mul, mul_assoc]

theorem operator_eq_smul {R : ℝ} (hR : R ≠ 0) :
    operator R = (inverseSquare R : ℂ) • SourceQuotientCasimir.operator := by
  apply LinearPMap.ext
  · exact Submodule.ext (operator_domain_iff hR)
  · intro f hf _hg
    exact operator_apply hR ⟨f, hf⟩

theorem operator_dilation {c R : ℝ} (hc : c ≠ 0) (hR : R ≠ 0) :
    operator (c * R) = (inverseSquare c : ℂ) • operator R := by
  rw [operator_eq_smul (mul_ne_zero hc hR), operator_eq_smul hR,
    inverseSquare_mul, Complex.ofReal_mul, smul_smul]

theorem operator_domain_pullback_iff {R : ℝ} (hR : R ≠ 0) (f : QuotientL2) :
    f ∈ (operator R).domain ↔
      pullbackL2 f ∈ SourceCasimirClosure.operator.domain := by
  rw [operator_domain_iff hR, SourceQuotientCasimir.operator_domain_pullback_iff]

theorem basis_mem_domain (R : ℝ) (a : EvenIndex) :
    quotientBasisVector a ∈ (operator R).domain := by
  have h := FiniteEigenbasisCore.basis_mem_domain quotientBasis
    (fun j => scaledEnergy R j.val.1) a
  simpa only [operator, finiteCore, quotientBasis_apply] using
    (FiniteEigenbasisCore.le_closure quotientBasis (fun j => scaledEnergy R j.val.1)).1 h

theorem operator_basis (R : ℝ) (a : EvenIndex) :
    operator R ⟨quotientBasisVector a, basis_mem_domain R a⟩ =
      (scaledEnergy R a.val.1 : ℂ) • quotientBasisVector a := by
  apply EigenbasisClosure.eq_of_coefficients quotientBasis
  intro j
  rw [quotientBasis_apply, operator_coefficients, inner_smul_right,
    orthonormal_iff_ite.mp quotientBasisVector_orthonormal]
  by_cases h : j = a
  · subst j
    rfl
  · simp only [h, ite_false, mul_zero]

theorem eigenvalue_iff (R : ℝ) (z : ℂ) :
    (∃ f : (operator R).domain, (f : QuotientL2) ≠ 0 ∧
      operator R f = z • (f : QuotientL2)) ↔
      ∃ m : ℕ, Even m ∧ z = (scaledEnergy R m : ℂ) := by
  constructor
  · rintro ⟨f, hf, he⟩
    have hn : ∃ a : EvenIndex, inner ℂ (quotientBasisVector a) (f : QuotientL2) ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply EigenbasisClosure.eq_of_coefficients quotientBasis
      intro a
      simpa only [quotientBasis_apply, inner_zero_right] using h a
    obtain ⟨a, ha⟩ := hn
    refine ⟨a.val.1, a.property, ?_⟩
    have hc := operator_coefficients R f a
    rw [he, inner_smul_right] at hc
    exact mul_right_cancel₀ ha hc
  · rintro ⟨m, hm, rfl⟩
    let a : EvenIndex := ⟨⟨m, 0, 0⟩, hm⟩
    exact ⟨⟨quotientBasisVector a, basis_mem_domain R a⟩,
      quotientBasisVector_orthonormal.ne_zero a, operator_basis R a⟩

/-- The global correlation length, denoted as the radius in the geometric formulas.

`radius` and `irEndpoint` name the same quantity: the IR **edge** of the
unit-covariance Gaussian window, `sqrt(2*pi)*b`.  This is the Lean physical
branch's canonical internal radius.  It is **not** the V5 finite-response TT
endpoint `kL`; that endpoint is the root of the TT spectral-sum equation
`A(L)=4/27` and is a different point (about 0.5% below this edge).  Do not
substitute one for the other without the companion TT-response construction. -/
def radius (b : ℝ) : ℝ := irEndpoint b

theorem radius_eq {b : ℝ} (hb : 0 < b) :
    radius b = Real.sqrt (2 * Real.pi) * b := irEndpoint_eq hb

theorem radius_pos {b : ℝ} (hb : 0 < b) : 0 < radius b := irEndpoint_pos hb

theorem radius_sq {b : ℝ} (hb : 0 < b) :
    radius b ^ 2 = 2 * Real.pi * b ^ 2 := by
  rw [radius_eq hb, mul_pow, Real.sq_sqrt (by positivity)]

theorem radius_dilation {b c : ℝ} (hb : 0 < b) (hc : 0 < c) :
    radius (c * b) = c * radius b := irEndpoint_dilation hb hc

theorem windowLength_lt_radius {b : ℝ} (hb : 0 < b) : windowLength b < radius b :=
  sub_lt_self _ (uvEndpoint_pos hb)

theorem endpoint_even_energy (b : ℝ) (n : ℕ) :
    scaledEnergy (radius b) (2 * n) =
      ((2 * (n : ℝ) + 1) ^ 2 - 1) / radius b ^ 2 := by
  rw [scaledEnergy, inverseSquare_eq, SourceQuotientCasimir.even_energy]
  ring

/-- The half-Laplacian convention used for physical correlation time. -/
def heatParameter (b t : ℝ) : ℝ := t / (2 * radius b ^ 2)

theorem heatParameter_uv {b : ℝ} (hb : 0 < b) :
    heatParameter b (separationScale (uvEndpoint b)) = 1 / (4 * Real.pi) := by
  rw [heatParameter, uvEndpoint_scale hb, radius_sq hb]
  field_simp [hb.ne', Real.pi_ne_zero]
  ring

theorem heatParameter_ir {b : ℝ} (hb : 0 < b) :
    heatParameter b (separationScale (irEndpoint b)) = 1 / 4 := by
  rw [heatParameter, irEndpoint_scale hb, radius_sq hb]
  field_simp [hb.ne', Real.pi_ne_zero]
  ring

theorem heatParameter_ratio {b : ℝ} (hb : 0 < b) :
    heatParameter b (separationScale (irEndpoint b)) /
      heatParameter b (separationScale (uvEndpoint b)) = Real.pi := by
  rw [heatParameter_ir hb, heatParameter_uv hb]
  field_simp [Real.pi_ne_zero]

end GeneratedFoundations.Geometry.SourceEndpointCasimir
