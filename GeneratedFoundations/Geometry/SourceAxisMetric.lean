module

public import GeneratedFoundations.Geometry.SourceCoefficientDifferentiation
public import GeneratedFoundations.Geometry.SourceInvariantMetric
public import Mathlib.Analysis.Calculus.Deriv.CompMul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Source-axis velocities in the original trace metric

The actual half-angle source curves have matrix velocities `i J_a`.
Doubling their parameters gives an orthonormal basis of the angular
quaternion space for the already constructed normalized trace metric.
The corresponding represented generators are therefore twice the
half-angle operators, and their negative quadratic sum is the proved
polynomial Casimir. This fixes the metric normalization without defining
or identifying a global Laplace--Beltrami operator.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators Quaternion RealInnerProductSpace ComplexConjugate
open scoped Matrix.Norms.Elementwise
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceAxisDifferentiation
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourcePolarMetric
open GeneratedFoundations.Geometry.SourceInvariantMetric

namespace GeneratedFoundations.Geometry.SourceAxisMetric

abbrev axisCurve := SourceCoefficientDifferentiation.sourceAxis

def spinMatrix : Fin 3 → Mat2 := ![spinMatrix1, spinMatrix2, spinMatrix3]

def axisVelocity (a : Fin 3) : Mat2 := Complex.I • spinMatrix a

def unitAxis (a : Fin 3) : Mat2 := (2 : ℂ) • axisVelocity a

private theorem cosine_half_derivative :
    HasDerivAt (fun t : ℝ => (Real.cos (t / 2) : ℂ)) 0 0 := by
  simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).cos).ofReal_comp

private theorem sine_half_derivative :
    HasDerivAt (fun t : ℝ => (Real.sin (t / 2) : ℂ)) (1 / 2 : ℂ) 0 := by
  simpa using (((hasDerivAt_id (0 : ℝ)).div_const 2).sin).ofReal_comp

theorem x_matrix_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => (xElement t : Mat2)) (Complex.I • spinMatrix1) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [xElement_matrix, spinMatrix1] using cosine_half_derivative
  · simpa [xElement_matrix, spinMatrix1] using sine_half_derivative.const_mul Complex.I
  · simpa [xElement_matrix, spinMatrix1] using sine_half_derivative.const_mul Complex.I
  · simpa [xElement_matrix, spinMatrix1] using cosine_half_derivative

theorem y_matrix_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => (yElement t : Mat2)) (Complex.I • spinMatrix2) 0 := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [yElement, yRotation, spinMatrix2] using cosine_half_derivative
  · simpa [yElement, yRotation, spinMatrix2, ← mul_div_assoc, Pi.neg_apply,
      neg_div] using! sine_half_derivative.neg
  · simpa [yElement, yRotation, spinMatrix2, ← mul_div_assoc] using sine_half_derivative
  · simpa [yElement, yRotation, spinMatrix2] using cosine_half_derivative

private theorem positive_half_phase (t : ℝ) :
    Complex.exp (Complex.I * (t : ℂ) / 2) =
      (Real.cos (t / 2) : ℂ) + (Real.sin (t / 2) : ℂ) * Complex.I := by
  rw [show Complex.I * (t : ℂ) / 2 = ((t / 2 : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_ofReal_mul_I (t / 2)

private theorem negative_half_phase (t : ℝ) :
    Complex.exp (-Complex.I * (t : ℂ) / 2) =
      (Real.cos (t / 2) : ℂ) - (Real.sin (t / 2) : ℂ) * Complex.I := by
  rw [show -Complex.I * (t : ℂ) / 2 = ((-(t / 2) : ℝ) : ℂ) * Complex.I by
    push_cast; ring, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, neg_mul, sub_eq_add_neg]

theorem z_matrix_hasDerivAt_zero :
    HasDerivAt (fun t : ℝ => (zElement t : Mat2)) (Complex.I • spinMatrix3) 0 := by
  simp_rw [zElement, zRotation, negative_half_phase, positive_half_phase]
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · simpa [spinMatrix3, div_eq_mul_inv, Pi.sub_apply,
      mul_comm] using! cosine_half_derivative.sub (sine_half_derivative.mul_const Complex.I)
  · simpa [spinMatrix3] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  · simpa [spinMatrix3] using hasDerivAt_const (0 : ℝ) (0 : ℂ)
  · simpa [spinMatrix3, div_eq_mul_inv, Pi.add_apply,
      mul_comm] using! cosine_half_derivative.add (sine_half_derivative.mul_const Complex.I)

/-- Differentiation of the actual source matrices retains their half-angle scale. -/
theorem axisCurve_hasDerivAt_zero (a : Fin 3) :
    HasDerivAt (fun t : ℝ => (axisCurve a t : Mat2)) (axisVelocity a) 0 := by
  fin_cases a
  · exact x_matrix_hasDerivAt_zero
  · exact y_matrix_hasDerivAt_zero
  · exact z_matrix_hasDerivAt_zero

theorem unitAxis_eq_real_smul (a : Fin 3) : unitAxis a = (2 : ℝ) • axisVelocity a := by
  simp only [unitAxis, two_smul]

/-- The matrix velocity after doubling the actual source parameter. -/
theorem unit_axis_matrix_hasDerivAt_zero (a : Fin 3) :
    HasDerivAt (fun t : ℝ => (axisCurve a (2 * t) : Mat2)) (unitAxis a) 0 := by
  have ht : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
  simpa only [Function.comp_def, unitAxis_eq_real_smul] using!
    (axisCurve_hasDerivAt_zero a).scomp_of_eq (0 : ℝ) ht (by simp)

/-- Quaternion coordinates of the three unit velocities, with their actual signs. -/
def unitQuaternion : Fin 3 → ℍ :=
  ![⟨0, 0, 0, 1⟩, ⟨0, 0, -1, 0⟩, ⟨0, -1, 0, 0⟩]

theorem matrixMap_unitQuaternion (a : Fin 3) : matrixMap (unitQuaternion a) = unitAxis a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [matrixMap_eq, unitQuaternion, unitAxis, axisVelocity, spinMatrix,
      spinMatrix1, spinMatrix2, spinMatrix3, canonical] <;> ring_nf <;> norm_num

theorem unitQuaternion_mem_angular (a : Fin 3) : unitQuaternion a ∈ angularSpace (1 : ℍ) := by
  apply mem_angularSpace.mpr
  fin_cases a <;> norm_num [unitQuaternion, Quaternion.inner_def]

theorem unitQuaternion_inner (a b : Fin 3) :
    inner ℝ (unitQuaternion a) (unitQuaternion b) = if a = b then 1 else 0 := by
  simp only [Quaternion.inner_def]
  fin_cases a <;> fin_cases b <;>
    norm_num [unitQuaternion, Quaternion.re_mul]

def unitTangent (a : Fin 3) : angularSpace (1 : ℍ) :=
  ⟨unitQuaternion a, unitQuaternion_mem_angular a⟩

theorem unitTangent_orthonormal : Orthonormal ℝ unitTangent := by
  rw [orthonormal_iff_ite]
  intro a b
  exact unitQuaternion_inner a b

/-- These actual velocities exhaust the three-dimensional angular tangent space. -/
theorem unitTangent_span : Submodule.span ℝ (Set.range unitTangent) = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card unitTangent_orthonormal.linearIndependent,
    angular_finrank (by simp : ‖(1 : ℍ)‖ = 1)]
  rfl

def tracePair (M N : Mat2) : ℝ := (Matrix.trace (M.conjTranspose * N)).re / 2

theorem tracePair_matrixMap (p q : ℍ) : tracePair (matrixMap p) (matrixMap q) = inner ℝ p q :=
  trace_inner p q

theorem tracePair_of_skew {M N : Mat2} (hM : M.conjTranspose = -M) :
    tracePair M N = -(Matrix.trace (M * N)).re / 2 := by
  simp [tracePair, hM, neg_mul]

theorem unitAxis_skew (a : Fin 3) : (unitAxis a).conjTranspose = -unitAxis a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [unitAxis, axisVelocity, spinMatrix, spinMatrix1, spinMatrix2, spinMatrix3,
      Matrix.conjTranspose_apply]

/-- The normalized trace form of the original source amplitudes makes these axes unit. -/
theorem trace_pairing_unitAxis_orthonormal (a b : Fin 3) :
    tracePair (unitAxis a) (unitAxis b) = if a = b then 1 else 0 := by
  rw [← matrixMap_unitQuaternion, ← matrixMap_unitQuaternion, tracePair_matrixMap,
    unitQuaternion_inner]

theorem traceMetric_unitAxis (a b : Fin 3) :
    traceMetric 1 (1 : unitary ℍ) (unitQuaternion a) (unitQuaternion b) =
      if a = b then 1 else 0 :=
  unitQuaternion_inner a b

/-- In the same quaternion coordinates the parameter-doubled source curves
have precisely these angular velocities. -/
theorem unit_axis_quaternion_hasDerivAt_zero (a : Fin 3) :
    HasDerivAt (fun t : ℝ => ofMatrix (axisCurve a (2 * t) : Mat2)) (unitQuaternion a) 0 := by
  have h := ofMatrixLinear.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (unit_axis_matrix_hasDerivAt_zero a)
  change HasDerivAt (fun t : ℝ => ofMatrix (axisCurve a (2 * t) : Mat2))
    (ofMatrix (unitAxis a)) 0 at h
  rwa [← matrixMap_unitQuaternion, ofMatrix_matrixMap] at h

abbrev halfHilbertAxis := SourceCoefficientDifferentiation.hilbertAxis

def unitHilbertAxis (m : ℕ) (a : Fin 3) : Module.End ℂ (HilbertCarrier m) :=
  (2 : ℂ) • halfHilbertAxis m a

theorem axis_hilbert_hasDerivAt_zero (m : ℕ) (a : Fin 3) (v : HilbertCarrier m) :
    HasDerivAt (fun t : ℝ => unitaryAction m (axisCurve a t) v)
      (halfHilbertAxis m a v) 0 := by
  fin_cases a
  · exact x_axis_hilbert_hasDerivAt_zero m v
  · exact y_axis_hilbert_hasDerivAt_zero m v
  · exact z_axis_hilbert_hasDerivAt_zero m v

/-- The unit tangent parameters induce twice the existing represented generators. -/
theorem unit_axis_hilbert_hasDerivAt_zero (m : ℕ) (a : Fin 3) (v : HilbertCarrier m) :
    HasDerivAt (fun t : ℝ => unitaryAction m (axisCurve a (2 * t)) v)
      (unitHilbertAxis m a v) 0 := by
  have ht : HasDerivAt (fun t : ℝ => 2 * t) 2 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul 2
  simpa only [Function.comp_def, unitHilbertAxis, LinearMap.smul_apply, two_smul,
      LinearMap.add_apply] using!
    (axis_hilbert_hasDerivAt_zero m a v).scomp_of_eq 0 ht (by simp)

/-- The negative sum for the trace-orthonormal source axes has the original
Casimir normalization. This statement does not posit a global Laplacian. -/
theorem unit_axis_negative_square_sum (m : ℕ) :
    -(∑ a : Fin 3, unitHilbertAxis m a * unitHilbertAxis m a) = hilbertCasimir m := by
  calc
    _ = (-4 : ℂ) • (hilbertAxisOne m * hilbertAxisOne m +
        hilbertAxisTwo m * hilbertAxisTwo m + hilbertAxisThree m * hilbertAxisThree m) := by
      simp only [Fin.sum_univ_three, unitHilbertAxis, halfHilbertAxis,
        SourceCoefficientDifferentiation.hilbertAxis,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons,
        smul_mul_smul_comm]
      apply LinearMap.ext
      intro v
      simp only [LinearMap.neg_apply, LinearMap.add_apply, LinearMap.smul_apply]
      module
    _ = _ := by rw [hilbert_axis_casimir, hilbertCasimir_eq_scalar]

theorem unit_axis_negative_square_sum_eq_scalar (m : ℕ) :
    -(∑ a : Fin 3, unitHilbertAxis m a * unitHilbertAxis m a) =
      ((m : ℂ) * ((m : ℂ) + 2)) • (1 : Module.End ℂ (HilbertCarrier m)) := by
  rw [unit_axis_negative_square_sum, hilbertCasimir_eq_scalar]

/-- The derivative along right multiplication by the actual source curve
whose identity tangent has unit length in the original trace metric. -/
def unitAxisDerivative (a : Fin 3) (f : SU2 → ℂ) (g : SU2) : ℂ :=
  deriv (fun t : ℝ => f (g * axisCurve a (2 * t))) 0

/-- Invertible parameter scaling gives this identity for the derivative
operation itself; no representation degree enters the formula. -/
theorem unitAxisDerivative_eq (a : Fin 3) (f : SU2 → ℂ) :
    unitAxisDerivative a f = fun g =>
      (2 : ℂ) * SourceCoefficientDifferentiation.axisDerivative a f g := by
  funext g
  have h := deriv_comp_mul_left (2 : ℝ) (fun t => f (g * axisCurve a t)) (0 : ℝ)
  simpa only [unitAxisDerivative, SourceCoefficientDifferentiation.axisDerivative,
    mul_zero, two_smul, two_mul] using h

theorem unitAxisDerivative_twice_eq (a : Fin 3) (f : SU2 → ℂ) :
    unitAxisDerivative a (unitAxisDerivative a f) = fun g =>
      (4 : ℂ) * SourceCoefficientDifferentiation.axisDerivative a
        (SourceCoefficientDifferentiation.axisDerivative a f) g := by
  funext g
  simp only [unitAxisDerivative_eq, SourceCoefficientDifferentiation.axisDerivative_const_mul]
  ring

/-- The actual negative square sum of the trace-orthonormal source directions.
This pointwise operator is not a separately postulated spectral diagonal. -/
def roundCasimir (f : SU2 → ℂ) (g : SU2) : ℂ :=
  -(∑ a : Fin 3, unitAxisDerivative a (unitAxisDerivative a f) g)

/-- The already analysed pointwise source Casimir has exactly the original
trace metric scale, on the very same group functions and source curves. -/
theorem roundCasimir_eq_sourceCasimir (f : SU2 → ℂ) :
    roundCasimir f = SourceCoefficientDifferentiation.sourceCasimir f := by
  funext g
  simp only [roundCasimir, unitAxisDerivative_twice_eq,
    SourceCoefficientDifferentiation.sourceCasimir]
  rw [← Finset.mul_sum]
  ring

end GeneratedFoundations.Geometry.SourceAxisMetric
