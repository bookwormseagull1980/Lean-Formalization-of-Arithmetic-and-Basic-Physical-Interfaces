module

public import GeneratedFoundations.Geometry.SourceAxisMetric
public import GeneratedFoundations.Physical.SourceTTResponseNormalization
public import GeneratedFoundations.Operations.FiniteMatrixGaussianVariation
public import Mathlib.Tactic

/-!
# Tensor insertions in the generated first nonconstant scalar shell

The derivative matrices below are computed from commutators of the original
trace-unit source axes. They act on each real adjoint row of the degree-two
matrix coefficients; three such rows form the nine-dimensional scalar shell.
The comparison changes these gradient components, not a spacetime metric.

Both the first precision vertex and the direct second vertex are retained.
Their Gaussian means and covariances use the full matrix precision. The
result is a shell response for this frame comparison; identifying it with
another spectral readout requires the corresponding comparison identity.
-/

@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Operator
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace GeneratedFoundations.Physical.SourceTTFrameComparison

open Geometry.SourceAxisMetric Geometry.SourceAxisTT
open Operations.SourceSpinCorner Operations.SourceSpinCornerGroup
open Operations.FiniteMatrixGaussian SourceTTResponseNormalization

abbrev Mat := Matrix (Fin 3) (Fin 3) ℝ

/-- Coefficients of the differentiated adjoint action in the original
trace-orthonormal source frame. -/
def axisDerivative (a : Fin 3) : Mat := fun i j =>
  tracePair (unitAxis i) (unitAxis a * unitAxis j - unitAxis j * unitAxis a)

theorem axisDerivative_eq (a : Fin 3) : axisDerivative a =
    ![!![0, 0, 0; 0, 0, 2; 0, -2, 0],
      !![0, 0, -2; 0, 0, 0; 2, 0, 0],
      !![0, 2, 0; -2, 0, 0; 0, 0, 0]] a := by
  fin_cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [axisDerivative, tracePair, unitAxis, axisVelocity, spinMatrix,
      spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_two, Matrix.conjTranspose_apply] <;>
      ring_nf <;> norm_num

/-- This is the variation of the gradient quadratic form on the same
source coefficients. The two derivative indices are not collapsed. -/
def vertex (h : Mat) : Mat :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    h a b • ((axisDerivative a).transpose * axisDerivative b)

theorem vertex_formula (h : Mat) :
    vertex h = (4 : ℝ) • (Matrix.trace h • (1 : Mat) - h.transpose) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vertex, axisDerivative_eq, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.trace, Fin.sum_univ_three] <;> ring

theorem kinetic_operator : vertex (1 : Mat) = (8 : ℝ) • (1 : Mat) := by
  rw [vertex_formula]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.trace, Fin.sum_univ_three]

theorem tt_vertex (a b : ℝ) : vertex (ttMatrix a b) = (-4 : ℝ) • ttMatrix a b := by
  rw [vertex_formula, (ttMatrix_isAxisTT a b).1]
  have ht := (ttMatrix_isAxisTT a b).2.2
  rw [ht, zero_smul, zero_sub, smul_neg]
  module

/-- The mixed second gradient vertex for the affine frame path
`I + s*h/2 + t*k/2`. -/
def secondVertex (h k : Mat) : Mat :=
  vertex ((1 / 4 : ℝ) • (h.transpose * k + k.transpose * h))

theorem tt_second_trace (a b c d : ℝ) :
    Matrix.trace (secondVertex (ttMatrix a b) (ttMatrix c d)) =
      8 * (a * c + b * d) := by
  rw [secondVertex, vertex_formula]
  simp [ttMatrix, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    Fin.sum_univ_three]
  ring

def changedDerivative (R : Mat) (i : Fin 3) : Mat :=
  ∑ a : Fin 3, R i a • axisDerivative a

theorem vertex_gram (R : Mat) :
    vertex (R.transpose * R) =
      ∑ i : Fin 3, (changedDerivative R i).transpose * changedDerivative R i := by
  rw [vertex_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [changedDerivative, axisDerivative_eq, Matrix.mul_apply,
      Matrix.transpose_apply, Matrix.trace, Fin.sum_univ_three] <;> ring

theorem frame_precision_posDef {p : ℝ} (hp : 8 < p) (h : Mat) (t : ℝ) :
    (Matrix.diagonal (fun _ : Fin 3 => p - 8) +
      vertex (((1 : Mat) + (t / 2) • h).transpose *
        ((1 : Mat) + (t / 2) • h))).PosDef := by
  apply (Matrix.posDef_diagonal_iff.mpr (fun _ => by linarith :
    ∀ _ : Fin 3, 0 < p - 8)).add_posSemidef
  rw [vertex_gram]
  apply Matrix.posSemidef_sum
  intro i _
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.posSemidef_conjTranspose_mul_self
      (changedDerivative ((1 : Mat) + (t / 2) • h) i)

/-- The precision comes from applying the affine frame to the actual
gradient. Its zero-frame kinetic term is eight, as calculated above. -/
def comparisonPrecision (p : ℝ) (h : Mat) (t : ℝ) : Mat :=
  Matrix.diagonal (fun _ => p - 8) +
    vertex (((1 : Mat) + (t / 2) • h).transpose *
      ((1 : Mat) + (t / 2) • h))

theorem comparisonPrecision_expansion (p a b t : ℝ) :
    comparisonPrecision p (ttMatrix a b) t =
      Matrix.diagonal (fun _ => p) + t • vertex (ttMatrix a b) +
        (t ^ 2 / 2) • secondVertex (ttMatrix a b) (ttMatrix a b) := by
  simp only [comparisonPrecision, secondVertex, vertex_formula]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ttMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.trace, Fin.sum_univ_three] <;> ring

@[simp] theorem comparisonPrecision_zero (p a b : ℝ) :
    comparisonPrecision p (ttMatrix a b) 0 = Matrix.diagonal (fun _ => p) := by
  rw [comparisonPrecision_expansion]
  simp

def comparisonVertex (a b t : ℝ) : Mat :=
  vertex (ttMatrix a b) + t • secondVertex (ttMatrix a b) (ttMatrix a b)

theorem comparisonPrecision_hasDerivAt (p a b t : ℝ) :
    HasDerivAt (comparisonPrecision p (ttMatrix a b)) (comparisonVertex a b t) t := by
  have hd := ((hasDerivAt_const t (Matrix.diagonal (fun _ : Fin 3 => p))).add
    ((hasDerivAt_id t).smul_const (vertex (ttMatrix a b)))).add
      ((((hasDerivAt_id t).pow 2).div_const 2).smul_const
        (secondVertex (ttMatrix a b) (ttMatrix a b)))
  convert! hd using 1
  · funext s
    exact comparisonPrecision_expansion p a b s
  · simp only [comparisonVertex, id_eq, Nat.cast_ofNat]
    module

theorem comparisonVertex_hasDerivAt (a b t : ℝ) :
    HasDerivAt (comparisonVertex a b)
      (secondVertex (ttMatrix a b) (ttMatrix a b)) t := by
  simpa only [comparisonVertex, zero_add, one_smul] using!
    (hasDerivAt_const t (vertex (ttMatrix a b))).add
      ((hasDerivAt_id t).smul_const (secondVertex (ttMatrix a b) (ttMatrix a b)))

def precision (p : ℝ) : Mat := Matrix.diagonal (fun _ => p)

theorem precision_posDef {p : ℝ} (hp : 0 < p) : (precision p).PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun _ => hp)

theorem precision_inverse (p : ℝ) :
    (precision p)⁻¹ = Matrix.diagonal (fun _ => p⁻¹) := by
  by_cases hp : p = 0
  · simp [precision, hp]
  · apply Matrix.inv_eq_left_inv
    ext i j
    by_cases hij : i = j
    · subst j
      simp [precision, Matrix.mul_apply, Matrix.diagonal, hp]
    · simp [precision, Matrix.mul_apply, Matrix.diagonal, hij]

/-- The kinetic score covariance on one actual real adjoint row. -/
theorem row_covariance {p : ℝ} (hp : 0 < p) (a b c d : ℝ) :
    cov[score (vertex (ttMatrix a b)), score (vertex (ttMatrix c d));
      law (precision p)] = 16 / p ^ 2 * (a * c + b * d) := by
  have hs : (vertex (ttMatrix c d)).IsSymm := by
    rw [tt_vertex]
    change ((-4 : ℝ) • ttMatrix c d).transpose = (-4 : ℝ) • ttMatrix c d
    rw [Matrix.transpose_smul, (ttMatrix_isAxisTT c d).1]
  rw [score_covariance_trace (precision_posDef hp) _ _ hs,
    precision_inverse, tt_vertex, tt_vertex]
  simp [ttMatrix, Matrix.trace, Matrix.mul_apply, Matrix.diagonal,
    Fin.sum_univ_three]
  field_simp
  ring

/-- The direct term belongs to the same frame path and Gaussian law. -/
theorem row_direct {p : ℝ} (hp : 0 < p) (a b c d : ℝ) :
    (∫ x, score (secondVertex (ttMatrix a b) (ttMatrix c d)) x
      ∂law (precision p)) = 4 / p * (a * c + b * d) := by
  rw [score_mean_trace (precision_posDef hp), precision_inverse]
  simp only [secondVertex, vertex_formula]
  simp [ttMatrix, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.diagonal, Fin.sum_univ_three]
  field_simp
  ring

/-- Hessian of minus the logarithmic Gaussian partition, before any
independent direct comparison cost has been added. -/
def rowHessian (p a b c d : ℝ) : ℝ :=
  (∫ x, score (secondVertex (ttMatrix a b) (ttMatrix c d)) x
    ∂law (precision p)) -
  cov[score (vertex (ttMatrix a b)), score (vertex (ttMatrix c d));
    law (precision p)]

theorem rowHessian_eq {p : ℝ} (hp : 0 < p) (a b c d : ℝ) :
    rowHessian p a b c d = 4 * (p - 4) / p ^ 2 * (a * c + b * d) := by
  rw [rowHessian, row_direct hp, row_covariance hp]
  field_simp
  ring

theorem rowHessian_pos {p : ℝ} (hp : 8 < p) (a b : ℝ)
    (hab : a ≠ 0 ∨ b ≠ 0) : 0 < rowHessian p a b a b := by
  rw [rowHessian_eq (by linarith : 0 < p)]
  have hs : 0 < a * a + b * b := by
    rcases hab with ha | hb
    · nlinarith [sq_pos_of_ne_zero ha, sq_nonneg b]
    · nlinarith [sq_pos_of_ne_zero hb, sq_nonneg a]
  exact mul_pos (div_pos (by linarith) (sq_pos_of_pos (by linarith))) hs

/-- The calculated Hessian is the derivative of the actual quadratic
force in the varied original Gaussian, not a separately assigned form. -/
theorem original_frame_force_hasDerivAt {p : ℝ} (hp : 8 < p) (a b : ℝ) :
    HasDerivAt
      (fun t => ∫ x, score (comparisonVertex a b t) x
        ∂law (comparisonPrecision p (ttMatrix a b) t))
      (rowHessian p a b a b) 0 := by
  have hs : (comparisonVertex a b 0).IsSymm := by
    simp only [comparisonVertex, zero_smul, add_zero, tt_vertex]
    change ((-4 : ℝ) • ttMatrix a b).transpose = (-4 : ℝ) • ttMatrix a b
    rw [Matrix.transpose_smul, (ttMatrix_isAxisTT a b).1]
  have hd := varying_mean_hasDerivAt
    (comparisonPrecision p (ttMatrix a b)) (comparisonVertex a b) 0
    (comparisonVertex a b 0) (secondVertex (ttMatrix a b) (ttMatrix a b))
    (fun t => frame_precision_posDef hp _ t)
    (comparisonPrecision_hasDerivAt p a b 0) (comparisonVertex_hasDerivAt a b 0) hs
  simpa only [rowHessian, comparisonPrecision_zero, precision, comparisonVertex,
    zero_smul, add_zero] using hd

/-! ## Comparison with the scalar kinetic insertion -/

def repeatRows (M : Mat) : Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℝ :=
  Matrix.blockDiagonal (fun _ : Fin 3 => M)

theorem repeated_precision (p : ℝ) :
    repeatRows (precision p) = Matrix.diagonal (fun _ => p) := by
  ext i j
  rcases i with ⟨i, r⟩
  rcases j with ⟨j, s⟩
  by_cases hrs : r = s <;> by_cases hij : i = j <;>
    simp [repeatRows, precision, Matrix.blockDiagonal_apply,
      Matrix.diagonal, hrs, hij, Prod.ext_iff]

theorem repeated_inverse {p : ℝ} (hp : 0 < p) :
    (repeatRows (precision p))⁻¹ = repeatRows ((precision p)⁻¹) := by
  apply Matrix.inv_eq_left_inv
  simp only [repeatRows, ← Matrix.blockDiagonal_mul,
    inverse_mul_precision (precision_posDef hp)]
  exact Matrix.blockDiagonal_one

/-- The row factor is derived in the actual nine-coordinate Gaussian
law, including its full covariance, rather than attached to the readout. -/
theorem repeated_covariance {p : ℝ} (hp : 0 < p) (a b c d : ℝ) :
    cov[score (repeatRows (vertex (ttMatrix a b))),
      score (repeatRows (vertex (ttMatrix c d)));
      law (repeatRows (precision p))] =
        3 * cov[score (vertex (ttMatrix a b)), score (vertex (ttMatrix c d));
          law (precision p)] := by
  have hP : (repeatRows (precision p)).PosDef := by
    rw [repeated_precision]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => hp)
  have hs : (vertex (ttMatrix c d)).IsSymm := by
    change (vertex (ttMatrix c d)).transpose = vertex (ttMatrix c d)
    rw [tt_vertex, Matrix.transpose_smul, (ttMatrix_isAxisTT c d).1]
  have hrs : (repeatRows (vertex (ttMatrix c d))).IsSymm := by
    change (repeatRows (vertex (ttMatrix c d))).transpose = _
    change (Matrix.blockDiagonal (fun _ : Fin 3 => vertex (ttMatrix c d))).transpose = _
    rw [Matrix.blockDiagonal_transpose]
    congr 1
    funext i
    exact hs
  rw [score_covariance_trace hP _ _ hrs,
    score_covariance_trace (precision_posDef hp) _ _ hs,
    repeated_inverse hp]
  simp only [repeatRows, ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal,
    Fin.sum_univ_three]
  ring

/-- The same scalar precision occurs in the nine-dimensional shell. -/
def shellPrecision (omega m2 : ℝ) : ℝ := omega ^ 2 + 8 + m2

/-- Twice the covariance, with all three real matrix-coefficient rows
retained and one unit plus polarization. -/
def shellTensorResponse (omega m2 : ℝ) : ℝ :=
  3 * 2 * cov[score (vertex (ttMatrix 1 0)), score (vertex (ttMatrix 1 0));
    law (precision (shellPrecision omega m2))]

theorem shellTensorResponse_original_law {omega m2 : ℝ} (hm : 0 ≤ m2) :
    shellTensorResponse omega m2 =
      2 * cov[score (repeatRows (vertex (ttMatrix 1 0))),
        score (repeatRows (vertex (ttMatrix 1 0)));
        law (repeatRows (precision (shellPrecision omega m2)))] := by
  have hp : 0 < shellPrecision omega m2 := by
    unfold shellPrecision
    nlinarith [sq_nonneg omega]
  rw [repeated_covariance hp, shellTensorResponse]
  ring

theorem shellTensorResponse_eq {omega m2 : ℝ} (hm : 0 ≤ m2) :
    shellTensorResponse omega m2 = 96 / (omega ^ 2 + 8 + m2) ^ 2 := by
  have hp : 0 < shellPrecision omega m2 := by
    unfold shellPrecision
    nlinarith [sq_nonneg omega]
  rw [shellTensorResponse, row_covariance hp]
  simp only [mul_one, mul_zero, add_zero, shellPrecision]
  ring

/-- The source-gradient tensor score and the scalar kinetic score have
an exact, frequency-dependent conversion. No frequency is discarded. -/
theorem shell_response_conversion {omega m2 : ℝ} (hm : 0 ≤ m2) :
    shellTensorResponse omega m2 =
      (32 / (3 * (omega ^ 2 + 8) ^ 2)) *
        (9 * SourceTensorResponseEndpoint.ttKernel (omega ^ 2 + 8) m2) := by
  rw [shellTensorResponse_eq hm]
  unfold SourceTensorResponseEndpoint.ttKernel
  have hq : omega ^ 2 + 8 ≠ 0 := by nlinarith [sq_nonneg omega]
  field_simp
  ring

/-- Even within one fixed shell, one constant rescaling cannot identify
these two source comparisons on an entire frequency interval. -/
theorem no_common_shell_conversion {m2 beta : ℝ} (hm : 0 ≤ m2) :
    ¬ (shellTensorResponse 0 m2 =
        beta * (9 * SourceTensorResponseEndpoint.ttKernel 8 m2) ∧
      shellTensorResponse 1 m2 =
        beta * (9 * SourceTensorResponseEndpoint.ttKernel 9 m2)) := by
  rintro ⟨hzero, hone⟩
  rw [shellTensorResponse_eq hm] at hzero hone
  norm_num [SourceTensorResponseEndpoint.ttKernel] at hzero hone
  have hp : 0 < 8 + m2 := by linarith
  have hq : 0 < 9 + m2 := by linarith
  field_simp [hp.ne'] at hzero
  field_simp [hq.ne'] at hone
  nlinarith

/-- All three rows contribute to the direct second-vertex response as
well as to the connected fluctuation. -/
theorem shell_complete_hessian {omega m2 : ℝ} (hm : 0 ≤ m2) :
    3 * rowHessian (shellPrecision omega m2) 1 0 1 0 =
      12 * (omega ^ 2 + 4 + m2) / (omega ^ 2 + 8 + m2) ^ 2 := by
  have hp : 0 < shellPrecision omega m2 := by
    unfold shellPrecision
    nlinarith [sq_nonneg omega]
  rw [rowHessian_eq hp]
  simp only [mul_one, mul_zero, add_zero, shellPrecision]
  ring

end GeneratedFoundations.Physical.SourceTTFrameComparison
