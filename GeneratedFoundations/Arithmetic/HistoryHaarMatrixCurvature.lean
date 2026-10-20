module

public import GeneratedFoundations.Arithmetic.HistoryCliffordAction
public import GeneratedFoundations.Geometry.SourceOneFormContinuousCore
public import GeneratedFoundations.Geometry.HilbertTraceVariation

/-!
# Nonlinear matrix curvature on the actual source Haar field

Every matrix coefficient on the complete generated history--phase/source
carrier is a member of the original differentiated one-form core. Its
continuous representative supplies the pointwise products; its inclusion
and curl are those of the original Haar Hilbert space. The nonlinearity is
the actual matrix commutator, with every matrix entry and both cross terms
retained. The action Hessian at zero is derived from that nonlinearity and
identified with two applications of the original curl.

The root index is an observation cutoff. It is not a colour multiplicity
or a new source parameter. The lower bound concerns the coclosed source
field with all history matrix coefficients; it does not assert the same
bound for the distinct arithmetic generation/reaction operator.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarMatrixCurvature

open Geometry.SourceSpinCentre Geometry.SourceOneFormHaarBlock
open Geometry.SourceOneFormCurlSpectrum Geometry.SourceOneFormClosedHodge
open Geometry.SourceOneFormHodgeLaplacian Geometry.SourceOneFormContinuousCore

abbrev Index (N : ℕ) := HistoryCliffordAction.Index N
abbrev Coefficients (N : ℕ) := Matrix (Index N) (Index N) Core
abbrev Fields (N : ℕ) := PiLp 2 (fun _ : Index N × Index N => OneFormL2)
abbrev ContinuousMatrix (N : ℕ) := Matrix (Index N) (Index N) C(CentralQuotient, ℂ)

def field (N : ℕ) : Coefficients N →ₗ[ℂ] Fields N where
  toFun A := WithLp.toLp 2 fun i => includeCore (A i.1 i.2)
  map_add' A B := by
    apply (WithLp.equiv 2 (Index N × Index N → OneFormL2)).injective
    funext i
    exact map_add includeCore _ _
  map_smul' z A := by
    apply (WithLp.equiv 2 (Index N × Index N → OneFormL2)).injective
    funext i
    exact map_smul includeCore z _

def differentiated (N : ℕ) : Coefficients N →ₗ[ℂ] Fields N where
  toFun A := WithLp.toLp 2 fun i => includeCore (coreCurl (A i.1 i.2))
  map_add' A B := by
    apply (WithLp.equiv 2 (Index N × Index N → OneFormL2)).injective
    funext i
    change includeCore (coreCurl (A i.1 i.2 + B i.1 i.2)) = _
    simp only [map_add]
    rfl
  map_smul' z A := by
    apply (WithLp.equiv 2 (Index N × Index N → OneFormL2)).injective
    funext i
    change includeCore (coreCurl (z • A i.1 i.2)) = z • _
    rw [map_smul, map_smul]
    rfl

theorem differentiated_component (N : ℕ) (A : Coefficients N) (i j : Index N) :
    differentiated N A (i, j) = closedCurl (coreToCurlDomain (A i j)) :=
  (coreCurl_is_differential (A i j)).symm

def matrixRepresentative (N : ℕ) (A : Coefficients N) (j : Fin 3) : ContinuousMatrix N :=
  fun a b => representative (A a b) j

theorem matrixRepresentative_smul (N : ℕ) (t : ℂ) (A : Coefficients N) (j : Fin 3) :
    matrixRepresentative N (t • A) j = t • matrixRepresentative N A j := by
  ext a b x
  simp only [matrixRepresentative, Matrix.smul_apply, map_smul, Pi.smul_apply,
    ContinuousMap.smul_apply]

def commutator (N : ℕ) (X Y : ContinuousMatrix N) : ContinuousMatrix N := X * Y - Y * X

theorem commutator_smul (N : ℕ) (t : ℂ) (X Y : ContinuousMatrix N) :
    commutator N (t • X) (t • Y) = (t * t) • commutator N X Y := by
  simp only [commutator, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub]

def vertexRepresentative (N : ℕ) (A : Coefficients N) (a b : Index N) : ContinuousField :=
  ![commutator N (matrixRepresentative N A 1) (matrixRepresentative N A 2) a b,
    commutator N (matrixRepresentative N A 2) (matrixRepresentative N A 0) a b,
    commutator N (matrixRepresentative N A 0) (matrixRepresentative N A 1) a b]

def vertex (N : ℕ) (A : Coefficients N) : Fields N :=
  WithLp.toLp 2 fun i => toHaar (vertexRepresentative N A i.1 i.2)

theorem vertex_smul (N : ℕ) (t : ℂ) (A : Coefficients N) :
    vertex N (t • A) = (t * t) • vertex N A := by
  have h (a b : Index N) : vertexRepresentative N (t • A) a b =
      (t * t) • vertexRepresentative N A a b := by
    funext j
    fin_cases j <;>
      simp [vertexRepresentative, matrixRepresentative_smul, commutator_smul,
        Matrix.smul_apply, Pi.smul_apply]
  apply (WithLp.equiv 2 (Index N × Index N → OneFormL2)).injective
  funext i
  change toHaar (vertexRepresentative N (t • A) i.1 i.2) =
    (t * t) • toHaar (vertexRepresentative N A i.1 i.2)
  rw [h, map_smul]

def curvature (N : ℕ) (A : Coefficients N) : Fields N := differentiated N A + vertex N A

theorem curvature_ray (N : ℕ) (t : ℝ) (A : Coefficients N) :
    curvature N ((t : ℂ) • A) = (t : ℂ) • differentiated N A +
      ((t ^ 2 : ℝ) : ℂ) • vertex N A := by
  rw [curvature, map_smul, vertex_smul]
  simp only [pow_two, Complex.ofReal_mul]

def action (N : ℕ) (A : Coefficients N) : ℝ := ‖curvature N A‖ ^ 2 / 2

theorem action_nonneg (N : ℕ) (A : Coefficients N) : 0 ≤ action N A := by
  exact div_nonneg (sq_nonneg _) (by norm_num)

theorem action_ray (N : ℕ) (t : ℝ) (A : Coefficients N) :
    action N ((t : ℂ) • A) =
      t ^ 2 * ‖differentiated N A‖ ^ 2 / 2 +
      t ^ 3 * (inner ℂ (differentiated N A) (vertex N A)).re +
      t ^ 4 * ‖vertex N A‖ ^ 2 / 2 := by
  rw [action, curvature_ray, norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.re_eq_complex_re, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ), Complex.conj_ofReal,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

def rayDerivative (N : ℕ) (A : Coefficients N) (t : ℝ) : ℝ :=
  t * ‖differentiated N A‖ ^ 2 +
    3 * t ^ 2 * (inner ℂ (differentiated N A) (vertex N A)).re +
    2 * t ^ 3 * ‖vertex N A‖ ^ 2

theorem action_hasDerivAt (N : ℕ) (A : Coefficients N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N ((s : ℂ) • A)) (rayDerivative N A t) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0 0
    (‖differentiated N A‖ ^ 2 / 2)
    (inner ℂ (differentiated N A) (vertex N A)).re (‖vertex N A‖ ^ 2 / 2) t using 1
  · funext s
    rw [action_ray]
    ring
  · unfold rayDerivative
    ring

theorem secondDeriv_zero (N : ℕ) (A : Coefficients N) :
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => action N ((s : ℂ) • A)) t)
      (‖differentiated N A‖ ^ 2) 0 := by
  have he : (fun t : ℝ => deriv (fun s : ℝ => action N ((s : ℂ) • A)) t) =
      rayDerivative N A := funext fun t => (action_hasDerivAt N A t).deriv
  rw [he]
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0
    (‖differentiated N A‖ ^ 2)
    (3 * (inner ℂ (differentiated N A) (vertex N A)).re)
    (2 * ‖vertex N A‖ ^ 2) 0 0 using 1
  · funext t
    unfold rayDerivative
    ring
  · simp

theorem field_normSq (N : ℕ) (A : Coefficients N) :
    ‖field N A‖ ^ 2 = ∑ i : Index N × Index N, ‖(A i.1 i.2 : coclosedField)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem differentiated_normSq (N : ℕ) (A : Coefficients N) :
    ‖differentiated N A‖ ^ 2 =
      ∑ i : Index N × Index N, ‖(coreCurl (A i.1 i.2) : coclosedField)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  rfl

theorem hessian_coercive (N : ℕ) (A : Coefficients N) :
    4 * ‖field N A‖ ^ 2 ≤ ‖differentiated N A‖ ^ 2 := by
  rw [field_normSq, differentiated_normSq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hm : (coreToCurlDomain (A i.1 i.2) : OneFormL2) ∈ coclosedField := by
    rw [coreToCurlDomain_val]
    exact (A i.1 i.2).val.property
  have h := closedCurl_coclosed_coercivity (coreToCurlDomain (A i.1 i.2)) hm
  rw [coreToCurlDomain_val, coreCurl_is_differential] at h
  exact h

theorem hessian_differential (N : ℕ) (A : Coefficients N) :
    ‖differentiated N A‖ ^ 2 =
      ∑ i : Index N × Index N,
        (inner ℂ (A i.1 i.2 : coclosedField) (finiteHodge (A i.1 i.2))).re := by
  rw [differentiated_normSq]
  exact Finset.sum_congr rfl fun _ _ => (Geometry.SourceOneFormHodgeEnergy.finiteHodge_energy _).symm

structure Conclusions : Prop where
  actual_differential : ∀ N (A : Coefficients N) i j,
    differentiated N A (i, j) = closedCurl (coreToCurlDomain (A i j))
  actual_nonlinearity : ∀ N (t : ℝ) (A : Coefficients N),
    curvature N ((t : ℂ) • A) = (t : ℂ) • differentiated N A +
      ((t ^ 2 : ℝ) : ℂ) • vertex N A
  nonlinear_derivative : ∀ N (A : Coefficients N) t,
    HasDerivAt (fun s : ℝ => action N ((s : ℂ) • A)) (rayDerivative N A t) t
  actual_hessian : ∀ N (A : Coefficients N),
    HasDerivAt (fun t : ℝ => deriv (fun s : ℝ => action N ((s : ℂ) • A)) t)
      (‖differentiated N A‖ ^ 2) 0
  differential_hessian : ∀ N (A : Coefficients N),
    ‖differentiated N A‖ ^ 2 = ∑ i : Index N × Index N,
      (inner ℂ (A i.1 i.2 : coclosedField) (finiteHodge (A i.1 i.2))).re
  cutoff_independent_bound : ∀ N (A : Coefficients N),
    4 * ‖field N A‖ ^ 2 ≤ ‖differentiated N A‖ ^ 2

theorem generated : Conclusions where
  actual_differential := differentiated_component
  actual_nonlinearity := curvature_ray
  nonlinear_derivative := action_hasDerivAt
  actual_hessian := secondDeriv_zero
  differential_hessian := hessian_differential
  cutoff_independent_bound := hessian_coercive

end GeneratedFoundations.Arithmetic.HistoryHaarMatrixCurvature
