module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionWindow
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Connection vertices of the original history section action

The connection acts on the original position-dependent sections, before
Haar inclusion and without projecting its products back into a finite
core. Differentiating the covariant kinetic square gives both ordered
current terms and a direct second variation. The same identities hold
between distinct sections, and therefore determine full matrices rather
than only their diagonals.

The finite matrices below are restrictions to actual source eigenvectors.
Their cutoff is the original kinetic cutoff at the given frequency.
Neither a response normalization nor an endpoint selection is inserted.
-/

@[expose] public section
noncomputable section
open scoped BigOperators ComplexConjugate ComplexOrder

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionVariation

open HistoryHaarMatrixCurvature (Coefficients)
open HistoryHaarSectionAction
open Geometry.SourceOneFormContinuousCore (toHaar)

private theorem self_inner_re {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (x : E) : (inner ℂ x x).re = ‖x‖ ^ 2 := by
  simpa only [RCLike.re_eq_complex_re] using inner_self_eq_norm_sq (𝕜 := ℂ) x

theorem connectionRepresentative_add_left (N : ℕ) (A B : Coefficients N)
    (ψ : Sections N) (i : HistoryHaarMatrixCurvature.Index N) :
    connectionRepresentative N (A + B) ψ i =
      connectionRepresentative N A ψ i + connectionRepresentative N B ψ i := by
  funext j
  ext x
  simp [connectionRepresentative, Matrix.add_apply, map_add, Pi.add_apply,
    add_mul, Finset.sum_add_distrib]

theorem connectionRepresentative_add_right (N : ℕ) (A : Coefficients N)
    (ψ ξ : Sections N) (i : HistoryHaarMatrixCurvature.Index N) :
    connectionRepresentative N A (ψ + ξ) i =
      connectionRepresentative N A ψ i + connectionRepresentative N A ξ i := by
  funext j
  ext x
  simp only [connectionRepresentative, Pi.add_apply, map_add,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply,
    mul_add, Finset.sum_add_distrib]

theorem connectionDerivative_add_left (N : ℕ) (A B : Coefficients N)
    (ψ : Sections N) :
    connectionDerivative N (A + B) ψ =
      connectionDerivative N A ψ + connectionDerivative N B ψ := by
  apply (WithLp.equiv 2 (HistoryHaarMatrixCurvature.Index N →
    Geometry.SourceOneFormHaarBlock.OneFormL2)).injective
  funext i
  change toHaar (connectionRepresentative N (A + B) ψ i) =
    toHaar (connectionRepresentative N A ψ i) + toHaar (connectionRepresentative N B ψ i)
  rw [connectionRepresentative_add_left, map_add]

theorem connectionDerivative_add_right (N : ℕ) (A : Coefficients N)
    (ψ ξ : Sections N) :
    connectionDerivative N A (ψ + ξ) =
      connectionDerivative N A ψ + connectionDerivative N A ξ := by
  apply (WithLp.equiv 2 (HistoryHaarMatrixCurvature.Index N →
    Geometry.SourceOneFormHaarBlock.OneFormL2)).injective
  funext i
  change toHaar (connectionRepresentative N A (ψ + ξ) i) =
    toHaar (connectionRepresentative N A ψ i) + toHaar (connectionRepresentative N A ξ i)
  rw [connectionRepresentative_add_right, map_add]

def connectionLinear (N : ℕ) (A : Coefficients N) :
    Sections N →ₗ[ℂ] DerivativeFields N where
  toFun := connectionDerivative N A
  map_add' := connectionDerivative_add_right N A
  map_smul' z ψ := by
    simpa using connectionDerivative_smul N 1 z A ψ

def covariantLinear (N : ℕ) (A : Coefficients N) :
    Sections N →ₗ[ℂ] DerivativeFields N := gradient N + connectionLinear N A

@[simp] theorem covariantLinear_apply (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    covariantLinear N A ψ = covariantDerivative N A ψ := rfl

theorem covariantDerivative_connection_ray (N : ℕ) (A B : Coefficients N)
    (ψ : Sections N) (t : ℝ) :
    covariantDerivative N (A + (t : ℂ) • B) ψ =
      covariantDerivative N A ψ + (t : ℂ) • connectionDerivative N B ψ := by
  have h := connectionDerivative_smul N (t : ℂ) 1 B ψ
  simp only [one_smul, mul_one] at h
  rw [covariantDerivative, connectionDerivative_add_left, h]
  simp only [covariantDerivative, add_assoc]

/-- The two ordered terms of the actual first precision vertex. -/
def firstVertex (N : ℕ) (A B : Coefficients N) (ψ ξ : Sections N) : ℂ :=
  inner ℂ (covariantDerivative N A ψ) (connectionDerivative N B ξ) +
    inner ℂ (connectionDerivative N B ψ) (covariantDerivative N A ξ)

/-- The mixed direct second variation is not a covariance term. -/
def secondVertex (N : ℕ) (B C : Coefficients N) (ψ ξ : Sections N) : ℂ :=
  inner ℂ (connectionDerivative N B ψ) (connectionDerivative N C ξ) +
    inner ℂ (connectionDerivative N C ψ) (connectionDerivative N B ξ)

def precisionForm (N : ℕ) (A : Coefficients N) (ψ ξ : Sections N) : ℂ :=
  inner ℂ (covariantDerivative N A ψ) (covariantDerivative N A ξ) +
    (HistoryDefiningResponse.coefficient N : ℂ) *
      inner ℂ (sectionField N ψ) (sectionField N ξ)

theorem precisionForm_hermitian (N : ℕ) (A : Coefficients N) (ψ ξ : Sections N) :
    conj (precisionForm N A ξ ψ) = precisionForm N A ψ ξ := by
  simp only [precisionForm, map_add, map_mul, Complex.conj_ofReal, inner_conj_symm]

theorem firstVertex_hermitian (N : ℕ) (A B : Coefficients N) (ψ ξ : Sections N) :
    conj (firstVertex N A B ξ ψ) = firstVertex N A B ψ ξ := by
  simp only [firstVertex, map_add, inner_conj_symm]
  exact add_comm _ _

theorem secondVertex_hermitian (N : ℕ) (B C : Coefficients N) (ψ ξ : Sections N) :
    conj (secondVertex N B C ξ ψ) = secondVertex N B C ψ ξ := by
  simp only [secondVertex, map_add, inner_conj_symm]
  exact add_comm _ _

/-- Exact finite-parameter identity for every pair of original sections. -/
theorem precisionForm_connection_ray (N : ℕ) (A B : Coefficients N)
    (ψ ξ : Sections N) (t : ℝ) :
    precisionForm N (A + (t : ℂ) • B) ψ ξ =
      precisionForm N A ψ ξ + (t : ℂ) * firstVertex N A B ψ ξ +
        ((t ^ 2 : ℝ) : ℂ) *
          inner ℂ (connectionDerivative N B ψ) (connectionDerivative N B ξ) := by
  simp only [precisionForm, covariantDerivative_connection_ray,
    inner_add_left, inner_add_right, inner_smul_left (𝕜 := ℂ),
    inner_smul_right (𝕜 := ℂ), Complex.conj_ofReal, firstVertex, Complex.ofReal_pow]
  ring

theorem firstVertex_connection_ray (N : ℕ) (A B C : Coefficients N)
    (ψ ξ : Sections N) (t : ℝ) :
    firstVertex N (A + (t : ℂ) • C) B ψ ξ =
      firstVertex N A B ψ ξ + (t : ℂ) * secondVertex N B C ψ ξ := by
  simp only [firstVertex, covariantDerivative_connection_ray,
    inner_add_left, inner_add_right, inner_smul_left (𝕜 := ℂ),
    inner_smul_right (𝕜 := ℂ), Complex.conj_ofReal, secondVertex]
  ring

/-- The mixed channel derivative is obtained from the same current.
No assertion that two different channels have zero overlap is made. -/
theorem firstVertex_hasDerivAt (N : ℕ) (A B C : Coefficients N)
    (ψ ξ : Sections N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (firstVertex N (A + (s : ℂ) • C) B ψ ξ).re / 2)
      ((secondVertex N B C ψ ξ).re / 2) t := by
  have h : (fun s : ℝ => (firstVertex N (A + (s : ℂ) • C) B ψ ξ).re / 2) =
      fun s => (firstVertex N A B ψ ξ).re / 2 + s * (secondVertex N B C ψ ξ).re / 2 := by
    funext s
    rw [firstVertex_connection_ray]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [h]
  convert (((hasDerivAt_id t).mul_const (secondVertex N B C ψ ξ).re).div_const 2).const_add
    ((firstVertex N A B ψ ξ).re / 2) using 1 <;> simp

theorem secondVertex_diagonal (N : ℕ) (B : Coefficients N) (ψ : Sections N) :
    (secondVertex N B B ψ ψ).re = 2 * ‖connectionDerivative N B ψ‖ ^ 2 := by
  simp only [secondVertex, Complex.add_re, self_inner_re]
  ring

def sectionAction (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  (precisionForm N A ψ ψ).re / 2

theorem sectionAction_eq (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    sectionAction N A ψ = ‖covariantDerivative N A ψ‖ ^ 2 / 2 +
      HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2 / 2 := by
  simp only [sectionAction, precisionForm, Complex.add_re, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, self_inner_re]
  ring

/-- The varied quadratic form is the section part of the original action. -/
theorem original_action_eq (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    HistoryHaarSectionAction.action N A ψ =
      HistoryHaarMatrixCurvature.action N A + sectionAction N A ψ := by
  rw [sectionAction_eq, HistoryHaarSectionAction.action]
  ring

theorem sectionAction_connection_ray (N : ℕ) (A B : Coefficients N)
    (ψ : Sections N) (t : ℝ) :
    sectionAction N (A + (t : ℂ) • B) ψ = sectionAction N A ψ +
      t * (firstVertex N A B ψ ψ).re / 2 +
        t ^ 2 * ‖connectionDerivative N B ψ‖ ^ 2 / 2 := by
  rw [sectionAction, precisionForm_connection_ray]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, self_inner_re]
  unfold sectionAction
  ring

theorem sectionAction_hasDerivAt (N : ℕ) (A B : Coefficients N)
    (ψ : Sections N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => sectionAction N (A + (s : ℂ) • B) ψ)
      ((firstVertex N A B ψ ψ).re / 2 +
        t * ‖connectionDerivative N B ψ‖ ^ 2) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt (sectionAction N A ψ)
    ((firstVertex N A B ψ ψ).re / 2)
    (‖connectionDerivative N B ψ‖ ^ 2 / 2) 0 0 t using 1
  · funext s
    rw [sectionAction_connection_ray]
    ring
  · ring

theorem sectionAction_secondDeriv (N : ℕ) (A B : Coefficients N)
    (ψ : Sections N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => deriv
      (fun r : ℝ => sectionAction N (A + (r : ℂ) • B) ψ) s)
      (‖connectionDerivative N B ψ‖ ^ 2) t := by
  have h : (fun s : ℝ => deriv
      (fun r : ℝ => sectionAction N (A + (r : ℂ) • B) ψ) s) =
      fun s => (firstVertex N A B ψ ψ).re / 2 +
        s * ‖connectionDerivative N B ψ‖ ^ 2 :=
    funext fun s => (sectionAction_hasDerivAt N A B ψ s).deriv
  rw [h]
  simpa using ((hasDerivAt_id t).mul_const
    (‖connectionDerivative N B ψ‖ ^ 2)).const_add ((firstVertex N A B ψ ψ).re / 2)

theorem firstVertex_at_zero (N : ℕ) (B : Coefficients N) (ψ : Sections N) :
    (firstVertex N 0 B ψ ψ).re / 2 = sectionCurrent N B ψ := by
  have hz : connectionDerivative N 0 ψ = 0 := by
    have h := connectionDerivative_smul N 0 1 B ψ
    simpa using h
  simp only [firstVertex, covariantDerivative, hz, add_zero, Complex.add_re, sectionCurrent]
  have hs : (inner ℂ (connectionDerivative N B ψ) (gradient N ψ)).re =
      (inner ℂ (gradient N ψ) (connectionDerivative N B ψ)).re := by
    simpa only [RCLike.re_eq_complex_re] using
      inner_re_symm (𝕜 := ℂ) (connectionDerivative N B ψ) (gradient N ψ)
  rw [hs]
  ring

/-- The scalar restriction is exactly the scalar part of the existing
joint frequency cutoff. -/
def scalarSupport (N : ℕ) (B u : ℝ) : Finset (HistoryHaarSectionHessian.Index N) := by
  classical
  exact ((Finset.univ : Finset (HistoryHaarSectionHessian.Label N)) ×ˢ
    HistoryHaarSectionWindow.scalarCandidates
      (HistorySpectralWindow.enumerationBound (B - u ^ 2))).filter
        fun a => u ^ 2 + Geometry.SourceCasimirClosure.energy a.2.val.1 < B

theorem mem_scalarSupport (N : ℕ) (B u : ℝ)
    (a : HistoryHaarSectionHessian.Index N) :
    a ∈ scalarSupport N B u ↔
      Sum.inr a ∈ HistoryHaarSectionWindow.support N (B - u ^ 2) := by
  classical
  rw [scalarSupport, Finset.mem_filter, HistoryHaarSectionWindow.mem_support]
  constructor
  · rintro ⟨_, h⟩
    change Geometry.SourceCasimirClosure.energy a.2.val.1 < B - u ^ 2
    linarith
  · intro h
    change Geometry.SourceCasimirClosure.energy a.2.val.1 < B - u ^ 2 at h
    have hc := HistoryHaarSectionWindow.cutoff_mem_candidates N (B - u ^ 2)
      (Sum.inr a) h
    refine ⟨?_, by linarith⟩
    simpa [HistoryHaarSectionWindow.candidates] using hc

abbrev WindowIndex (N : ℕ) (B u : ℝ) := ↥(scalarSupport N B u)

def windowSection (N : ℕ) (B u : ℝ) (i : WindowIndex N B u) : Sections N :=
  basisSection N i.val.1 i.val.2

def precisionMatrix (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ := fun i j =>
  precisionForm N A (windowSection N B u i) (windowSection N B u j) +
    ((u ^ 2 : ℝ) : ℂ) * inner ℂ (sectionField N (windowSection N B u i))
      (sectionField N (windowSection N B u j))

def firstMatrix (N : ℕ) (B u : ℝ) (A X : Coefficients N) :
    Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ := fun i j =>
  firstVertex N A X (windowSection N B u i) (windowSection N B u j)

def directMatrix (N : ℕ) (B u : ℝ) (X : Coefficients N) :
    Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ := fun i j =>
  inner ℂ (connectionDerivative N X (windowSection N B u i))
    (connectionDerivative N X (windowSection N B u j))

/-- Every matrix entry, including all off-diagonal entries, is retained. -/
theorem precisionMatrix_connection_ray (N : ℕ) (B u : ℝ)
    (A X : Coefficients N) (t : ℝ) :
    precisionMatrix N B u (A + (t : ℂ) • X) = precisionMatrix N B u A +
      (t : ℂ) • firstMatrix N B u A X +
        ((t ^ 2 : ℝ) : ℂ) • directMatrix N B u X := by
  ext i j
  simp only [precisionMatrix, precisionForm_connection_ray, Matrix.add_apply,
    Matrix.smul_apply, smul_eq_mul, firstMatrix, directMatrix]
  ring

theorem windowSection_field (N : ℕ) (B u : ℝ) (i : WindowIndex N B u) :
    sectionField N (windowSection N B u i) = HistoryHaarSectionHessian.vector N i.val := by
  rw [windowSection, sectionField_basisSection]
  rw [Geometry.SourceScalarResolution.includeScalar_basis]
  rfl

theorem windowSection_gram (N : ℕ) (B u : ℝ) :
    Matrix.gram ℂ (fun i : WindowIndex N B u => sectionField N (windowSection N B u i)) = 1 := by
  classical
  ext i j
  rw [Matrix.gram_apply, windowSection_field, windowSection_field]
  have h := orthonormal_iff_ite.mp (HistoryHaarSectionHessian.vector_orthonormal N) i.val j.val
  simpa only [Matrix.one_apply, Subtype.val_inj] using h

/-- Exact Gram representation; no nonlinear product is projected back into
the observation window when this matrix is formed. -/
theorem precisionMatrix_gram (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    precisionMatrix N B u A =
      Matrix.gram ℂ (fun i : WindowIndex N B u => covariantDerivative N A (windowSection N B u i)) +
        (HistoryDefiningResponse.coefficient N + u ^ 2) •
          (1 : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ) := by
  classical
  ext i j
  have hg := congrArg (fun M : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ => M i j)
    (windowSection_gram N B u)
  simp only [Matrix.gram_apply] at hg
  simp only [precisionMatrix, precisionForm, hg, Matrix.add_apply, Matrix.gram_apply,
    Matrix.smul_apply, Complex.real_smul, Complex.ofReal_add]
  ring

/-- The original restoring term gives positive precision at every actual
connection, including non-diagonal deformations of its vacuum eigenbasis. -/
theorem precisionMatrix_posDef (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    (precisionMatrix N B u A).PosDef := by
  classical
  rw [precisionMatrix_gram]
  exact Matrix.PosDef.posSemidef_add (Matrix.posSemidef_gram ℂ _)
    (Matrix.PosDef.one.smul (add_pos_of_pos_of_nonneg
      (HistoryDefiningResponse.coefficient_pos N) (sq_nonneg u)))

/-- The same restoring lower bound survives the entire connection
deformation, uniformly in the cutoff and history stage. -/
theorem precisionMatrix_uniform_lower (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    (precisionMatrix N B u A - ((15 / 8 : ℝ) + u ^ 2) •
      (1 : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ)).PosSemidef := by
  classical
  rw [precisionMatrix_gram, add_sub_assoc, ← sub_smul]
  have he : HistoryDefiningResponse.coefficient N + u ^ 2 - ((15 / 8 : ℝ) + u ^ 2) =
      HistoryDefiningResponse.coefficient N - 15 / 8 := by ring
  rw [he]
  exact (Matrix.posSemidef_gram ℂ _).add
    (Matrix.PosSemidef.one.smul (sub_nonneg.mpr (HistoryDefiningResponse.coefficient_lower N)))

def inversePrecision (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ := (precisionMatrix N B u A)⁻¹

theorem precision_mul_inverse (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    precisionMatrix N B u A * inversePrecision N B u A = 1 := by
  classical
  exact Matrix.mul_nonsing_inv _
    ((precisionMatrix N B u A).isUnit_iff_isUnit_det.mp (precisionMatrix_posDef N B u A).isUnit)

theorem inverse_mul_precision (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    inversePrecision N B u A * precisionMatrix N B u A = 1 := by
  classical
  exact Matrix.nonsing_inv_mul _
    ((precisionMatrix N B u A).isUnit_iff_isUnit_det.mp (precisionMatrix_posDef N B u A).isUnit)

theorem inversePrecision_posDef (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    (inversePrecision N B u A).PosDef := (precisionMatrix_posDef N B u A).inv

/-- The inverse response retains the complete finite-connection change.
There is no entrywise absolute-value estimate in this identity. -/
theorem inversePrecision_difference (N : ℕ) (B u : ℝ) (A X : Coefficients N) :
    inversePrecision N B u X - inversePrecision N B u A =
      inversePrecision N B u X *
        (precisionMatrix N B u A - precisionMatrix N B u X) * inversePrecision N B u A := by
  classical
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
    precision_mul_inverse, Matrix.mul_one, inverse_mul_precision, Matrix.one_mul]

/-- Uniqueness is among all matrices; no diagonal or commuting ansatz is
imposed on the candidate inverse response. -/
theorem inversePrecision_existsUnique (N : ℕ) (B u : ℝ) (A : Coefficients N) :
    ∃! C : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ,
      precisionMatrix N B u A * C = 1 := by
  classical
  refine ⟨inversePrecision N B u A, precision_mul_inverse N B u A, ?_⟩
  intro C hC
  calc
    C = (inversePrecision N B u A * precisionMatrix N B u A) * C := by
      rw [inverse_mul_precision, Matrix.one_mul]
    _ = inversePrecision N B u A := by rw [Matrix.mul_assoc, hC, Matrix.mul_one]

structure Conclusions : Prop where
  original_action : ∀ N A ψ,
    HistoryHaarSectionAction.action N A ψ =
      HistoryHaarMatrixCurvature.action N A + sectionAction N A ψ
  full_precision_vertex : ∀ N A B ψ ξ (t : ℝ),
    precisionForm N (A + (t : ℂ) • B) ψ ξ = precisionForm N A ψ ξ +
      (t : ℂ) * firstVertex N A B ψ ξ + ((t ^ 2 : ℝ) : ℂ) *
        inner ℂ (connectionDerivative N B ψ) (connectionDerivative N B ξ)
  actual_first_derivative : ∀ N A B ψ t,
    HasDerivAt (fun s : ℝ => sectionAction N (A + (s : ℂ) • B) ψ)
      ((firstVertex N A B ψ ψ).re / 2 + t * ‖connectionDerivative N B ψ‖ ^ 2) t
  actual_direct_second_derivative : ∀ N A B ψ t,
    HasDerivAt (fun s : ℝ => deriv
      (fun r : ℝ => sectionAction N (A + (r : ℂ) • B) ψ) s)
      (‖connectionDerivative N B ψ‖ ^ 2) t
  original_current : ∀ N B ψ,
    (firstVertex N 0 B ψ ψ).re / 2 = sectionCurrent N B ψ
  actual_scalar_cutoff : ∀ N B u a,
    a ∈ scalarSupport N B u ↔
      Sum.inr a ∈ HistoryHaarSectionWindow.support N (B - u ^ 2)
  full_finite_matrix : ∀ N B u A X (t : ℝ),
    precisionMatrix N B u (A + (t : ℂ) • X) = precisionMatrix N B u A +
      (t : ℂ) • firstMatrix N B u A X +
        ((t ^ 2 : ℝ) : ℂ) • directMatrix N B u X
  all_connections_positive : ∀ N B u A, (precisionMatrix N B u A).PosDef
  all_connections_uniform_bound : ∀ N B u A,
    (precisionMatrix N B u A - ((15 / 8 : ℝ) + u ^ 2) •
      (1 : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ)).PosSemidef
  full_inverse_unique : ∀ N B u A,
    ∃! C : Matrix (WindowIndex N B u) (WindowIndex N B u) ℂ,
      precisionMatrix N B u A * C = 1

theorem generated : Conclusions where
  original_action := original_action_eq
  full_precision_vertex := precisionForm_connection_ray
  actual_first_derivative := sectionAction_hasDerivAt
  actual_direct_second_derivative := sectionAction_secondDeriv
  original_current := firstVertex_at_zero
  actual_scalar_cutoff := mem_scalarSupport
  full_finite_matrix := precisionMatrix_connection_ray
  all_connections_positive := precisionMatrix_posDef
  all_connections_uniform_bound := precisionMatrix_uniform_lower
  full_inverse_unique := inversePrecision_existsUnique

end GeneratedFoundations.Arithmetic.HistoryHaarSectionConnectionVariation
