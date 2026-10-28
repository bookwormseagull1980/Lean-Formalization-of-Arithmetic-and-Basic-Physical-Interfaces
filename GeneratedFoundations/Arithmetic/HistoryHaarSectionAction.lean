module

public import GeneratedFoundations.Arithmetic.HistoryFieldResolution
public import GeneratedFoundations.Arithmetic.HistoryHaarCoupledAction
public import GeneratedFoundations.Geometry.SourceScalarKineticForm

/-!
# The joint action on position-dependent complete history sections

The scalar coefficients and source derivatives are those already constructed
on the original quotient Haar source. Each section retains every arithmetic
history, finite phase and source coordinate. The connection is the original
matrix-valued differentiated Haar core; its product with a section is formed
on continuous representatives, before passage to Haar space.

The covariant derivative contains both the differentiated section and the
matrix evaluation. Their interference survives in the nonlinear action.
Along a joint ray it is a cubic term. With the state fixed it is the linear
connection current, which was absent for homogeneous sections. The vacuum
Hessian, including the section kinetic energy, follows by differentiating
this same functional. No position count or response window is an input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionAction

open Geometry.SourceSpinCentre Geometry.SourceQuotientHilbert
open Geometry.SourceOneFormHaarBlock Geometry.SourceOneFormContinuousCore
open Geometry.SourceScalarResolution (ScalarCore includeScalar)
open HistoryHaarMatrixCurvature (Index Coefficients)

abbrev Sections (N : ℕ) := Index N → ScalarCore
abbrev StateFields (N : ℕ) := PiLp 2 (fun _ : Index N => QuotientL2)
abbrev DerivativeFields (N : ℕ) := PiLp 2 (fun _ : Index N => OneFormL2)

def sectionField (N : ℕ) : Sections N →ₗ[ℂ] StateFields N where
  toFun ψ := WithLp.toLp 2 fun i => includeScalar (ψ i)
  map_add' ψ ξ := by
    apply (WithLp.equiv 2 (Index N → QuotientL2)).injective
    funext i
    exact map_add includeScalar _ _
  map_smul' z ψ := by
    apply (WithLp.equiv 2 (Index N → QuotientL2)).injective
    funext i
    exact map_smul includeScalar z _

/-- The unit metric source derivative of every original section component. -/
def gradient (N : ℕ) : Sections N →ₗ[ℂ] DerivativeFields N where
  toFun ψ := WithLp.toLp 2 fun i => Geometry.SourceScalarKineticForm.gradient (ψ i)
  map_add' ψ ξ := by
    apply (WithLp.equiv 2 (Index N → OneFormL2)).injective
    funext i
    change toHaar (fun j =>
      Geometry.SourceScalarResolution.derivative 1 j (ψ i + ξ i)) = _
    simp only [map_add]
    rfl
  map_smul' z ψ := by
    apply (WithLp.equiv 2 (Index N → OneFormL2)).injective
    funext i
    change toHaar (fun j =>
      Geometry.SourceScalarResolution.derivative 1 j (z • ψ i)) = _
    simp only [map_smul]
    rfl

def connectionRepresentative (N : ℕ) (A : Coefficients N) (ψ : Sections N)
    (i : Index N) : ContinuousField := fun j =>
  ∑ k : Index N, representative (A i k) j *
    Geometry.SourceScalarResolution.representative (ψ k)

/-- No product is projected into its initial finite coefficient core. -/
def connectionDerivative (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    DerivativeFields N :=
  WithLp.toLp 2 fun i => toHaar (connectionRepresentative N A ψ i)

theorem connectionRepresentative_smul (N : ℕ) (z w : ℂ)
    (A : Coefficients N) (ψ : Sections N) (i : Index N) :
    connectionRepresentative N (z • A) (w • ψ) i =
      (z * w) • connectionRepresentative N A ψ i := by
  funext j
  ext x
  simp only [connectionRepresentative, Matrix.smul_apply, map_smul,
    Pi.smul_apply, ContinuousMap.sum_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem connectionDerivative_smul (N : ℕ) (z w : ℂ)
    (A : Coefficients N) (ψ : Sections N) :
    connectionDerivative N (z • A) (w • ψ) =
      (z * w) • connectionDerivative N A ψ := by
  apply (WithLp.equiv 2 (Index N → OneFormL2)).injective
  funext i
  change toHaar (connectionRepresentative N (z • A) (w • ψ) i) = _
  rw [connectionRepresentative_smul, map_smul]
  rfl

def covariantDerivative (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    DerivativeFields N := gradient N ψ + connectionDerivative N A ψ

/-- The original one-form components have actual finite scalar coordinates;
this map does not approximate or project the connection. -/
def connectionCoordinates (N : ℕ) (A : Coefficients N) : HistoryFieldResolution.Connection N :=
  fun j a => Geometry.SourceOneFormScalarCoordinates.component j (A a.1 a.2)

/-- This identity uses the original pointwise response from the complete
resolution construction, including all cross-history matrix entries. -/
theorem covariantDerivative_component (N : ℕ) (A : Coefficients N)
    (ψ : Sections N) (i : Index N) (j : Fin 3) :
    covariantDerivative N A ψ i j =
      HistoryFieldResolution.matterDerivative N 1
        (connectionCoordinates N A, ψ) j i := by
  change ContinuousMap.toLp 2 quotientHaar ℂ
      (Geometry.SourceScalarResolution.derivative 1 j (ψ i)) +
    ContinuousMap.toLp 2 quotientHaar ℂ
      (∑ k, representative (A i k) j *
        Geometry.SourceScalarResolution.representative (ψ k)) = _
  rw [← map_add]
  simp only [HistoryFieldResolution.matterDerivative, HistoryFieldResolution.matrixProduct,
    connectionCoordinates, Geometry.SourceOneFormScalarCoordinates.component_representative]

def action (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  HistoryHaarMatrixCurvature.action N A + ‖covariantDerivative N A ψ‖ ^ 2 / 2 +
    HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2 / 2

theorem action_nonneg (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    0 ≤ action N A ψ := by
  unfold action
  exact add_nonneg
    (add_nonneg (HistoryHaarMatrixCurvature.action_nonneg N A)
      (div_nonneg (sq_nonneg _) (by norm_num)))
    (div_nonneg (mul_nonneg (HistoryDefiningResponse.coefficient_pos N).le
      (sq_nonneg _)) (by norm_num))

def quadratic (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  ‖HistoryHaarMatrixCurvature.differentiated N A‖ ^ 2 + ‖gradient N ψ‖ ^ 2 +
    HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2

def sectionCurrent (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  (inner ℂ (gradient N ψ) (connectionDerivative N A ψ)).re

def cubic (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  HistoryHaarCoupledAction.cubic N A + sectionCurrent N A ψ

def quartic (N : ℕ) (A : Coefficients N) (ψ : Sections N) : ℝ :=
  (‖HistoryHaarMatrixCurvature.vertex N A‖ ^ 2 +
    ‖connectionDerivative N A ψ‖ ^ 2) / 2

theorem covariantDerivative_ray (N : ℕ) (t : ℝ)
    (A : Coefficients N) (ψ : Sections N) :
    covariantDerivative N ((t : ℂ) • A) ((t : ℂ) • ψ) =
      (t : ℂ) • gradient N ψ + ((t ^ 2 : ℝ) : ℂ) • connectionDerivative N A ψ := by
  rw [covariantDerivative, map_smul, connectionDerivative_smul]
  simp only [pow_two, Complex.ofReal_mul]

/-- Full ray expansion: the derivative--connection pairing is retained. -/
theorem action_ray (N : ℕ) (t : ℝ) (A : Coefficients N) (ψ : Sections N) :
    action N ((t : ℂ) • A) ((t : ℂ) • ψ) =
      t ^ 2 * quadratic N A ψ / 2 + t ^ 3 * cubic N A ψ + t ^ 4 * quartic N A ψ := by
  rw [action, HistoryHaarMatrixCurvature.action_ray, covariantDerivative_ray,
    norm_add_sq (𝕜 := ℂ), map_smul]
  simp only [RCLike.re_eq_complex_re, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ),
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  unfold quadratic cubic quartic sectionCurrent HistoryHaarCoupledAction.cubic
  ring

theorem sectionCurrent_smul (N : ℕ) (s : ℝ)
    (A : Coefficients N) (ψ : Sections N) :
    sectionCurrent N A ((s : ℂ) • ψ) = s ^ 2 * sectionCurrent N A ψ := by
  have h := connectionDerivative_smul N 1 (s : ℂ) A ψ
  simp only [one_smul, one_mul] at h
  rw [sectionCurrent, map_smul, h, inner_smul_left (𝕜 := ℂ),
    inner_smul_right (𝕜 := ℂ)]
  simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, sectionCurrent]
  ring

/-- At fixed section the full current contributes linearly to the
connection variation; it is not a positive mass or a vanished cross term. -/
theorem action_connection_ray (N : ℕ) (t : ℝ)
    (A : Coefficients N) (ψ : Sections N) :
    action N ((t : ℂ) • A) ψ =
      (‖gradient N ψ‖ ^ 2 +
        HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2) / 2 +
      t * sectionCurrent N A ψ +
      t ^ 2 * (‖HistoryHaarMatrixCurvature.differentiated N A‖ ^ 2 +
        ‖connectionDerivative N A ψ‖ ^ 2) / 2 +
      t ^ 3 * HistoryHaarCoupledAction.cubic N A +
      t ^ 4 * ‖HistoryHaarMatrixCurvature.vertex N A‖ ^ 2 / 2 := by
  have h := connectionDerivative_smul N (t : ℂ) 1 A ψ
  simp only [one_smul, mul_one] at h
  rw [action, HistoryHaarMatrixCurvature.action_ray, covariantDerivative, h,
    norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.re_eq_complex_re, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, inner_smul_right (𝕜 := ℂ), Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  unfold sectionCurrent HistoryHaarCoupledAction.cubic
  ring

theorem action_connection_firstDeriv (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    HasDerivAt (fun t : ℝ => action N ((t : ℂ) • A) ψ) (sectionCurrent N A ψ) 0 := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt
    ((‖gradient N ψ‖ ^ 2 +
      HistoryDefiningResponse.coefficient N * ‖sectionField N ψ‖ ^ 2) / 2)
    (sectionCurrent N A ψ)
    ((‖HistoryHaarMatrixCurvature.differentiated N A‖ ^ 2 +
      ‖connectionDerivative N A ψ‖ ^ 2) / 2)
    (HistoryHaarCoupledAction.cubic N A)
    (‖HistoryHaarMatrixCurvature.vertex N A‖ ^ 2 / 2) 0 using 1
  · funext t
    rw [action_connection_ray]
    ring
  · simp

def rayDerivative (N : ℕ) (A : Coefficients N) (ψ : Sections N) (t : ℝ) : ℝ :=
  t * quadratic N A ψ + 3 * t ^ 2 * cubic N A ψ + 4 * t ^ 3 * quartic N A ψ

theorem action_hasDerivAt (N : ℕ) (A : Coefficients N) (ψ : Sections N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ))
      (rayDerivative N A ψ t) t := by
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0 0
    (quadratic N A ψ / 2) (cubic N A ψ) (quartic N A ψ) t using 1
  · funext s
    rw [action_ray]
    ring
  · unfold rayDerivative
    ring

theorem secondDeriv_zero (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ)) t)
      (quadratic N A ψ) 0 := by
  have h : (fun t : ℝ => deriv
      (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ)) t) =
      rayDerivative N A ψ := funext fun t => (action_hasDerivAt N A ψ t).deriv
  rw [h]
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt 0
    (quadratic N A ψ) (3 * cubic N A ψ) (4 * quartic N A ψ) 0 0 using 1
  · funext t
    unfold rayDerivative
    ring
  · simp

theorem action_mixed_secondDeriv_zero (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      action N ((t : ℂ) • A) ((s : ℂ) • ψ)) 0) 0 0 := by
  have h : (fun s : ℝ => deriv (fun t : ℝ =>
      action N ((t : ℂ) • A) ((s : ℂ) • ψ)) 0) =
      fun s => s ^ 2 * sectionCurrent N A ψ := by
    funext s
    rw [(action_connection_firstDeriv N A ((s : ℂ) • ψ)).deriv,
      sectionCurrent_smul]
  rw [h]
  convert Geometry.HilbertTraceVariation.quartic_hasDerivAt
    0 0 (sectionCurrent N A ψ) 0 0 0 using 1 <;> simp

def hessian (N : ℕ) (A B : Coefficients N) (ψ ξ : Sections N) : ℝ :=
  (inner ℂ (HistoryHaarMatrixCurvature.differentiated N A)
    (HistoryHaarMatrixCurvature.differentiated N B)).re +
    (inner ℂ (gradient N ψ) (gradient N ξ)).re +
    HistoryDefiningResponse.coefficient N *
      (inner ℂ (sectionField N ψ) (sectionField N ξ)).re

theorem hessian_diagonal (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    hessian N A A ψ ψ = quadratic N A ψ := by
  simp [hessian, quadratic, inner_self_eq_norm_sq_to_K, pow_two, Complex.mul_re]

theorem hessian_polarization (N : ℕ) (A B : Coefficients N) (ψ ξ : Sections N) :
    quadratic N (A + B) (ψ + ξ) - quadratic N A ψ - quadratic N B ξ =
      2 * hessian N A B ψ ξ := by
  simp only [quadratic, map_add, norm_add_sq (𝕜 := ℂ), hessian,
    RCLike.re_eq_complex_re]
  ring

/-- The kinetic term is retained with coefficient one, before any lower
bound is applied to the already derived restoring coefficient. -/
theorem joint_coercivity (N : ℕ) (A : Coefficients N) (ψ : Sections N) :
    4 * ‖HistoryHaarMatrixCurvature.field N A‖ ^ 2 + ‖gradient N ψ‖ ^ 2 +
      (15 / 8 : ℝ) * ‖sectionField N ψ‖ ^ 2 ≤ quadratic N A ψ := by
  have hA := HistoryHaarMatrixCurvature.hessian_coercive N A
  have hψ := mul_le_mul_of_nonneg_right (HistoryDefiningResponse.coefficient_lower N)
    (sq_nonneg ‖sectionField N ψ‖)
  unfold quadratic
  linarith

/-- One original normalized source coefficient in one complete history
coordinate. No other history coordinate is identified with it. -/
def basisSection (N : ℕ) (i : Index N)
    (a : Geometry.SourceQuotientHilbert.EvenIndex) : Sections N := by
  classical
  exact Pi.single i (Geometry.SourceScalarResolution.scalarBasis a)

theorem sectionField_basisSection (N : ℕ) (i : Index N)
    (a : Geometry.SourceQuotientHilbert.EvenIndex) :
    sectionField N (basisSection N i a) =
      PiLp.single 2 i (includeScalar (Geometry.SourceScalarResolution.scalarBasis a)) := by
  classical
  apply (WithLp.equiv 2 (Index N → QuotientL2)).injective
  funext j
  by_cases h : i = j
  · subst j
    simp [sectionField, basisSection]
  · simp [sectionField, basisSection, h]

theorem gradient_basisSection (N : ℕ) (i : Index N)
    (a : Geometry.SourceQuotientHilbert.EvenIndex) :
    gradient N (basisSection N i a) =
      PiLp.single 2 i (Geometry.SourceScalarKineticForm.gradient
        (Geometry.SourceScalarResolution.scalarBasis a)) := by
  classical
  apply (WithLp.equiv 2 (Index N → OneFormL2)).injective
  funext j
  by_cases h : i = j
  · subst j
    simp [gradient, basisSection]
  · simp [gradient, basisSection, h]

theorem basisSection_norm (N : ℕ) (i : Index N)
    (a : Geometry.SourceQuotientHilbert.EvenIndex) :
    ‖sectionField N (basisSection N i a)‖ = 1 := by
  classical
  rw [sectionField_basisSection, PiLp.norm_single,
    Geometry.SourceScalarKineticForm.coefficient_norm]

/-- Kinetic and restoring contributions are calculated separately from
the very same second variation. The source degree is even. -/
theorem quadratic_basisSection (N : ℕ) (i : Index N)
    (a : Geometry.SourceQuotientHilbert.EvenIndex) :
    quadratic N 0 (basisSection N i a) =
      Geometry.SourceCasimirClosure.energy a.val.1 +
        HistoryDefiningResponse.coefficient N := by
  classical
  rw [quadratic, map_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    gradient_basisSection, PiLp.norm_single,
    Geometry.SourceScalarKineticForm.gradient_basis_energy, basisSection_norm,
    one_pow, mul_one]

abbrev PositionLabels (N j : ℕ) :=
  Index N × Fin (2 * j + 1) × Fin (2 * j + 1)

/-- The two row coordinates and every original history--phase coordinate
are retained. The multiplicity is calculated, not a content parameter. -/
theorem position_multiplicity (N j : ℕ) :
    Fintype.card (PositionLabels N j) =
      HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2 := by
  simp [PositionLabels, HistoryAdjointCasimir.dimension, pow_two, Nat.mul_assoc]

def positionSection (N j : ℕ) (i : PositionLabels N j) : Sections N :=
  basisSection N i.1 ⟨⟨2 * j, i.2.1, i.2.2⟩, by
    change Even (2 * j)
    exact ⟨j, by omega⟩⟩

theorem positionSection_quadratic (N j : ℕ) (i : PositionLabels N j) :
    quadratic N 0 (positionSection N j i) =
      Geometry.SourceScalarKineticForm.position j + HistoryDefiningResponse.coefficient N :=
  quadratic_basisSection N i.1 _

structure Conclusions : Prop where
  actual_section_derivative : ∀ N A ψ i j,
    covariantDerivative N A ψ i j =
      HistoryFieldResolution.matterDerivative N 1
        (connectionCoordinates N A, ψ) j i
  nonnegative_action : ∀ N A ψ, 0 ≤ action N A ψ
  complete_ray_expansion : ∀ N (t : ℝ) A ψ,
    action N ((t : ℂ) • A) ((t : ℂ) • ψ) =
      t ^ 2 * quadratic N A ψ / 2 + t ^ 3 * cubic N A ψ + t ^ 4 * quartic N A ψ
  actual_connection_current : ∀ N A ψ,
    HasDerivAt (fun t : ℝ => action N ((t : ℂ) • A) ψ) (sectionCurrent N A ψ) 0
  actual_second_variation : ∀ N A ψ,
    HasDerivAt (fun t : ℝ => deriv
      (fun s : ℝ => action N ((s : ℂ) • A) ((s : ℂ) • ψ)) t) (quadratic N A ψ) 0
  derived_mixed_vacuum : ∀ N A ψ,
    HasDerivAt (fun s : ℝ => deriv (fun t : ℝ =>
      action N ((t : ℂ) • A) ((s : ℂ) • ψ)) 0) 0 0
  complete_polarization : ∀ N A B ψ ξ,
    quadratic N (A + B) (ψ + ξ) - quadratic N A ψ - quadratic N B ξ =
      2 * hessian N A B ψ ξ
  kinetic_restoring_bound : ∀ N A ψ,
    4 * ‖HistoryHaarMatrixCurvature.field N A‖ ^ 2 + ‖gradient N ψ‖ ^ 2 +
      (15 / 8 : ℝ) * ‖sectionField N ψ‖ ^ 2 ≤ quadratic N A ψ
  actual_basis_kinetic : ∀ N i a,
    quadratic N 0 (basisSection N i a) =
      Geometry.SourceCasimirClosure.energy a.val.1 + HistoryDefiningResponse.coefficient N
  actual_position_multiplicity : ∀ N j,
    Fintype.card (PositionLabels N j) = HistoryAdjointCasimir.dimension N * (2 * j + 1) ^ 2
  actual_position_response : ∀ N j i,
    quadratic N 0 (positionSection N j i) =
      Geometry.SourceScalarKineticForm.position j + HistoryDefiningResponse.coefficient N

theorem generated : Conclusions where
  actual_section_derivative := covariantDerivative_component
  nonnegative_action := action_nonneg
  complete_ray_expansion := action_ray
  actual_connection_current := action_connection_firstDeriv
  actual_second_variation := secondDeriv_zero
  derived_mixed_vacuum := action_mixed_secondDeriv_zero
  complete_polarization := hessian_polarization
  kinetic_restoring_bound := joint_coercivity
  actual_basis_kinetic := quadratic_basisSection
  actual_position_multiplicity := position_multiplicity
  actual_position_response := positionSection_quadratic

end GeneratedFoundations.Arithmetic.HistoryHaarSectionAction
