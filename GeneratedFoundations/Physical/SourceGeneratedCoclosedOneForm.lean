module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
public import GeneratedFoundations.Operations.FiniteEigenbasisCore
public import Mathlib.Tactic.DeriveCountable

/-!
# The complete generated coclosed colour one-form operator

The representation calculation on the generated projective three-space
provides two coclosed vector branches at every positive odd degree.  Their
combined multiplicity is `vectorMultiplicity l`.  This file retains every
such polarization and tensors it with all eight generated colour directions.
Thus the index below is the full representation-labelled one-particle mode
set, rather than one representative coordinate per degree.

The Hilbert space is the square-summable completion of that mode set.  On the
finite spectral span, the Yang--Mills response Hessian acts by the generated
coclosed eigenvalue.  The finite multiplier has a unique self-adjoint closure;
its domain is the corresponding weighted square-summability domain.  The
degree-one shell is proved to be the bottom of the entire closed tower and is
realized by an explicit colour-polarization basis vector.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap lp
open GeneratedFoundations.Operations
open GeneratedFoundations.Physical.SourceRP3FieldSpectrum
open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
open GeneratedFoundations.Geometry.SourceLeftRightRepresentations

namespace GeneratedFoundations.Physical.SourceGeneratedCoclosedOneForm

/-- The two source-generated coclosed vector branches.  They are retained as
part of the mode label rather than compressed into a bare dimension count. -/
inductive VectorBranch
  | plus
  | minus
  deriving DecidableEq, Countable

instance : Fintype VectorBranch where
  elems := {.plus, .minus}
  complete branch := by cases branch <;> simp

/-- A complete coclosed colour one-form mode.  Each explicit branch has the
generated half-multiplicity `vectorMultiplicity degree / 2`, while `colour`
runs through all eight generated adjoint directions. -/
structure CoclosedModeIndex where
  degree : ℕ
  degree_ok : VectorDegree degree
  branch : VectorBranch
  polarization : Fin (vectorMultiplicity degree / 2)
  colour : Fin 8
  deriving DecidableEq, Countable

/-- Casimir read directly from the generated left--right source carrier of
the selected coclosed branch. -/
def branchCasimir (a : CoclosedModeIndex) : ℝ :=
  match a.branch with
  | .plus => casimirIndex (a.degree + 1) (a.degree - 1)
  | .minus => casimirIndex (a.degree - 1) (a.degree + 1)

/-- Both source-generated vector branches have the same Hodge Casimir. -/
theorem branchCasimir_eq (a : CoclosedModeIndex) :
    branchCasimir a = vectorCasimir a.degree := by
  rcases generated_vector_branch_casimir a.degree_ok.2 with ⟨hplus, hminus⟩
  cases hbranch : a.branch <;> simp [branchCasimir, hbranch, hplus, hminus]

/-- The polarization label has exactly the dimension of the corresponding
generated source representation; it is not a supplied degeneracy table. -/
theorem polarization_card_eq_source_finrank (a : CoclosedModeIndex) :
    Fintype.card (Fin (vectorMultiplicity a.degree / 2)) =
      match a.branch with
      | .plus => Module.finrank ℂ (VectorPlusCarrier a.degree)
      | .minus => Module.finrank ℂ (VectorMinusCarrier a.degree) := by
  rcases generated_vector_branch_finrank a.degree_ok.2 with ⟨hplus, hminus⟩
  cases a.branch <;> simp [hplus, hminus]

/-- The complete square-summable generated coclosed one-form space. -/
abbrev CoclosedOneFormL2 := ℓ²(CoclosedModeIndex, ℂ)

/-- The canonical coordinate Hilbert basis of the complete mode space. -/
def coclosedBasis : HilbertBasis CoclosedModeIndex ℂ CoclosedOneFormL2 := default

/-- The generated shifted Hodge eigenvalue attached to a complete mode. -/
def modeEigenvalue (L z : ℝ) (a : CoclosedModeIndex) : ℝ :=
  coclosedMassIndex L z a.degree

/-- The complete mode eigenvalue is the generated representation Casimir,
scaled by the generated radius, plus the Gaussian connection-response shift. -/
theorem modeEigenvalue_eq_sourceCasimir_add_shift (L z : ℝ)
    (a : CoclosedModeIndex) :
    modeEigenvalue L z a = branchCasimir a / L ^ 2 +
      coclosedResponseShift L z := by
  rw [modeEigenvalue, coclosedMassIndex, vectorEigenvalue, branchCasimir_eq]

/-- A concrete degree-one polarization in the first generated colour
direction.  Its existence uses the full degree-one multiplicity six. -/
def lowestMode : CoclosedModeIndex where
  degree := 1
  degree_ok := by norm_num [VectorDegree]
  branch := .plus
  polarization := ⟨0, by norm_num [vectorMultiplicity]⟩
  colour := ⟨0, by norm_num⟩

@[simp] theorem lowestMode_degree : lowestMode.degree = 1 := rfl

@[simp] theorem modeEigenvalue_lowestMode (L z : ℝ) :
    modeEigenvalue L z lowestMode = coclosedMassIndex L z 1 := rfl

/-- Every complete coclosed mode lies above the degree-one shell. -/
theorem modeEigenvalue_bottom (L z : ℝ) (a : CoclosedModeIndex) :
    modeEigenvalue L z lowestMode ≤ modeEigenvalue L z a := by
  exact coclosedMassIndex_one_le a.degree_ok.2

/-- The bottom is positive on the generated condensed branch. -/
theorem modeEigenvalue_lowestMode_pos {L z : ℝ} (hL : 0 < L) (hz : 0 < z) :
    0 < modeEigenvalue L z lowestMode := by
  exact coclosedMassIndex_pos hL hz 1

/-- Finite linear combinations of complete coclosed modes. -/
def finiteCore (L z : ℝ) : CoclosedOneFormL2 →ₗ.[ℂ] CoclosedOneFormL2 :=
  FiniteEigenbasisCore.finiteMultiplier coclosedBasis (modeEigenvalue L z)

/-- The unique self-adjoint closure of the generated coclosed response
Hessian on its finite spectral core. -/
def operator (L z : ℝ) : CoclosedOneFormL2 →ₗ.[ℂ] CoclosedOneFormL2 :=
  (finiteCore L z).closure

theorem finiteCore_le_operator (L z : ℝ) : finiteCore L z ≤ operator L z :=
  FiniteEigenbasisCore.le_closure coclosedBasis (modeEigenvalue L z)

theorem operator_selfAdjoint (L z : ℝ) : IsSelfAdjoint (operator L z) :=
  FiniteEigenbasisCore.closure_selfAdjoint coclosedBasis (modeEigenvalue L z)

theorem operator_closed (L z : ℝ) : (operator L z).IsClosed :=
  (operator_selfAdjoint L z).isClosed

theorem operator_domain_dense (L z : ℝ) :
    Dense ((operator L z).domain : Set CoclosedOneFormL2) :=
  (operator_selfAdjoint L z).dense_domain

/-- No other self-adjoint operator can extend the same complete finite
spectral multiplier. -/
theorem selfAdjoint_extension_unique (L z : ℝ)
    (T : CoclosedOneFormL2 →ₗ.[ℂ] CoclosedOneFormL2)
    (hT : IsSelfAdjoint T) (hcore : finiteCore L z ≤ T) :
    T = operator L z :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique coclosedBasis
    (modeEigenvalue L z) T hT hcore

/-- The exact domain of the closed generated coclosed operator. -/
theorem operator_domain_iff_memℓp (L z : ℝ) (f : CoclosedOneFormL2) :
    f ∈ (operator L z).domain ↔
      Memℓp (fun a : CoclosedModeIndex =>
        (modeEigenvalue L z a : ℂ) * inner ℂ (coclosedBasis a) f) 2 := by
  simpa only [operator, finiteCore] using
    FiniteEigenbasisCore.closure_domain_iff_memℓp coclosedBasis
      (modeEigenvalue L z) f

/-- Equivalent weighted-square description of the full closed domain. -/
theorem operator_domain_iff_summable (L z : ℝ) (f : CoclosedOneFormL2) :
    f ∈ (operator L z).domain ↔
      Summable (fun a : CoclosedModeIndex =>
        modeEigenvalue L z a ^ 2 * ‖inner ℂ (coclosedBasis a) f‖ ^ 2) := by
  simpa only [operator, finiteCore] using
    FiniteEigenbasisCore.closure_domain_iff_summable coclosedBasis
      (modeEigenvalue L z) f

theorem operator_coefficients (L z : ℝ) (f : (operator L z).domain)
    (a : CoclosedModeIndex) :
    inner ℂ (coclosedBasis a) (operator L z f) =
      (modeEigenvalue L z a : ℂ) *
        inner ℂ (coclosedBasis a) (f : CoclosedOneFormL2) := by
  simpa only [operator, finiteCore] using
    FiniteEigenbasisCore.closure_coefficients coclosedBasis
      (modeEigenvalue L z) f a

theorem basis_mem_domain (L z : ℝ) (a : CoclosedModeIndex) :
    coclosedBasis a ∈ (operator L z).domain := by
  have h := FiniteEigenbasisCore.basis_mem_domain coclosedBasis
    (modeEigenvalue L z) a
  exact (finiteCore_le_operator L z).1 h

/-- Every retained branch, polarization and colour vector is an actual
eigenvector of the closed operator. -/
theorem operator_basis (L z : ℝ) (a : CoclosedModeIndex) :
    operator L z ⟨coclosedBasis a, basis_mem_domain L z a⟩ =
      (modeEigenvalue L z a : ℂ) • coclosedBasis a := by
  apply EigenbasisClosure.eq_of_coefficients coclosedBasis
  intro j
  rw [operator_coefficients, inner_smul_right,
    orthonormal_iff_ite.mp coclosedBasis.orthonormal]
  by_cases h : j = a
  · subst j
    rfl
  · simp only [h, ite_false, mul_zero]

/-- The degree-one basis vector realizes the exact lower edge of all basis
eigenvalues. -/
theorem operator_bottom_attained (L z : ℝ) :
    operator L z ⟨coclosedBasis lowestMode, basis_mem_domain L z lowestMode⟩ =
      (coclosedMassIndex L z 1 : ℂ) • coclosedBasis lowestMode := by
  simpa using operator_basis L z lowestMode

/-- Bundled statement of completeness, self-adjointness and the exact
generated degree-one bottom. -/
structure Properties : Prop where
  selfAdjoint : ∀ L z, IsSelfAdjoint (operator L z)
  basis_action : ∀ L z a,
    operator L z ⟨coclosedBasis a, basis_mem_domain L z a⟩ =
      (modeEigenvalue L z a : ℂ) • coclosedBasis a
  basis_lower_bound : ∀ L z a,
    modeEigenvalue L z lowestMode ≤ modeEigenvalue L z a
  bottom_attained : ∀ L z,
    operator L z ⟨coclosedBasis lowestMode, basis_mem_domain L z lowestMode⟩ =
      (coclosedMassIndex L z 1 : ℂ) • coclosedBasis lowestMode

theorem properties : Properties where
  selfAdjoint := operator_selfAdjoint
  basis_action := operator_basis
  basis_lower_bound := modeEigenvalue_bottom
  bottom_attained := operator_bottom_attained

end GeneratedFoundations.Physical.SourceGeneratedCoclosedOneForm
