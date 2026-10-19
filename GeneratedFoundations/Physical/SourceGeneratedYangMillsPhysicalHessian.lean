module

public import GeneratedFoundations.Physical.SourceGeneratedCoclosedOneForm
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
public import GeneratedFoundations.Operations.FiniteEigenbasisCore
public import Mathlib.Tactic.DeriveCountable

/-!
# The complete generated Yang--Mills response Hessian

The physical one-response space keeps the source-normalized radial direction
and every generated coclosed colour one-form mode.  The latter already retains
the two vector branches, their full multiplicities, every positive odd RP3
degree and all eight generated colour directions.

The eigenvalue function is not a supplied spectrum.  Its radial entry is the
curvature of the generated restoring response in the source information
metric; its coclosed entries are the generated RP3 Hodge eigenvalues plus the
Gaussian colour-covariance shift.  The finite multiplier therefore has a
unique self-adjoint closure on the complete response space.  Its exact lower
edge is the previously generated radial/coclosed minimum and is attained by
an explicit generated mode.
-/

@[expose] public section

noncomputable section

open scoped LinearPMap lp
open GeneratedFoundations.Operations
open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
open GeneratedFoundations.Physical.SourceGeneratedCoclosedOneForm

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsPhysicalHessian

/-- Complete one-response labels: one radial mode and the entire generated
coclosed colour one-form tower. -/
inductive PhysicalMode
  | radial
  | coclosed (mode : CoclosedModeIndex)
  deriving DecidableEq, Countable

/-- Hilbert completion of all generated physical one-response modes. -/
abbrev PhysicalResponseL2 := ℓ²(PhysicalMode, ℂ)

/-- Canonical complete coordinate basis of the physical response space. -/
def physicalBasis : HilbertBasis PhysicalMode ℂ PhysicalResponseL2 := default

/-- Eigenvalue of the complete response Hessian on a generated physical
mode. -/
def physicalEigenvalue (L z : ℝ) : PhysicalMode → ℝ
  | .radial => normalizedRadialMassSq z
  | .coclosed a => modeEigenvalue L z a

/-- Every physical eigenvalue lies above the generated radial/coclosed
minimum. -/
theorem gap_le_physicalEigenvalue (L z : ℝ) (a : PhysicalMode) :
    generatedYangMillsGapSq L z ≤ physicalEigenvalue L z a := by
  cases a with
  | radial => exact generatedYangMillsGapSq_le_radial L z
  | coclosed a =>
      exact (generatedYangMillsGapSq_le_coclosed a.degree_ok.2)

theorem physicalEigenvalue_pos {L z : ℝ} (hL : 0 < L) (hz : 0 < z)
    (a : PhysicalMode) : 0 < physicalEigenvalue L z a := by
  cases a with
  | radial => exact normalizedRadialMassSq_pos hz
  | coclosed a => exact coclosedMassIndex_pos hL hz a.degree

/-- A generated mode that realizes the smaller of the two response blocks. -/
def minimizingMode (L z : ℝ) : PhysicalMode :=
  if normalizedRadialMassSq z ≤ coclosedMassIndex L z 1 then
    .radial
  else
    .coclosed lowestMode

theorem physicalEigenvalue_minimizingMode (L z : ℝ) :
    physicalEigenvalue L z (minimizingMode L z) =
      generatedYangMillsGapSq L z := by
  unfold minimizingMode generatedYangMillsGapSq
  split_ifs with h
  · simp [physicalEigenvalue, min_eq_left h]
  · have h' : coclosedMassIndex L z 1 ≤ normalizedRadialMassSq z :=
      (lt_of_not_ge h).le
    simp [physicalEigenvalue, min_eq_right h']

/-- Finite physical-mode multiplier obtained from the complete generated
eigenvalue list. -/
def finiteCore (L z : ℝ) : PhysicalResponseL2 →ₗ.[ℂ] PhysicalResponseL2 :=
  FiniteEigenbasisCore.finiteMultiplier physicalBasis (physicalEigenvalue L z)

/-- Unique self-adjoint closure of the full generated physical response
Hessian. -/
def operator (L z : ℝ) : PhysicalResponseL2 →ₗ.[ℂ] PhysicalResponseL2 :=
  (finiteCore L z).closure

theorem finiteCore_le_operator (L z : ℝ) : finiteCore L z ≤ operator L z :=
  FiniteEigenbasisCore.le_closure physicalBasis (physicalEigenvalue L z)

theorem operator_selfAdjoint (L z : ℝ) : IsSelfAdjoint (operator L z) :=
  FiniteEigenbasisCore.closure_selfAdjoint physicalBasis (physicalEigenvalue L z)

theorem operator_closed (L z : ℝ) : (operator L z).IsClosed :=
  (operator_selfAdjoint L z).isClosed

theorem operator_domain_dense (L z : ℝ) :
    Dense ((operator L z).domain : Set PhysicalResponseL2) :=
  (operator_selfAdjoint L z).dense_domain

theorem selfAdjoint_extension_unique (L z : ℝ)
    (T : PhysicalResponseL2 →ₗ.[ℂ] PhysicalResponseL2)
    (hT : IsSelfAdjoint T) (hcore : finiteCore L z ≤ T) :
    T = operator L z :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique physicalBasis
    (physicalEigenvalue L z) T hT hcore

theorem operator_domain_iff_summable (L z : ℝ) (f : PhysicalResponseL2) :
    f ∈ (operator L z).domain ↔
      Summable (fun a : PhysicalMode =>
        physicalEigenvalue L z a ^ 2 * ‖inner ℂ (physicalBasis a) f‖ ^ 2) := by
  simpa only [operator, finiteCore] using
    FiniteEigenbasisCore.closure_domain_iff_summable physicalBasis
      (physicalEigenvalue L z) f

theorem operator_coefficients (L z : ℝ) (f : (operator L z).domain)
    (a : PhysicalMode) :
    inner ℂ (physicalBasis a) (operator L z f) =
      (physicalEigenvalue L z a : ℂ) *
        inner ℂ (physicalBasis a) (f : PhysicalResponseL2) := by
  simpa only [operator, finiteCore] using
    FiniteEigenbasisCore.closure_coefficients physicalBasis
      (physicalEigenvalue L z) f a

theorem basis_mem_domain (L z : ℝ) (a : PhysicalMode) :
    physicalBasis a ∈ (operator L z).domain := by
  have h := FiniteEigenbasisCore.basis_mem_domain physicalBasis
    (physicalEigenvalue L z) a
  exact (finiteCore_le_operator L z).1 h

theorem operator_basis (L z : ℝ) (a : PhysicalMode) :
    operator L z ⟨physicalBasis a, basis_mem_domain L z a⟩ =
      (physicalEigenvalue L z a : ℂ) • physicalBasis a := by
  apply EigenbasisClosure.eq_of_coefficients physicalBasis
  intro j
  rw [operator_coefficients, inner_smul_right,
    orthonormal_iff_ite.mp physicalBasis.orthonormal]
  by_cases h : j = a
  · subst j
    rfl
  · simp only [h, ite_false, mul_zero]

/-- The generated minimum is not merely a lower estimate: an explicit
physical basis mode realizes it. -/
theorem operator_bottom_attained (L z : ℝ) :
    operator L z
        ⟨physicalBasis (minimizingMode L z),
          basis_mem_domain L z (minimizingMode L z)⟩ =
      (generatedYangMillsGapSq L z : ℂ) •
        physicalBasis (minimizingMode L z) := by
  rw [operator_basis, physicalEigenvalue_minimizingMode]

/-- On the uniquely generated condensed branch the complete physical Hessian
has a strictly positive, exactly attained spectral bottom. -/
theorem condensed_operator_positive_bottom (L : ℝ)
    (hL : SourceInternalYangMillsResponse.criticalRadius < L) :
    0 < generatedYangMillsGapSq L
      (SourceGeneratedYangMillsAction.condensedAmplitude L hL) :=
  (SourceGeneratedYangMillsAction.condensedAmplitude_spec L hL).2.2

/-- Complete generated-scope operator conclusions. -/
structure Properties : Prop where
  selfAdjoint : ∀ L z, IsSelfAdjoint (operator L z)
  uniqueClosure : ∀ L z T, IsSelfAdjoint T → finiteCore L z ≤ T →
    T = operator L z
  basisAction : ∀ L z a,
    operator L z ⟨physicalBasis a, basis_mem_domain L z a⟩ =
      (physicalEigenvalue L z a : ℂ) • physicalBasis a
  completeLowerBound : ∀ L z a,
    generatedYangMillsGapSq L z ≤ physicalEigenvalue L z a
  exactBottom : ∀ L z,
    operator L z
        ⟨physicalBasis (minimizingMode L z),
          basis_mem_domain L z (minimizingMode L z)⟩ =
      (generatedYangMillsGapSq L z : ℂ) •
        physicalBasis (minimizingMode L z)
  condensedPositive : ∀ L
      (hL : SourceInternalYangMillsResponse.criticalRadius < L),
    0 < generatedYangMillsGapSq L
      (SourceGeneratedYangMillsAction.condensedAmplitude L hL)

theorem properties : Properties where
  selfAdjoint := operator_selfAdjoint
  uniqueClosure := selfAdjoint_extension_unique
  basisAction := operator_basis
  completeLowerBound := gap_le_physicalEigenvalue
  exactBottom := operator_bottom_attained
  condensedPositive := condensed_operator_positive_bottom

end GeneratedFoundations.Physical.SourceGeneratedYangMillsPhysicalHessian
