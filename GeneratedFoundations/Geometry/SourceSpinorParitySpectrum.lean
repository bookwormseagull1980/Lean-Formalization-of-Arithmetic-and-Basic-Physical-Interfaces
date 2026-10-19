module

public import GeneratedFoundations.Geometry.SourceSpinorCentralSectors

/-!
# The two central spinor sectors in the original Haar space

The two spaces are the eigenspaces of the actual geometric central pullback.
Their complete bases are obtained from the differentiated source fields.
The closed sector operators are proved to be restrictions of the same
original Dirac operator; neither a branch table nor a boundary condition
is supplied as an additional input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceSpinorHaarBlock
open GeneratedFoundations.Geometry.SourceSpinorClosedSpectrum
open GeneratedFoundations.Geometry.SourceSpinorCentralSectors
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceSpinorParitySpectrum

def sign (odd : Bool) : ℂ := if odd then -1 else 1

def sector (odd : Bool) : Submodule ℂ SpinorL2 :=
  LinearMap.ker (central.toLinearMap - sign odd • (1 : Module.End ℂ SpinorL2))

theorem mem_sector (odd : Bool) (F : SpinorL2) :
    F ∈ sector odd ↔ central F = sign odd • F := by
  change central F - sign odd • F = 0 ↔ _
  exact sub_eq_zero

theorem sector_isClosed (odd : Bool) : IsClosed (sector odd : Set SpinorL2) := by
  have h : IsClosed {F : SpinorL2 | central F = sign odd • F} :=
    isClosed_eq central.continuous (continuous_const_smul (sign odd))
  convert h using 1
  ext F
  exact mem_sector odd F

instance sectorComplete (odd : Bool) : CompleteSpace (sector odd) :=
  (sector_isClosed odd).isComplete.completeSpace_coe

abbrev Index (odd : Bool) := {a : SpinIndex // (-1 : ℂ) ^ a.1.1 = sign odd}

def sectorEigenfield (odd : Bool) (a : Index odd) : sector odd :=
  ⟨eigenfield a.val, (mem_sector odd _).mpr
    ((central_eigenfield a.val).trans (congrArg (fun c : ℂ => c • eigenfield a.val)
      a.property))⟩

theorem sectorEigenfield_orthonormal (odd : Bool) :
    Orthonormal ℂ (sectorEigenfield odd) := by
  rw [orthonormal_iff_ite]
  intro a b
  change inner ℂ (eigenfield a.val) (eigenfield b.val) = _
  rw [orthonormal_iff_ite.mp eigenfield_orthonormal]
  simp only [Subtype.val_inj]

theorem coefficient_zero (odd : Bool) (F : sector odd) (a : SpinIndex)
    (ha : (-1 : ℂ) ^ a.1.1 ≠ sign odd) :
    inner ℂ (eigenfield a) (F : SpinorL2) = 0 := by
  have h := central_coefficients (F : SpinorL2) a
  rw [(mem_sector odd _).mp F.property, inner_smul_right] at h
  have hm : (sign odd - (-1 : ℂ) ^ a.1.1) *
      inner ℂ (eigenfield a) (F : SpinorL2) = 0 := by
    rw [sub_mul, h, sub_self]
  exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr ha.symm)

def finiteSectorCore (odd : Bool) : Submodule ℂ (sector odd) :=
  Submodule.span ℂ (Set.range (sectorEigenfield odd))

theorem finiteSectorCore_orthogonal (odd : Bool) :
    (finiteSectorCore odd)ᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro F hF
  have hselected (a : Index odd) : inner ℂ (eigenfield a.val) (F : SpinorL2) = 0 :=
    ((finiteSectorCore odd).mem_orthogonal F).mp hF (sectorEigenfield odd a)
      (Submodule.subset_span (Set.mem_range_self a))
  change F = 0
  apply Subtype.ext
  apply EigenbasisClosure.eq_of_coefficients diracHilbertBasis
  intro a
  rw [diracHilbertBasis_apply, Submodule.coe_zero, inner_zero_right]
  by_cases ha : (-1 : ℂ) ^ a.1.1 = sign odd
  · exact hselected ⟨a, ha⟩
  · exact coefficient_zero odd F a ha

def sectorHilbertBasis (odd : Bool) : HilbertBasis (Index odd) ℂ (sector odd) :=
  HilbertBasis.mkOfOrthogonalEqBot (sectorEigenfield_orthonormal odd)
    (finiteSectorCore_orthogonal odd)

@[simp] theorem sectorHilbertBasis_apply (odd : Bool) (a : Index odd) :
    sectorHilbertBasis odd a = sectorEigenfield odd a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    (sectorEigenfield_orthonormal odd) (finiteSectorCore_orthogonal odd)) a

def finiteSectorDirac (odd : Bool) : sector odd →ₗ.[ℂ] sector odd :=
  FiniteEigenbasisCore.finiteMultiplier (sectorHilbertBasis odd) (fun a => eigenvalue a.val)

def closedSectorDirac (odd : Bool) : sector odd →ₗ.[ℂ] sector odd :=
  (finiteSectorDirac odd).closure

theorem closedSectorDirac_selfAdjoint (odd : Bool) :
    IsSelfAdjoint (closedSectorDirac odd) :=
  FiniteEigenbasisCore.closure_selfAdjoint (sectorHilbertBasis odd) _

theorem closedSectorDirac_unique (odd : Bool) (S : sector odd →ₗ.[ℂ] sector odd)
    (hS : IsSelfAdjoint S) (hcore : finiteSectorDirac odd ≤ S) :
    S = closedSectorDirac odd :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique (sectorHilbertBasis odd) _ S hS hcore

theorem closedSectorDirac_domain (odd : Bool) (F : sector odd) :
    F ∈ (closedSectorDirac odd).domain ↔
      Summable (fun a : Index odd => eigenvalue a.val ^ 2 *
        ‖inner ℂ (eigenfield a.val) (F : SpinorL2)‖ ^ 2) := by
  simpa only [closedSectorDirac, finiteSectorDirac, sectorHilbertBasis_apply,
    sectorEigenfield, Submodule.coe_inner] using
    FiniteEigenbasisCore.closure_domain_iff_summable
      (sectorHilbertBasis odd) (fun a => eigenvalue a.val) F

theorem closedSectorDirac_coefficients (odd : Bool)
    (F : (closedSectorDirac odd).domain) (a : Index odd) :
    inner ℂ (eigenfield a.val) ((closedSectorDirac odd F : sector odd) : SpinorL2) =
      (eigenvalue a.val : ℂ) * inner ℂ (eigenfield a.val) ((F : sector odd) : SpinorL2) := by
  simpa only [closedSectorDirac, finiteSectorDirac, sectorHilbertBasis_apply,
    sectorEigenfield, Submodule.coe_inner] using
    FiniteEigenbasisCore.closure_coefficients
      (sectorHilbertBasis odd) (fun a => eigenvalue a.val) F a

theorem sector_domain_iff_full (odd : Bool) (F : sector odd) :
    F ∈ (closedSectorDirac odd).domain ↔ (F : SpinorL2) ∈ closedDirac.domain := by
  classical
  rw [closedSectorDirac_domain, closedDirac_domain]
  constructor
  · intro hF
    have h : Summable ({a : SpinIndex | (-1 : ℂ) ^ a.1.1 = sign odd}.indicator
        (fun a : SpinIndex => eigenvalue a ^ 2 *
          ‖inner ℂ (eigenfield a) (F : SpinorL2)‖ ^ 2)) :=
      (summable_subtype_iff_indicator
        (s := {a : SpinIndex | (-1 : ℂ) ^ a.1.1 = sign odd})
        (f := fun a : SpinIndex => eigenvalue a ^ 2 *
          ‖inner ℂ (eigenfield a) (F : SpinorL2)‖ ^ 2)).mp hF
    convert h using 1
    funext a
    by_cases ha : (-1 : ℂ) ^ a.1.1 = sign odd
    · simp [ha]
    · simp [ha, coefficient_zero odd F a ha]
  · intro hF
    exact hF.subtype _

def fullDomain (odd : Bool) (F : (closedSectorDirac odd).domain) : closedDirac.domain :=
  ⟨((F : sector odd) : SpinorL2), (sector_domain_iff_full odd _).mp F.property⟩

/-- This identity identifies the sector closure with the original field
operator on its entire domain, not only on finite eigenfield sums. -/
theorem closedSectorDirac_is_restriction (odd : Bool)
    (F : (closedSectorDirac odd).domain) :
    ((closedSectorDirac odd F : sector odd) : SpinorL2) = closedDirac (fullDomain odd F) := by
  classical
  apply EigenbasisClosure.eq_of_coefficients diracHilbertBasis
  intro a
  rw [diracHilbertBasis_apply, closedDirac_coefficients]
  by_cases ha : (-1 : ℂ) ^ a.1.1 = sign odd
  · exact closedSectorDirac_coefficients odd F ⟨a, ha⟩
  · rw [coefficient_zero odd (closedSectorDirac odd F) a ha]
    change 0 = (eigenvalue a : ℂ) *
      inner ℂ (eigenfield a) ((F : sector odd) : SpinorL2)
    rw [coefficient_zero odd (F : sector odd) a ha, mul_zero]

theorem closedSectorDirac_norm_lower (odd : Bool)
    (F : (closedSectorDirac odd).domain) :
    (3 / 2 : ℝ) ^ 2 * ‖(F : sector odd)‖ ^ 2 ≤ ‖closedSectorDirac odd F‖ ^ 2 :=
  SpectralFormLowerBound.closed_norm_lower_bound (sectorHilbertBasis odd)
    (fun a => eigenvalue a.val) ((3 / 2 : ℝ) ^ 2)
    (fun a => eigenvalue_sq_lower a.val) F

end GeneratedFoundations.Geometry.SourceSpinorParitySpectrum
