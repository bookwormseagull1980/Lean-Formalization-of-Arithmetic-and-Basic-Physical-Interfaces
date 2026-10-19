module

public import GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum

/-!
# The Hodge Laplacian obtained by applying the source curl twice

The finite core consists of actual coclosed Haar fields. Its first-order
operator is intertwined with the closed curl on the original field space.
Applying that differential twice determines the Hodge coefficients. Only
after this identification do we close the second-order graph by the complete
orthonormal basis. Both the domain and uniqueness concern the original
coclosed field space.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian

abbrev Core := FiniteEigenbasisCore.finiteSpan coclosedHilbertBasis

def coreBasis : Module.Basis CoclosedIndex ℂ Core :=
  FiniteEigenbasisCore.finiteBasis coclosedHilbertBasis

def includeCore : Core →ₗ[ℂ] OneFormL2 :=
  coclosedField.subtype.comp
    (FiniteEigenbasisCore.finiteSpan coclosedHilbertBasis).subtype

@[simp] theorem includeCore_basis (a : CoclosedIndex) :
    includeCore (coreBasis a) = eigenfield a.val := by
  exact congrArg (fun A : coclosedField => A.val)
    ((FiniteEigenbasisCore.finiteBasis_coe coclosedHilbertBasis a).trans
      (coclosedHilbertBasis_apply a))

/-- The already differentiated first-order operator, on the actual dense
field core. Its eigenvalues have been derived from the source commutators. -/
def coreCurl : Core →ₗ[ℂ] Core :=
  coreBasis.constr ℂ (fun a => (eigenvalue a.val : ℂ) • coreBasis a)

@[simp] theorem coreCurl_basis (a : CoclosedIndex) :
    coreCurl (coreBasis a) = (eigenvalue a.val : ℂ) • coreBasis a :=
  coreBasis.constr_basis ℂ _ a

/-- This map remembers the actual full-field differential domain. -/
def coreToCurlDomain : Core →ₗ[ℂ] closedCurl.domain :=
  coreBasis.constr ℂ (fun a =>
    ⟨eigenfield a.val, eigenfield_mem_domain a.val⟩)

theorem coreToCurlDomain_val (x : Core) :
    (coreToCurlDomain x : OneFormL2) = includeCore x := by
  have h : closedCurl.domain.subtype.comp coreToCurlDomain = includeCore := by
    apply coreBasis.ext
    intro a
    change (coreToCurlDomain (coreBasis a) : OneFormL2) = includeCore (coreBasis a)
    rw [coreToCurlDomain, coreBasis.constr_basis, includeCore_basis]
  exact LinearMap.congr_fun h x

/-- The core operator is exactly the original Haar-field differential. -/
theorem coreCurl_is_differential (x : Core) :
    closedCurl (coreToCurlDomain x) = includeCore (coreCurl x) := by
  have h : closedCurl.toFun.comp coreToCurlDomain = includeCore.comp coreCurl := by
    apply coreBasis.ext
    intro a
    change closedCurl (coreToCurlDomain (coreBasis a)) =
      includeCore (coreCurl (coreBasis a))
    rw [coreToCurlDomain, coreBasis.constr_basis, closedCurl_eigenfield,
      coreCurl_basis, map_smul, includeCore_basis]
  exact LinearMap.congr_fun h x

def hodgeEigenvalue (a : CoclosedIndex) : ℝ := eigenvalue a.val ^ 2

def finiteHodge : coclosedField →ₗ.[ℂ] coclosedField :=
  FiniteEigenbasisCore.finiteMultiplier coclosedHilbertBasis hodgeEigenvalue

theorem finiteHodge_core (x : Core) :
    finiteHodge x = ((coreCurl.comp coreCurl x : Core) : coclosedField) := by
  have h : finiteHodge.toFun =
      (FiniteEigenbasisCore.finiteSpan coclosedHilbertBasis).subtype.comp
        (coreCurl.comp coreCurl) := by
    apply coreBasis.ext
    intro a
    have hb : coreBasis a =
        (⟨coclosedHilbertBasis a,
          FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis hodgeEigenvalue a⟩ :
            finiteHodge.domain) :=
      Subtype.ext (FiniteEigenbasisCore.finiteBasis_coe coclosedHilbertBasis a)
    change finiteHodge (coreBasis a) = _
    have ha : finiteHodge (coreBasis a) =
        (hodgeEigenvalue a : ℂ) • coclosedHilbertBasis a := by
      rw [hb]
      exact FiniteEigenbasisCore.basis_action coclosedHilbertBasis hodgeEigenvalue a
    rw [ha]
    change (hodgeEigenvalue a : ℂ) • coclosedHilbertBasis a =
      ((coreCurl (coreCurl (coreBasis a)) : Core) : coclosedField)
    rw [coreCurl_basis, map_smul, coreCurl_basis, smul_smul]
    simp only [hodgeEigenvalue, pow_two, Complex.ofReal_mul,
      Submodule.coe_smul, coreBasis, FiniteEigenbasisCore.finiteBasis_coe]
  exact LinearMap.congr_fun h x

/-- The second-order core is obtained by two genuine differential
applications on the same field, including the intermediate domain. -/
theorem finiteHodge_is_twice_curl (x : Core) :
    (finiteHodge x : OneFormL2) =
      closedCurl (coreToCurlDomain (coreCurl x)) := by
  rw [coreCurl_is_differential]
  exact congrArg (fun A : coclosedField => A.val) (finiteHodge_core x)

def closedHodge : coclosedField →ₗ.[ℂ] coclosedField := finiteHodge.closure

theorem closedHodge_selfAdjoint : IsSelfAdjoint closedHodge :=
  FiniteEigenbasisCore.closure_selfAdjoint coclosedHilbertBasis hodgeEigenvalue

theorem closedHodge_unique (S : coclosedField →ₗ.[ℂ] coclosedField)
    (hS : IsSelfAdjoint S) (hcore : finiteHodge ≤ S) : S = closedHodge :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique coclosedHilbertBasis
    hodgeEigenvalue S hS hcore

theorem closedHodge_domain (A : coclosedField) :
    A ∈ closedHodge.domain ↔
      Summable (fun a : CoclosedIndex => eigenvalue a.val ^ 4 *
        ‖inner ℂ (coclosedHilbertBasis a) A‖ ^ 2) := by
  simpa only [closedHodge, finiteHodge, hodgeEigenvalue, ← pow_mul,
    Nat.reduceMul] using
    FiniteEigenbasisCore.closure_domain_iff_summable
      coclosedHilbertBasis hodgeEigenvalue A

end GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
