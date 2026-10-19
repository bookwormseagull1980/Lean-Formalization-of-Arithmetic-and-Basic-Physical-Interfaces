module

public import GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
public import GeneratedFoundations.Geometry.SourceOneFormMultiplicity
public import GeneratedFoundations.Operations.SpectralFormLowerBound

/-!
# Differential Hodge energy and its exact lower edge

The quadratic form is evaluated in the original coclosed Haar field metric.
On the dense field core it is the squared norm of the differentiated curl.
On the full closed domain Parseval carries the same lower bound, and a
degree-zero source field realizes the lower edge. No shell is omitted in
either statement.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate LinearPMap
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormLowestCurl
open GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Geometry.SourceOneFormMultiplicity
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormHodgeEnergy

theorem coreCurl_formal (A B : Core) :
    inner ℂ (coreCurl A : coclosedField) (B : coclosedField) =
      inner ℂ (A : coclosedField) (coreCurl B : coclosedField) := by
  have hs : closedCurl.IsFormalAdjoint closedCurl := by
    have h := LinearPMap.adjoint_isFormalAdjoint closedCurl_selfAdjoint.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp closedCurl_selfAdjoint] at h
  have h := hs (coreToCurlDomain A) (coreToCurlDomain B)
  rw [coreCurl_is_differential, coreCurl_is_differential,
    coreToCurlDomain_val, coreToCurlDomain_val] at h
  exact h

/-- The Hodge quadratic form is obtained by differentiating the same field;
its spectral diagonalization does not define a different energy. -/
theorem finiteHodge_energy (A : Core) :
    (inner ℂ (A : coclosedField) (finiteHodge A)).re =
      ‖(coreCurl A : coclosedField)‖ ^ 2 := by
  rw [finiteHodge_core]
  change (inner ℂ (A : coclosedField)
    (coreCurl (coreCurl A) : coclosedField)).re = _
  rw [← coreCurl_formal A (coreCurl A)]
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) (coreCurl A : coclosedField)).symm

/-- The exact coefficient sum on the full closed Hodge domain. -/
theorem closedHodge_energy_sum (A : closedHodge.domain) :
    HasSum (fun a : CoclosedIndex =>
      hodgeEigenvalue a * ‖inner ℂ (coclosedHilbertBasis a) (A : coclosedField)‖ ^ 2)
      (inner ℂ (A : coclosedField) (closedHodge A)).re :=
  SpectralFormLowerBound.hasSum_quadratic coclosedHilbertBasis hodgeEigenvalue A

theorem closedHodge_coercive (A : closedHodge.domain) :
    4 * ‖(A : coclosedField)‖ ^ 2 ≤
      (inner ℂ (A : coclosedField) (closedHodge A)).re :=
  SpectralFormLowerBound.closed_quadratic_lower_bound coclosedHilbertBasis
    hodgeEigenvalue 4 coclosed_eigenvalue_sq_ge_four A

/-- A nonzero mode at the bottom, taken from the actual constant-frame
source block. Its curl eigenvalue was computed by differentiation. -/
def lowestIndex : CoclosedIndex :=
  ⟨⟨lowestRow, 0⟩, by
    change curlEigenvalue 0 0 ≠ 0
    rw [degree_zero_eigenvalue]
    norm_num⟩

theorem hodgeEigenvalue_lowest : hodgeEigenvalue lowestIndex = 4 := by
  change curlEigenvalue 0 0 ^ 2 = 4
  rw [degree_zero_eigenvalue]
  norm_num

theorem lowest_mem_domain : coclosedHilbertBasis lowestIndex ∈ closedHodge.domain :=
  (FiniteEigenbasisCore.le_closure coclosedHilbertBasis hodgeEigenvalue).1
    (FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis hodgeEigenvalue lowestIndex)

theorem closedHodge_lowest :
    closedHodge ⟨coclosedHilbertBasis lowestIndex, lowest_mem_domain⟩ =
      (4 : ℂ) • coclosedHilbertBasis lowestIndex := by
  have h := (FiniteEigenbasisCore.le_closure coclosedHilbertBasis hodgeEigenvalue).2
    (x := ⟨coclosedHilbertBasis lowestIndex,
      FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis hodgeEigenvalue lowestIndex⟩)
    (y := ⟨coclosedHilbertBasis lowestIndex, lowest_mem_domain⟩) rfl
  calc
    closedHodge ⟨coclosedHilbertBasis lowestIndex, lowest_mem_domain⟩ =
        finiteHodge ⟨coclosedHilbertBasis lowestIndex,
          FiniteEigenbasisCore.basis_mem_domain coclosedHilbertBasis
            hodgeEigenvalue lowestIndex⟩ := h.symm
    _ = (hodgeEigenvalue lowestIndex : ℂ) • coclosedHilbertBasis lowestIndex :=
      FiniteEigenbasisCore.basis_action coclosedHilbertBasis hodgeEigenvalue lowestIndex
    _ = (4 : ℂ) • coclosedHilbertBasis lowestIndex := by
      rw [hodgeEigenvalue_lowest]
      norm_num

end GeneratedFoundations.Geometry.SourceOneFormHodgeEnergy
