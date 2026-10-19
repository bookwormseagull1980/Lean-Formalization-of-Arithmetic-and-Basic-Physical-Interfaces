module

public import GeneratedFoundations.Geometry.SourceOneFormCurlBranches

/-!
# Complete nongauge spectrum in the original Haar field space

The weak divergence kernel is closed in the already constructed field
Hilbert space. Nonzero eigenvectors of the differentiated curl belong to
this kernel. Conversely, every zero-curl row is an actual gradient, so its
inner product with a coclosed field vanishes. These two differential facts
prove that the nonzero curl eigenfields form a complete orthonormal basis
of the original coclosed field space.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap lp
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock
open GeneratedFoundations.Geometry.SourceOneFormHodgeBlock
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum
open GeneratedFoundations.Geometry.SourceOneFormClosedHodge
open GeneratedFoundations.Geometry.SourceOneFormLowestCurl
open GeneratedFoundations.Geometry.SourceOneFormCurlBranches
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum

attribute [local irreducible] curlBasis curlEigenvalue

instance coclosedFieldNormed : NormedAddCommGroup coclosedField :=
  Submodule.normedAddCommGroup coclosedField

instance coclosedFieldInner : InnerProductSpace ℂ coclosedField :=
  Submodule.innerProductSpace coclosedField

instance coclosedFieldComplete : CompleteSpace coclosedField :=
  coclosedField_isClosed.isComplete.completeSpace_coe

abbrev CoclosedIndex := {a : CurlIndex // eigenvalue a ≠ 0}

theorem eigenfield_mem_domain (a : CurlIndex) : eigenfield a ∈ closedCurl.domain :=
  row_mem_closedCurl a.1 (curlBasis a.1.1.val a.2)

theorem closedCurl_eigenfield (a : CurlIndex) :
    closedCurl ⟨eigenfield a, eigenfield_mem_domain a⟩ =
      (eigenvalue a : ℂ) • eigenfield a := by
  exact (closedCurl_row a.1 (curlBasis a.1.1.val a.2)).trans
    ((congrArg (blockEmbedding a.1) (curlBasis_eigenvector a.1.1.val a.2)).trans
      ((blockEmbedding a.1).map_smul (eigenvalue a : ℂ) (curlBasis a.1.1.val a.2)))

theorem eigenfield_coclosed (a : CoclosedIndex) : eigenfield a.val ∈ coclosedField := by
  have h := closedCurl_coclosed ⟨eigenfield a.val, eigenfield_mem_domain a.val⟩
  rw [closedCurl_eigenfield] at h
  have hc : (eigenvalue a.val : ℂ) ≠ 0 := by exact_mod_cast a.property
  have hh := coclosedField.smul_mem ((eigenvalue a.val : ℂ)⁻¹) h
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

def coclosedEigenfield (a : CoclosedIndex) : coclosedField :=
  ⟨eigenfield a.val, eigenfield_coclosed a⟩

theorem coclosedEigenfield_orthonormal : Orthonormal ℂ coclosedEigenfield := by
  rw [orthonormal_iff_ite]
  intro a b
  change inner ℂ (eigenfield a.val) (eigenfield b.val) = _
  rw [orthonormal_iff_ite.mp eigenfield_orthonormal]
  simp only [Subtype.val_inj]

theorem zero_mode_inner_coclosed (a : CurlIndex) (ha : eigenvalue a = 0)
    (A : coclosedField) : inner ℂ (eigenfield a) A.val = 0 := by
  have hker : curlBasis a.1.1.val a.2 ∈ LinearMap.ker (curlOperator a.1.1.val) := by
    change curlOperator a.1.1.val (curlBasis a.1.1.val a.2) = 0
    rw [curlBasis_eigenvector]
    have hz : curlEigenvalue a.1.1.val a.2 = 0 := ha
    rw [hz, Complex.ofReal_zero]
    exact zero_smul ℂ (curlBasis a.1.1.val a.2)
  rw [curl_kernel_eq_gradient_range a.1.1.property] at hker
  obtain ⟨v, hv⟩ := hker
  rw [eigenfield, inner_blockEmbedding, ← hv, gradient_divergence_pairing]
  have hdiv := (mem_coclosedField A.val).mp A.property a.1
  rw [hdiv, inner_zero_right, neg_zero]

def finiteCoclosedCore : Submodule ℂ coclosedField :=
  Submodule.span ℂ (Set.range coclosedEigenfield)

theorem finiteCoclosedCore_orthogonal : finiteCoclosedCoreᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  have hnonzero (a : CoclosedIndex) : inner ℂ (eigenfield a.val) A.val = 0 :=
    (finiteCoclosedCore.mem_orthogonal A).mp hA (coclosedEigenfield a)
      (Submodule.subset_span (Set.mem_range_self a))
  have hall (a : CurlIndex) : inner ℂ (eigenfield a) A.val = 0 := by
    by_cases ha : eigenvalue a = 0
    · exact zero_mode_inner_coclosed a ha A
    · exact hnonzero ⟨a, ha⟩
  change A = 0
  apply Subtype.ext
  apply curlHilbertBasis.repr.injective
  apply lp.ext
  funext a
  simp only [HilbertBasis.repr_apply_apply, curlHilbertBasis_apply,
    hall, Submodule.coe_zero, inner_zero_right]

def coclosedHilbertBasis : HilbertBasis CoclosedIndex ℂ coclosedField :=
  HilbertBasis.mkOfOrthogonalEqBot coclosedEigenfield_orthonormal
    finiteCoclosedCore_orthogonal

@[simp] theorem coclosedHilbertBasis_apply (a : CoclosedIndex) :
    coclosedHilbertBasis a = coclosedEigenfield a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    coclosedEigenfield_orthonormal finiteCoclosedCore_orthogonal) a

theorem coclosed_eigenvalue_sq_ge_four (a : CoclosedIndex) :
    4 ≤ eigenvalue a.val ^ 2 := by
  obtain ⟨l, _, hl, hvalue⟩ := every_nongauge_field_mode_has_odd_degree a.val a.property
  rw [hvalue]
  have hreal : (1 : ℝ) ≤ l := by exact_mod_cast hl
  nlinarith

end GeneratedFoundations.Geometry.SourceOneFormCoclosedSpectrum
