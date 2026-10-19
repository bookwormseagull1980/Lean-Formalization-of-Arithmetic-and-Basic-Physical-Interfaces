module

public import GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum

/-!
# Full-field coclosedness and coercivity of the source curl

Weak divergence is tested on every source matrix-coefficient row. These
tests are continuous in the original Haar field norm, so their common
kernel is a closed field subspace. The closed curl has the actual block
differential as its row coordinates. Consequently the differential lower
bound passes to every field in its full closed domain, without imposing
a finite cutoff or discarding a field component.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate LinearPMap lp
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock
open GeneratedFoundations.Geometry.SourceOneFormHaarBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum

namespace GeneratedFoundations.Geometry.SourceOneFormClosedHodge

attribute [local irreducible] curlBasis curlEigenvalue

theorem blockCoordinates_embedding (r : RowIndex) (B : FrameCarrier r.1.val) :
    blockCoordinates (blockEmbedding r B) = lp.single 2 r B := by
  classical
  apply blockCoordinates.symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact (completeHilbertSum.linearIsometryEquiv_symm_apply_single B).symm

theorem inner_blockEmbedding (r : RowIndex) (B : FrameCarrier r.1.val) (A : OneFormL2) :
    inner ℂ (blockEmbedding r B) A = inner ℂ B (blockCoordinates A r) := by
  classical
  calc
    _ = inner ℂ (blockCoordinates (blockEmbedding r B)) (blockCoordinates A) :=
      (blockCoordinates.inner_map_map (blockEmbedding r B) A).symm
    _ = inner ℂ (lp.single 2 r B) (blockCoordinates A) := by
      rw [blockCoordinates_embedding]
    _ = _ := lp.inner_single_left (𝕜 := ℂ)
      (G := fun s : RowIndex => FrameCarrier s.1.val) r B (blockCoordinates A)

theorem curlBasis_inner_curl (m : ℕ) (j : Fin (3 * (m + 1))) (A : FrameCarrier m) :
    inner ℂ (curlBasis m j) (curlOperator m A) =
      (curlEigenvalue m j : ℂ) * inner ℂ (curlBasis m j) A := by
  calc
    _ = inner ℂ (curlOperator m (curlBasis m j)) A :=
      ((curlOperator_symmetric m) (curlBasis m j) A).symm
    _ = inner ℂ ((curlEigenvalue m j : ℂ) • curlBasis m j) A :=
      congrArg (fun B : FrameCarrier m => inner ℂ B A) (curlBasis_eigenvector m j)
    _ = conj (curlEigenvalue m j : ℂ) * inner ℂ (curlBasis m j) A :=
      inner_smul_left (curlBasis m j) A (curlEigenvalue m j : ℂ)
    _ = _ := congrArg (fun c : ℂ => c * inner ℂ (curlBasis m j) A)
      (Complex.conj_ofReal (curlEigenvalue m j))

/-- The closed operator retains the differential on every source row. -/
theorem closedCurl_blockCoordinates (A : closedCurl.domain) (r : RowIndex) :
    blockCoordinates (closedCurl A) r = curlOperator r.1.val (blockCoordinates A.val r) := by
  apply (curlBasis r.1.val).repr.injective
  apply (WithLp.equiv 2 (Fin (3 * (r.1.val + 1)) → ℂ)).injective
  funext j
  change (curlBasis r.1.val).repr (blockCoordinates (closedCurl A) r) j =
    (curlBasis r.1.val).repr (curlOperator r.1.val (blockCoordinates A.val r)) j
  simp only [OrthonormalBasis.repr_apply_apply]
  calc
    _ = inner ℂ (eigenfield ⟨r, j⟩) (closedCurl A) :=
      (inner_blockEmbedding r (curlBasis r.1.val j) (closedCurl A)).symm
    _ = (eigenvalue ⟨r, j⟩ : ℂ) * inner ℂ (eigenfield ⟨r, j⟩) A.val :=
      closedCurl_coefficients A ⟨r, j⟩
    _ = (curlEigenvalue r.1.val j : ℂ) *
        inner ℂ (curlBasis r.1.val j) (blockCoordinates A.val r) := by
      rw [eigenfield, inner_blockEmbedding]
      rfl
    _ = _ := (curlBasis_inner_curl r.1.val j (blockCoordinates A.val r)).symm

def rowDivergence (r : RowIndex) : OneFormL2 →L[ℂ] HilbertCarrier r.1.val :=
  (divergenceOperator r.1.val).toContinuousLinearMap.comp
    ((lp.evalCLM ℂ (fun s : RowIndex => FrameCarrier s.1.val) 2 r).comp
      blockCoordinates.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem rowDivergence_apply (r : RowIndex) (A : OneFormL2) :
    rowDivergence r A = divergenceOperator r.1.val (blockCoordinates A r) := rfl

/-- The actual weak-divergence kernel in the complete quotient Haar space. -/
def coclosedField : Submodule ℂ OneFormL2 :=
  ⨅ r : RowIndex, LinearMap.ker (rowDivergence r).toLinearMap

theorem mem_coclosedField (A : OneFormL2) :
    A ∈ coclosedField ↔
      ∀ r : RowIndex, divergenceOperator r.1.val (blockCoordinates A r) = 0 := by
  simp only [coclosedField, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, rowDivergence_apply]

theorem coclosedField_isClosed : IsClosed (coclosedField : Set OneFormL2) := by
  simpa only [coclosedField, Submodule.coe_iInf] using
    isClosed_iInter (fun r : RowIndex => (rowDivergence r).isClosed_ker)

theorem closedCurl_coclosed (A : closedCurl.domain) : closedCurl A ∈ coclosedField := by
  rw [mem_coclosedField]
  intro r
  rw [closedCurl_blockCoordinates]
  exact SourceOneFormDifferential.coefficientDivergence_curl_zero r.1.val
    (fun i => (blockCoordinates A.val r) i)

/-- Parseval in the actual field norm, including all even degrees and rows. -/
theorem hasSum_row_norm_sq (A : OneFormL2) :
    HasSum (fun r : RowIndex => ‖blockCoordinates A r‖ ^ 2) (‖A‖ ^ 2) := by
  have h := lp.hasSum_norm (p := (2 : ENNReal)) (by norm_num) (blockCoordinates A)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] using h

/-- The spectral gap of the actual closed curl on the complete coclosed
field space follows from the differentiated source commutators. -/
theorem closedCurl_coclosed_coercivity (A : closedCurl.domain)
    (hA : A.val ∈ coclosedField) : 4 * ‖A.val‖ ^ 2 ≤ ‖closedCurl A‖ ^ 2 := by
  have hrows := (mem_coclosedField A.val).mp hA
  have hbound (r : RowIndex) :
      4 * ‖blockCoordinates A.val r‖ ^ 2 ≤ ‖blockCoordinates (closedCurl A) r‖ ^ 2 := by
    rw [closedCurl_blockCoordinates]
    exact coclosedCurl_norm_sq_ge_four r.1.property
      ⟨blockCoordinates A.val r, hrows r⟩
  exact hasSum_le hbound ((hasSum_row_norm_sq A.val).mul_left 4)
    (hasSum_row_norm_sq (closedCurl A))

theorem closedCurl_coclosed_kernel (A : closedCurl.domain)
    (hA : A.val ∈ coclosedField) (hcurl : closedCurl A = 0) : A.val = 0 := by
  have h := closedCurl_coclosed_coercivity A hA
  rw [hcurl, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at h
  have hz : ‖A.val‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖A.val‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hz)

end GeneratedFoundations.Geometry.SourceOneFormClosedHodge
