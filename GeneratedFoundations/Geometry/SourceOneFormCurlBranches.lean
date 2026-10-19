module

public import GeneratedFoundations.Geometry.SourceOneFormLowestCurl

/-!
# Projective parity of the actual non-gauge differential spectrum

The eigenvalues here are the outputs of diagonalizing the differentiated
source curl. Applying the actual divergence to a nonzero eigenvector proves
coclosedness. The second-order differential identity then fixes both signed
branches. Projective parity forces their Hodge degree to be positive odd.
Thus no even-degree mode is inserted when the field operator is closed.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock
open GeneratedFoundations.Geometry.SourceOneFormHilbertSum
open GeneratedFoundations.Geometry.SourceOneFormCurlSpectrum

namespace GeneratedFoundations.Geometry.SourceOneFormCurlBranches

attribute [local irreducible] curlBasis curlEigenvalue

theorem nonzero_eigenvector_coclosed (m : ℕ) (j : Fin (3 * (m + 1)))
    (hc : curlEigenvalue m j ≠ 0) : curlBasis m j ∈ coclosedSpace m := by
  have hzero : divergenceOperator m (curlOperator m (curlBasis m j)) = 0 :=
    coefficientDivergence_curl_zero m (fun i => curlBasis m j i)
  rw [curlBasis_eigenvector, map_smul] at hzero
  have hcast : (curlEigenvalue m j : ℂ) ≠ 0 := by exact_mod_cast hc
  exact (smul_eq_zero.mp hzero).resolve_left hcast

theorem curlEigenvalue_branches (m : ℕ) (j : Fin (3 * (m + 1))) :
    curlEigenvalue m j = 0 ∨ curlEigenvalue m j = (m : ℝ) + 2 ∨
      curlEigenvalue m j = -(m : ℝ) := by
  by_cases hc : curlEigenvalue m j = 0
  · exact Or.inl hc
  · right
    have hA : (fun i => curlBasis m j i) ≠ (0 : Fin 3 → HilbertCarrier m) := by
      intro hzero
      apply (curlBasis m).orthonormal.ne_zero j
      apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
      exact hzero
    have hcurl : coefficientCurl m (fun i => curlBasis m j i) =
        (curlEigenvalue m j : ℂ) • (fun i => curlBasis m j i) :=
      congrArg (fun A : FrameCarrier m => fun i => A i) (curlBasis_eigenvector m j)
    rcases coclosed_curl_eigenvalue m (curlEigenvalue m j : ℂ)
      (fun i => curlBasis m j i) hA (nonzero_eigenvector_coclosed m j hc) hcurl with hp | hn
    · left
      exact_mod_cast hp
    · right
      exact_mod_cast hn

/-- Every nonzero projective curl mode has a positive odd Hodge degree;
the spectral parameter is obtained from its differentiated eigenvalue. -/
theorem nonzero_eigenvalue_has_odd_degree {m : ℕ} (hm : Even m)
    (j : Fin (3 * (m + 1))) (hc : curlEigenvalue m j ≠ 0) :
    ∃ l : ℕ, Odd l ∧ 1 ≤ l ∧ curlEigenvalue m j ^ 2 = ((l : ℝ) + 1) ^ 2 := by
  rcases curlEigenvalue_branches m j with hz | hp | hn
  · exact (hc hz).elim
  · refine ⟨m + 1, ?_, by omega, ?_⟩
    · obtain ⟨k, hk⟩ := hm
      refine ⟨k, ?_⟩
      omega
    · rw [hp]
      push_cast
      ring
  · have hm0 : m ≠ 0 := by
      intro hz
      subst m
      exact hc (by simpa using hn)
    have hm2 : 2 ≤ m := by
      obtain ⟨k, hk⟩ := hm
      omega
    refine ⟨m - 1, ?_, by omega, ?_⟩
    · obtain ⟨k, hk⟩ := hm
      refine ⟨k - 1, ?_⟩
      omega
    · rw [hn, neg_sq, Nat.cast_sub (by omega : 1 ≤ m)]
      push_cast
      ring

theorem every_nongauge_field_mode_has_odd_degree (a : CurlIndex)
    (hc : eigenvalue a ≠ 0) :
    ∃ l : ℕ, Odd l ∧ 1 ≤ l ∧ eigenvalue a ^ 2 = ((l : ℝ) + 1) ^ 2 :=
  nonzero_eigenvalue_has_odd_degree a.1.1.property a.2 hc

end GeneratedFoundations.Geometry.SourceOneFormCurlBranches
