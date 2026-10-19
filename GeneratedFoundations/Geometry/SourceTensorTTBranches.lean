module

public import GeneratedFoundations.Geometry.SourceTensorTTBlock

/-!
# Spectral restrictions of the derived TT differential

The possible eigenvalues follow from the tensor differential identity.
Nonnegativity of the original connection energy excludes the spurious low
negative branch in degree two. The actual constant-degree differential
excludes the other low branch. Consequently the projective TT rough
operator has the degree-independent lower bound six on every block.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
open GeneratedFoundations.Geometry.SourceTensorSpectralCore
open GeneratedFoundations.Geometry.SourceTensorCurl
open GeneratedFoundations.Geometry.SourceTensorRoughIdentity
open GeneratedFoundations.Geometry.SourceTensorTTBlock

namespace GeneratedFoundations.Geometry.SourceTensorTTBranches

attribute [local irreducible] ttBasis ttCurlEigenvalue

theorem coefficients_ne_zero (m : ℕ) (H : ttSpace m) (hH : H ≠ 0) :
    coefficients m (H : TensorBlock m) ≠ 0 := by
  intro hz
  apply hH
  apply Subtype.ext
  apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
  funext ab
  exact congrFun (congrFun hz ab.1) ab.2

theorem tt_eigenvalue_cases (m : ℕ)
    (j : Fin (Module.finrank ℂ (ttSpace m))) :
    ttCurlEigenvalue m j = (m : ℝ) + 3 ∨
      ttCurlEigenvalue m j = 1 - (m : ℝ) := by
  have hn := coefficients_ne_zero m (ttBasis m j)
    ((ttBasis m).orthonormal.ne_zero j)
  have he : coefficientTensorCurl m
      (coefficients m ((ttBasis m j : ttSpace m) : TensorBlock m)) =
        (ttCurlEigenvalue m j : ℂ) •
          coefficients m ((ttBasis m j : ttSpace m) : TensorBlock m) := by
    exact congrArg (fun H : ttSpace m => coefficients m (H : TensorBlock m))
      (ttBasis_eigenvector m j)
  rcases tt_curl_eigenvalue m (ttCurlEigenvalue m j : ℂ) _
    (tt_property m (ttBasis m j)) hn he with hp | hn
  · left
    exact_mod_cast hp
  · right
    exact_mod_cast hn

theorem tt_rough_eigenvalue_nonnegative (m : ℕ)
    (j : Fin (Module.finrank ℂ (ttSpace m))) :
    0 ≤ ttCurlEigenvalue m j ^ 2 - 3 := by
  have hp := ttRough_nonnegative m (ttBasis m j)
  rw [ttBasis_rough_eigenvector] at hp
  have hi (r : ℝ) (H : ttSpace m) :
      inner ℂ H ((r : ℂ) • H) = (r : ℂ) * inner ℂ H H :=
    inner_smul_right H H (r : ℂ)
  have hself : inner ℂ (ttBasis m j) (ttBasis m j) = (1 : ℂ) :=
    inner_self_eq_one_of_norm_eq_one ((ttBasis m).norm_eq_one j)
  rw [hi, hself, mul_one, Complex.ofReal_re] at hp
  exact hp

theorem tensorCurl_degree_zero (H : TensorCoefficients 0)
    (hH : H ∈ ttCoefficients 0) :
    coefficientTensorCurl 0 H = (3 : ℂ) • H := by
  funext a b
  rw [curl_symmetric_tracefree 0 H hH.1 hH.2.1,
    coefficientCurl_degree_zero]
  change (2 : ℂ) • H a b + H a b = (3 : ℂ) • H a b
  module

theorem tt_eigenvalue_degree_zero
    (j : Fin (Module.finrank ℂ (ttSpace 0))) : ttCurlEigenvalue 0 j = 3 := by
  let H := coefficients 0 ((ttBasis 0 j : ttSpace 0) : TensorBlock 0)
  have he : coefficientTensorCurl 0 H = (ttCurlEigenvalue 0 j : ℂ) • H := by
    exact congrArg (fun K : ttSpace 0 => coefficients 0 (K : TensorBlock 0))
      (ttBasis_eigenvector 0 j)
  rw [tensorCurl_degree_zero H (tt_property 0 (ttBasis 0 j))] at he
  have hn : H ≠ 0 := coefficients_ne_zero 0 (ttBasis 0 j)
    ((ttBasis 0).orthonormal.ne_zero j)
  have h := (smul_left_injective ℂ hn he).symm
  exact_mod_cast h

/-- The bound uses actual differential positivity to remove the degree-two
lower branch; parity alone would not remove it. -/
theorem tt_rough_eigenvalue_ge_six {m : ℕ} (hm : Even m)
    (j : Fin (Module.finrank ℂ (ttSpace m))) :
    6 ≤ ttCurlEigenvalue m j ^ 2 - 3 := by
  by_cases hm0 : m = 0
  · subst m
    rw [tt_eigenvalue_degree_zero]
    norm_num
  have hm2 : 2 ≤ m := by
    obtain ⟨k, hk⟩ := hm
    omega
  rcases tt_eigenvalue_cases m j with hp | hn
  · rw [hp]
    have hmreal : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith
  · by_cases htwo : m = 2
    · subst m
      have h := tt_rough_eigenvalue_nonnegative 2 j
      rw [hn] at h
      norm_num at h
    · have hm4 : 4 ≤ m := by
        obtain ⟨k, hk⟩ := hm
        omega
      have hmreal : (4 : ℝ) ≤ m := by exact_mod_cast hm4
      rw [hn]
      nlinarith

end GeneratedFoundations.Geometry.SourceTensorTTBranches
