module

public import GeneratedFoundations.Geometry.SourceOneFormSpectralCore
public import Mathlib.Analysis.InnerProductSpace.Subspace

/-!
# Coclosed subspaces of the generated exterior differential

Coclosedness is imposed by the divergence computed from the source curves.
Curl preserves this kernel by the proved exterior-differential identity.
Its restriction is symmetric in the existing Haar inner product. We apply
the finite spectral theorem only after these facts have been established.

On every even source degree, the resulting eigenvalues have squared modulus
at least four. Hence the same lower bound holds for every coclosed vector in
the block, including all its frame components. The estimate is a consequence
of the differential commutators and projective parity; it is not an assumed
property of a diagonal multiplier.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore

namespace GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock

def divergenceOperator (m : ℕ) : FrameCarrier m →ₗ[ℂ] HilbertCarrier m where
  toFun A := coefficientDivergence m (fun i => A i)
  map_add' A B := by
    simp [coefficientDivergence, map_add, Finset.sum_add_distrib]
  map_smul' c A := by
    simp [coefficientDivergence, map_smul, Finset.smul_sum]

/-- The kernel of the actual source divergence on the full frame block. -/
def coclosedSpace (m : ℕ) : Submodule ℂ (FrameCarrier m) :=
  LinearMap.ker (divergenceOperator m)

instance coclosedSpaceNormed (m : ℕ) : NormedAddCommGroup (coclosedSpace m) := by
  exact Submodule.normedAddCommGroup (𝕜 := ℂ) (E := FrameCarrier m)
    (by exact coclosedSpace m)

instance coclosedSpaceInner (m : ℕ) : InnerProductSpace ℂ (coclosedSpace m) := by
  exact Submodule.innerProductSpace (𝕜 := ℂ) (E := FrameCarrier m)
    (by exact coclosedSpace m)

@[simp] theorem mem_coclosedSpace (m : ℕ) (A : FrameCarrier m) :
    A ∈ coclosedSpace m ↔ coefficientDivergence m (fun i => A i) = 0 := Iff.rfl

theorem curl_preserves_coclosed (m : ℕ) (A : FrameCarrier m)
    (_hA : A ∈ coclosedSpace m) : curlOperator m A ∈ coclosedSpace m := by
  exact coefficientDivergence_curl_zero m (fun i => A i)

def coclosedCurl (m : ℕ) : coclosedSpace m →ₗ[ℂ] coclosedSpace m :=
  (curlOperator m).restrict (curl_preserves_coclosed m)

theorem coclosedCurl_symmetric (m : ℕ) :
    LinearMap.IsSymmetric (𝕜 := ℂ) (E := coclosedSpace m) (coclosedCurl m) :=
  (curlOperator_symmetric m).restrict_invariant (curl_preserves_coclosed m)

def coclosedBasis (m : ℕ) :
    OrthonormalBasis (Fin (Module.finrank ℂ (coclosedSpace m))) ℂ (coclosedSpace m) :=
  (coclosedCurl_symmetric m).eigenvectorBasis rfl

def coclosedEigenvalue (m : ℕ)
    (j : Fin (Module.finrank ℂ (coclosedSpace m))) : ℝ :=
  (coclosedCurl_symmetric m).eigenvalues rfl j

theorem coclosedBasis_eigenvector (m : ℕ)
    (j : Fin (Module.finrank ℂ (coclosedSpace m))) :
    coclosedCurl m (coclosedBasis m j) =
      (coclosedEigenvalue m j : ℂ) • coclosedBasis m j :=
  (coclosedCurl_symmetric m).apply_eigenvectorBasis rfl j

/-- This lower bound concerns eigenvalues produced by the differential
operator, rather than eigenvalues supplied to construct it. -/
theorem coclosedEigenvalue_sq_ge_four {m : ℕ} (hm : Even m)
    (j : Fin (Module.finrank ℂ (coclosedSpace m))) :
    4 ≤ coclosedEigenvalue m j ^ 2 := by
  let A := coclosedBasis m j
  have hA : (fun i => (A : FrameCarrier m) i) ≠ 0 := by
    intro hzero
    apply (coclosedBasis m).orthonormal.ne_zero j
    apply Subtype.ext
    apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier m)).injective
    exact hzero
  have hdiv : coefficientDivergence m (fun i => (A : FrameCarrier m) i) = 0 :=
    A.property
  have hcurl :
      coefficientCurl m (fun i => (A : FrameCarrier m) i) =
        (coclosedEigenvalue m j : ℂ) • (fun i => (A : FrameCarrier m) i) := by
    have h := congrArg (fun x : coclosedSpace m => fun i => (x : FrameCarrier m) i)
      (coclosedBasis_eigenvector m j)
    exact h
  exact coclosed_curl_eigenvalue_sq_ge_four hm (coclosedEigenvalue m j)
    (fun i => (A : FrameCarrier m) i) hA hdiv hcurl

-- Subsequent norm arguments use the proved basis and eigenvector identities.
-- Keeping the finite spectral construction folded prevents elaboration from
-- reopening its choice of orthonormal eigenvectors inside scalar inequalities.
attribute [irreducible] coclosedBasis coclosedEigenvalue

theorem coclosedBasis_inner_curl (m : ℕ) (A : coclosedSpace m)
    (j : Fin (Module.finrank ℂ (coclosedSpace m))) :
    inner ℂ (coclosedBasis m j) (coclosedCurl m A) =
      (coclosedEigenvalue m j : ℂ) * inner ℂ (coclosedBasis m j) A := by
  calc
    _ = inner ℂ (coclosedCurl m (coclosedBasis m j)) A :=
      ((coclosedCurl_symmetric m) (coclosedBasis m j) A).symm
    _ = inner ℂ ((coclosedEigenvalue m j : ℂ) • coclosedBasis m j) A :=
      congrArg (fun x : coclosedSpace m => inner ℂ x A)
        (coclosedBasis_eigenvector m j)
    _ = conj (coclosedEigenvalue m j : ℂ) * inner ℂ (coclosedBasis m j) A :=
      inner_smul_left (coclosedBasis m j) A (coclosedEigenvalue m j : ℂ)
    _ = _ := congrArg (fun c : ℂ => c * inner ℂ (coclosedBasis m j) A)
      (Complex.conj_ofReal (coclosedEigenvalue m j))

/-- Uniform coercivity on the entire coclosed differential block. -/
theorem coclosedCurl_norm_sq_ge_four {m : ℕ} (hm : Even m)
    (A : coclosedSpace m) : 4 * ‖A‖ ^ 2 ≤ ‖coclosedCurl m A‖ ^ 2 := by
  have hcoordinate (j : Fin (Module.finrank ℂ (coclosedSpace m))) :
      4 * ‖inner ℂ (coclosedBasis m j) A‖ ^ 2 ≤
        ‖inner ℂ (coclosedBasis m j) (coclosedCurl m A)‖ ^ 2 := by
    rw [coclosedBasis_inner_curl m A j, norm_mul, mul_pow]
    have hc : ‖(coclosedEigenvalue m j : ℂ)‖ ^ 2 = coclosedEigenvalue m j ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_right (coclosedEigenvalue_sq_ge_four hm j)
      (sq_nonneg ‖inner ℂ (coclosedBasis m j) A‖)).trans_eq
        (congrArg (fun t : ℝ => t * ‖inner ℂ (coclosedBasis m j) A‖ ^ 2) hc.symm)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun j _ => hcoordinate j)
  have hleft : (∑ j, 4 * ‖inner ℂ (coclosedBasis m j) A‖ ^ 2) = 4 * ‖A‖ ^ 2 :=
    (Finset.mul_sum Finset.univ
      (fun j => ‖inner ℂ (coclosedBasis m j) A‖ ^ 2) (4 : ℝ)).symm.trans
        (congrArg (fun t : ℝ => 4 * t) ((coclosedBasis m).sum_sq_norm_inner_right A))
  exact (hleft.symm.le.trans hsum).trans_eq
    ((coclosedBasis m).sum_sq_norm_inner_right (coclosedCurl m A))

end GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock
