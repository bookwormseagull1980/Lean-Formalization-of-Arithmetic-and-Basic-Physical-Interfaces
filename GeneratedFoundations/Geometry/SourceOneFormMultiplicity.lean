module

public import GeneratedFoundations.Geometry.SourceOneFormCurlBranches
public import Mathlib.Analysis.InnerProductSpace.Trace

/-!
# Multiplicities of the differentiated one-form branches

The trace is computed in the original three-component Haar metric. Its
diagonal entries are obtained from the differentiated curl, not from a
proposed spectrum. The gradient kernel and the two possible nonzero
eigenvalues then determine the branch multiplicities.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceOneFormHodgeBlock
open GeneratedFoundations.Geometry.SourceOneFormCurlBranches

namespace GeneratedFoundations.Geometry.SourceOneFormMultiplicity

attribute [local irreducible] curlBasis

def componentBasis (m : ℕ) :
    OrthonormalBasis (Σ _ : Fin 3, Fin (m + 1)) ℂ (FrameCarrier m) :=
  Pi.orthonormalBasis (fun _ : Fin 3 => sourceBasis m)

theorem component_diagonal (m : ℕ) (i : Fin 3) (j : Fin (m + 1)) :
    inner ℂ (PiLp.single 2 i (sourceBasis m j))
      (curlOperator m (PiLp.single 2 i (sourceBasis m j))) = 2 := by
  have hnorm : ‖((sourceBasis m j : HilbertCarrier m) : OrbitL2 m)‖ = 1 :=
    (sourceBasis m).norm_eq_one j
  fin_cases i <;>
    simp [PiLp.inner_apply, Fin.sum_univ_three, curlOperator_apply, coefficientCurl,
      PiLp.single_apply, inner_smul_right, hnorm]

theorem curl_trace (m : ℕ) :
    LinearMap.trace ℂ (FrameCarrier m) (curlOperator m) = 6 * (m + 1) := by
  rw [LinearMap.trace_eq_sum_inner _ (componentBasis m)]
  simp only [componentBasis, Pi.orthonormalBasis_apply, component_diagonal, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  push_cast
  ring

theorem sum_curlEigenvalue (m : ℕ) :
    ∑ j, curlEigenvalue m j = 6 * ((m : ℝ) + 1) := by
  have h := (curlOperator_symmetric m).re_trace_eq_sum_eigenvalues
    (frameCarrier_finrank m)
  change RCLike.re (LinearMap.trace ℂ (FrameCarrier m) (curlOperator m)) =
    ∑ j, curlEigenvalue m j at h
  rw [← h, curl_trace]
  change (6 * ((m : ℂ) + 1)).re = _
  simp

theorem gradient_injective {m : ℕ} (hm : m ≠ 0) :
    Function.Injective (gradientOperator m) := by
  rw [← LinearMap.ker_eq_bot]
  ext a
  change (gradientOperator m a = 0) ↔ a = 0
  constructor
  · intro ha
    have h := divergence_gradient m a
    rw [ha, map_zero] at h
    have hc : (m : ℂ) * ((m : ℂ) + 2) ≠ 0 := by
      have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
      have hpos : (0 : ℝ) < (m : ℝ) * ((m : ℝ) + 2) := by positivity
      exact_mod_cast ne_of_gt hpos
    exact (smul_eq_zero.mp (neg_eq_zero.mp h.symm)).resolve_left hc
  · rintro rfl
    exact map_zero _

def zeroMultiplicity (m : ℕ) : ℕ :=
  Fintype.card {j : Fin (3 * (m + 1)) // curlEigenvalue m j = 0}

def plusMultiplicity (m : ℕ) : ℕ :=
  Fintype.card {j : Fin (3 * (m + 1)) // curlEigenvalue m j = (m : ℝ) + 2}

def minusMultiplicity (m : ℕ) : ℕ :=
  Fintype.card {j : Fin (3 * (m + 1)) // curlEigenvalue m j = -(m : ℝ)}

theorem zeroMultiplicity_eq {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    zeroMultiplicity m = m + 1 := by
  have h := (curlOperator_symmetric m).card_filter_eigenvalues_eq
    (frameCarrier_finrank m) (0 : ℂ)
  change (Finset.univ.filter (fun j => (curlEigenvalue m j : ℂ) = 0)).card = _ at h
  simp only [Complex.ofReal_eq_zero] at h
  rw [Module.End.eigenspace_zero, curl_kernel_eq_gradient_range hm,
    LinearMap.finrank_range_of_inj (gradient_injective hm0), hilbertCarrier_finrank] at h
  simpa only [zeroMultiplicity, Fintype.card_subtype] using h

private theorem count_as_sum (m : ℕ) (c : ℝ) :
    (Fintype.card {j : Fin (3 * (m + 1)) // curlEigenvalue m j = c} : ℝ) =
      ∑ j : Fin (3 * (m + 1)), if curlEigenvalue m j = c then 1 else 0 := by
  classical
  simp [Fintype.card_subtype, Finset.sum_boole]

theorem branch_count_sum {m : ℕ} (hm0 : m ≠ 0) :
    zeroMultiplicity m + plusMultiplicity m + minusMultiplicity m = 3 * (m + 1) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hpoint (j : Fin (3 * (m + 1))) :
      (if curlEigenvalue m j = 0 then (1 : ℝ) else 0) +
        (if curlEigenvalue m j = (m : ℝ) + 2 then 1 else 0) +
        (if curlEigenvalue m j = -(m : ℝ) then 1 else 0) = 1 := by
    rcases curlEigenvalue_branches m j with hzero | hplus | hminus
    · have hp : curlEigenvalue m j ≠ (m : ℝ) + 2 := by linarith
      have hn : curlEigenvalue m j ≠ -(m : ℝ) := by linarith
      rw [ite_eq_left hzero, ite_eq_right hp, ite_eq_right hn]
      norm_num
    · have hz : curlEigenvalue m j ≠ 0 := by linarith
      have hn : curlEigenvalue m j ≠ -(m : ℝ) := by linarith
      rw [ite_eq_right hz, ite_eq_left hplus, ite_eq_right hn]
      norm_num
    · have hz : curlEigenvalue m j ≠ 0 := by linarith
      have hp : curlEigenvalue m j ≠ (m : ℝ) + 2 := by linarith
      rw [ite_eq_right hz, ite_eq_right hp, ite_eq_left hminus]
      norm_num
  have hs := congrArg (fun f : Fin (3 * (m + 1)) → ℝ => ∑ j, f j) (funext hpoint)
  simp only [Finset.sum_add_distrib] at hs
  rw [← count_as_sum m 0, ← count_as_sum m ((m : ℝ) + 2),
    ← count_as_sum m (-(m : ℝ))] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hs
  apply Nat.cast_injective (R := ℝ)
  simpa only [zeroMultiplicity, plusMultiplicity, minusMultiplicity,
    Nat.cast_add] using hs

theorem branch_weighted_sum {m : ℕ} (hm0 : m ≠ 0) :
    ((m : ℝ) + 2) * plusMultiplicity m -
      (m : ℝ) * minusMultiplicity m = 6 * ((m : ℝ) + 1) := by
  classical
  have hmpos : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hpoint (j : Fin (3 * (m + 1))) : curlEigenvalue m j =
      ((m : ℝ) + 2) * (if curlEigenvalue m j = (m : ℝ) + 2 then 1 else 0) -
        (m : ℝ) * (if curlEigenvalue m j = -(m : ℝ) then 1 else 0) := by
    rcases curlEigenvalue_branches m j with hzero | hplus | hminus <;>
      split_ifs <;> simp_all <;> linarith
  have hs := congrArg (fun f : Fin (3 * (m + 1)) → ℝ => ∑ j, f j) (funext hpoint)
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  rw [← count_as_sum m ((m : ℝ) + 2), ← count_as_sum m (-(m : ℝ)),
    sum_curlEigenvalue] at hs
  exact hs.symm

/-- Both branch dimensions follow from the actual differential trace and
the gradient kernel; they are not assigned representation dimensions. -/
theorem nonconstant_branch_multiplicities {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    plusMultiplicity m = m + 3 ∧ minusMultiplicity m = m - 1 := by
  have hcount := branch_count_sum hm0
  rw [zeroMultiplicity_eq hm hm0] at hcount
  have hcount' : (plusMultiplicity m : ℝ) + minusMultiplicity m =
      2 * ((m : ℝ) + 1) := by exact_mod_cast (by omega :
        plusMultiplicity m + minusMultiplicity m = 2 * (m + 1))
  have htrace := branch_weighted_sum hm0
  have hmul : 2 * ((m : ℝ) + 1) *
      ((plusMultiplicity m : ℝ) - ((m : ℝ) + 3)) = 0 := by
    linear_combination htrace + (m : ℝ) * hcount'
  have hp : (plusMultiplicity m : ℝ) = (m : ℝ) + 3 :=
    sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (by positivity))
  have hp' : plusMultiplicity m = m + 3 := by exact_mod_cast hp
  exact ⟨hp', by omega⟩

theorem degree_zero_eigenvalue (j : Fin (3 * (0 + 1))) :
    curlEigenvalue 0 j = 2 := by
  have hcurl : curlOperator 0 (curlBasis 0 j) = (2 : ℂ) • curlBasis 0 j := by
    apply (WithLp.equiv 2 (Fin 3 → HilbertCarrier 0)).injective
    exact coefficientCurl_degree_zero (fun i => curlBasis 0 j i)
  have h := congrArg (fun A : FrameCarrier 0 => inner ℂ (curlBasis 0 j) A)
    (hcurl.symm.trans (curlBasis_eigenvector 0 j))
  change inner ℂ (curlBasis 0 j) ((2 : ℂ) • curlBasis 0 j) =
    inner ℂ (curlBasis 0 j) ((curlEigenvalue 0 j : ℂ) • curlBasis 0 j) at h
  have hunit : inner ℂ (curlBasis 0 j) (curlBasis 0 j) = 1 := by
    simpa only [ite_true] using (orthonormal_iff_ite.mp (curlBasis 0).orthonormal j j)
  have htwo := inner_smul_right (curlBasis 0 j) (curlBasis 0 j) (2 : ℂ)
  have heigen := inner_smul_right (curlBasis 0 j) (curlBasis 0 j)
    (curlEigenvalue 0 j : ℂ)
  rw [htwo, heigen, hunit, mul_one, mul_one] at h
  exact_mod_cast h.symm

theorem constant_branch_multiplicities :
    zeroMultiplicity 0 = 0 ∧ plusMultiplicity 0 = 3 := by
  simp [zeroMultiplicity, plusMultiplicity, degree_zero_eigenvalue]

theorem eigenspace_dimension (m : ℕ) (c : ℝ) :
    Module.finrank ℂ (Module.End.eigenspace (curlOperator m) (c : ℂ)) =
      Fintype.card {j : Fin (3 * (m + 1)) // curlEigenvalue m j = c} := by
  have h := (curlOperator_symmetric m).card_filter_eigenvalues_eq
    (frameCarrier_finrank m) (c : ℂ)
  change (Finset.univ.filter
    (fun j => (curlEigenvalue m j : ℂ) = (c : ℂ))).card = _ at h
  simpa only [Complex.ofReal_inj, Fintype.card_subtype] using h.symm

/-- The positive branch is present with all of its differential
polarizations, including the three constant-frame directions at degree zero. -/
theorem positive_eigenspace_finrank {m : ℕ} (hm : Even m) :
    Module.finrank ℂ (Module.End.eigenspace (curlOperator m) (((m : ℝ) + 2 : ℝ) : ℂ)) =
      m + 3 := by
  rw [eigenspace_dimension]
  change plusMultiplicity m = m + 3
  by_cases hm0 : m = 0
  · subst m
    exact constant_branch_multiplicities.2
  · exact (nonconstant_branch_multiplicities hm hm0).1

theorem negative_eigenspace_finrank {m : ℕ} (hm : Even m) (hm0 : m ≠ 0) :
    Module.finrank ℂ (Module.End.eigenspace (curlOperator m) ((-(m : ℝ) : ℝ) : ℂ)) =
      m - 1 := by
  rw [eigenspace_dimension]
  exact (nonconstant_branch_multiplicities hm hm0).2

end GeneratedFoundations.Geometry.SourceOneFormMultiplicity
