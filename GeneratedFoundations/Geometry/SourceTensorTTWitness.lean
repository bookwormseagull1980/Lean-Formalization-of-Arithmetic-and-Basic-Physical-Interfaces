module

public import GeneratedFoundations.Geometry.SourceTensorTTBlock

/-!
# Actual polynomial witnesses for the TT upper branch

The highest binary homogeneous polynomial and the two transverse frame
directions give a symmetric trace-free tensor. The original source
derivatives prove its vanishing divergence and compute its tensor curl.
Thus every source degree has an actual nonzero TT field in the upper
branch. Neither a polarization table nor an assumed branch multiplicity
is used to supply these witnesses.
-/

@[expose] public section

noncomputable section

open Module
open scoped BigOperators
open GeneratedFoundations.Geometry.SourceSymmetricWeights
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceTensorCovariantDerivative
open GeneratedFoundations.Geometry.SourceTensorSpectralCore
open GeneratedFoundations.Geometry.SourceTensorCurl
open GeneratedFoundations.Geometry.SourceTensorTTBlock

namespace GeneratedFoundations.Geometry.SourceTensorTTWitness

def highest (m : ℕ) : HilbertCarrier m :=
  carrierEquiv m (mode m ⟨0, by omega⟩)

theorem highest_ne_zero (m : ℕ) : highest m ≠ 0 := by
  intro hz
  apply mode_ne_zero m ⟨0, by omega⟩
  apply (carrierEquiv m).injective
  simpa only [highest, map_zero] using hz

theorem highest_axis (m : ℕ) (i : Fin 3) :
    unitHilbertAxis m i (highest m) =
      carrierEquiv m (polynomialAxis m i (mode m ⟨0, by omega⟩)) := by
  rw [← polynomialAxis_transport, highest, hilbertOperator_apply]

theorem highest_transverse (m : ℕ) :
    unitHilbertAxis m 0 (highest m) =
      Complex.I • unitHilbertAxis m 1 (highest m) := by
  rw [highest_axis, highest_axis, ← map_smul]
  congr 1
  change Complex.I • ((raising m) (mode m ⟨0, by omega⟩) +
      (lowering m) (mode m ⟨0, by omega⟩)) =
    Complex.I • ((lowering m) (mode m ⟨0, by omega⟩) -
      (raising m) (mode m ⟨0, by omega⟩))
  rw [raising_mode_zero]
  module

theorem highest_axial (m : ℕ) :
    unitHilbertAxis m 2 (highest m) =
      (-Complex.I * (m : ℂ)) • highest m := by
  rw [highest_axis]
  simp [polynomialAxis, weightOperator_mode, highest, smul_smul]
  module

def witnessCoefficients (m : ℕ) : TensorCoefficients m :=
  ![![highest m, -Complex.I • highest m, 0],
    ![-Complex.I • highest m, -highest m, 0],
    ![0, 0, 0]]

theorem witness_symmetric (m : ℕ) (a b : Fin 3) :
    witnessCoefficients m a b = witnessCoefficients m b a := by
  fin_cases a <;> fin_cases b <;> rfl

theorem witness_trace (m : ℕ) :
    (∑ a : Fin 3, witnessCoefficients m a a) = 0 := by
  simp [witnessCoefficients, Fin.sum_univ_three]

theorem witness_transverse (m : ℕ) :
    SourceTensorCovariantDerivative.coefficientDivergence m (witnessCoefficients m) = 0 := by
  funext b
  rw [divergence_columns m _ (witness_symmetric m) b]
  fin_cases b <;>
    (simp [SourceOneFormDifferential.coefficientDivergence, witnessCoefficients,
      Fin.sum_univ_three, map_smul, map_neg, highest_transverse, smul_smul] <;> module)

theorem witness_mem (m : ℕ) : witnessCoefficients m ∈ ttCoefficients m :=
  ⟨witness_symmetric m, witness_trace m, witness_transverse m⟩

theorem witness_curl (m : ℕ) :
    coefficientTensorCurl m (witnessCoefficients m) =
      ((m : ℂ) + 3) • witnessCoefficients m := by
  funext a b
  rw [curl_symmetric_tracefree m _ (witness_symmetric m) (witness_trace m)]
  fin_cases a <;> fin_cases b <;>
    simp [coefficientCurl, witnessCoefficients, map_smul, map_neg, highest_axial,
      highest_transverse, smul_smul] <;>
      match_scalars <;> ring_nf <;> simp [Complex.I_sq, sub_eq_add_neg]

def witness (m : ℕ) : ttSpace m :=
  ⟨WithLp.toLp 2 (fun ab => witnessCoefficients m ab.1 ab.2), witness_mem m⟩

theorem witness_ne_zero (m : ℕ) : witness m ≠ 0 := by
  intro hz
  have h := congrArg (fun H : ttSpace m => (H : TensorBlock m) (0, 0)) hz
  exact highest_ne_zero m h

theorem witness_ttCurl (m : ℕ) :
    ttCurl m (witness m) = ((m : ℂ) + 3) • witness m := by
  apply Subtype.ext
  apply (WithLp.equiv 2 (Fin 3 × Fin 3 → HilbertCarrier m)).injective
  funext ab
  exact congrFun (congrFun (witness_curl m) ab.1) ab.2

theorem witness_ttRough (m : ℕ) :
    ttRough m (witness m) = (((m : ℂ) + 3) ^ 2 - 3) • witness m := by
  exact ttRough_of_curl_eigenvector m (witness m) ((m : ℂ) + 3) (witness_ttCurl m)

attribute [local irreducible] ttBasis ttCurlEigenvalue ttCurl ttRough witness

/-- Every upper branch is present in the spectrum obtained by diagonalizing
the actual tensor differential. Nonvanishing comes from the polynomial
witness, not from a proposed multiplicity formula. -/
theorem upper_branch_present (m : ℕ) :
    ∃ j : Fin (Module.finrank ℂ (ttSpace m)),
      ttCurlEigenvalue m j = (m : ℝ) + 3 := by
  have hmem : witness m ∈ Module.End.eigenspace (ttCurl m) ((m : ℂ) + 3) :=
    Module.End.mem_eigenspace_iff.mpr (witness_ttCurl m)
  have he : Module.End.HasEigenvalue (ttCurl m) ((m : ℂ) + 3) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, witness_ne_zero m⟩
  obtain ⟨j, hj⟩ := (ttCurl_symmetric m).exists_eigenvalues_eq rfl he
  refine ⟨j, ?_⟩
  have hvalue : (ttCurlEigenvalue m j : ℂ) = (m : ℂ) + 3 := by
    simpa only [ttCurlEigenvalue, RCLike.ofReal_eq_complex_ofReal] using hj
  exact_mod_cast hvalue

end GeneratedFoundations.Geometry.SourceTensorTTWitness
