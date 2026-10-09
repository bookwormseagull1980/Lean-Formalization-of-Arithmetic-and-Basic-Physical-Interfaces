module

public import GeneratedFoundations.Geometry.SourceCoefficientDensity
public import GeneratedFoundations.Geometry.SourceSchurOrthogonality
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Complete matrix coefficients of the actual source group

The vectors are the continuous matrix entries of the previously constructed
unitary source representations, viewed in the original probability-Haar
space. Schur orthogonality determines their normalization. Their density
comes from the actual source-coordinate algebra and the explicit
Clebsch–Gordan decomposition.

An arbitrary polynomial-representation coefficient is expanded in the
existing finite orthonormal source basis. This connects the algebraic
density theorem to these very matrix entries before the Hilbert basis is
constructed. No separate representation or coefficient-space completeness
is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricPowers
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCoefficientProducts

namespace GeneratedFoundations.Geometry.SourceCompleteCoefficients

abbrev SourceL2 := Lp ℂ 2 sourceHaar

/-- Both matrix indices are retained in every homogeneous degree. -/
abbrev Index := Σ m : ℕ, Fin (m + 1) × Fin (m + 1)

def entry (m : ℕ) (i j : Fin (m + 1)) : SourceL2 :=
  ContinuousMap.toLp 2 sourceHaar ℂ (matrixEntry m i j)

def normalization (m : ℕ) : ℂ := (Real.sqrt ((m + 1 : ℕ) : ℝ) : ℂ)

@[simp] theorem normalization_conj (m : ℕ) : conj (normalization m) = normalization m := by
  simp [normalization]

theorem normalization_square (m : ℕ) :
    normalization m * normalization m = ((m + 1 : ℕ) : ℂ) := by
  simp only [normalization]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg (m + 1)),
    Complex.ofReal_natCast]

theorem normalization_ne_zero (m : ℕ) : normalization m ≠ 0 := by
  have hpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
  exact Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hpos).ne'

def basisVector (a : Index) : SourceL2 :=
  normalization a.1 • entry a.1 a.2.1 a.2.2

theorem entry_inner_same (m : ℕ) (i j k l : Fin (m + 1)) :
    inner ℂ (entry m i j) (entry m k l) =
      if i = k ∧ j = l then (((m + 1 : ℕ) : ℂ))⁻¹ else 0 := by
  rw [entry, entry, ContinuousMap.inner_toLp]
  simpa only [mul_comm] using matrixEntry_integral_same m i j k l

theorem entry_inner_of_ne {m n : ℕ} (hmn : m ≠ n)
    (i j : Fin (m + 1)) (k l : Fin (n + 1)) :
    inner ℂ (entry m i j) (entry n k l) = 0 := by
  rw [entry, entry, ContinuousMap.inner_toLp]
  simpa only [mul_comm] using matrixEntry_integral_of_ne hmn i j k l

theorem basisVector_inner_same (m : ℕ) (i j k l : Fin (m + 1)) :
    inner ℂ (basisVector ⟨m, i, j⟩) (basisVector ⟨m, k, l⟩) =
      if i = k ∧ j = l then 1 else 0 := by
  have hd : ((m + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  simp only [basisVector, inner_smul_left, inner_smul_right,
    normalization_conj, entry_inner_same]
  split_ifs
  · rw [← mul_assoc, normalization_square, mul_inv_cancel₀ hd]
  · simp only [mul_zero]

theorem basisVector_inner_of_ne {m n : ℕ} (hmn : m ≠ n)
    (i j : Fin (m + 1)) (k l : Fin (n + 1)) :
    inner ℂ (basisVector ⟨m, i, j⟩) (basisVector ⟨n, k, l⟩) = 0 := by
  simp only [basisVector, inner_smul_left, inner_smul_right,
    entry_inner_of_ne hmn, mul_zero]

theorem basisVector_orthonormal : Orthonormal ℂ basisVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨m, i, j⟩ ⟨n, k, l⟩
  by_cases hmn : m = n
  · subst n
    rw [basisVector_inner_same]
    by_cases hik : i = k <;> by_cases hjl : j = l <;> simp [hik, hjl]
  · have hab : (⟨m, i, j⟩ : Index) ≠ ⟨n, k, l⟩ := by
      intro hab
      exact hmn (congrArg Sigma.fst hab)
    rw [ite_eq_right hab]
    exact basisVector_inner_of_ne hmn i j k l

/-- The full matrix-coefficient block retains both row and column indices. -/
def blockSpace (m : ℕ) : Submodule ℂ SourceL2 :=
  Submodule.span ℂ (Set.range (fun ij : Fin (m + 1) × Fin (m + 1) =>
    basisVector ⟨m, ij⟩))

/-- This is the dimension of an actual function subspace, independently of
the later identification of the differential Casimir. -/
theorem blockSpace_finrank (m : ℕ) : Module.finrank ℂ (blockSpace m) = (m + 1) ^ 2 := by
  have hinj : Function.Injective (fun ij : Fin (m + 1) × Fin (m + 1) =>
      (⟨m, ij⟩ : Index)) := by
    intro i j hij
    cases hij
    rfl
  have hon := basisVector_orthonormal.comp
    (fun ij : Fin (m + 1) × Fin (m + 1) => (⟨m, ij⟩ : Index)) hinj
  have hd := finrank_span_eq_card hon.linearIndependent
  simp only [Function.comp_def, Fintype.card_prod, Fintype.card_fin] at hd
  exact hd.trans (pow_two (m + 1)).symm

def entrySpan : Submodule ℂ SourceL2 := Submodule.span ℂ (Set.range basisVector)

theorem entry_mem_span (m : ℕ) (i j : Fin (m + 1)) : entry m i j ∈ entrySpan := by
  have hb : basisVector ⟨m, i, j⟩ ∈ entrySpan := Submodule.subset_span ⟨⟨m, i, j⟩, rfl⟩
  have hs := entrySpan.smul_mem (normalization m)⁻¹ hb
  simpa only [basisVector, smul_smul, inv_mul_cancel₀ (normalization_ne_zero m), one_smul]
    using hs

private theorem functional_expansion (m : ℕ) (ψ : HilbertCarrier m →ₗ[ℂ] ℂ)
    (x : HilbertCarrier m) :
    ψ x = ∑ i : Fin (m + 1), inner ℂ (sourceBasis m i) x * ψ (sourceBasis m i) := by
  conv_lhs => rw [← (sourceBasis m).sum_repr' x]
  simp only [map_sum, map_smul, smul_eq_mul]

private theorem orbit_coefficient_expansion (m : ℕ) (i : Fin (m + 1))
    (a : HilbertCarrier m) (U : SU2) :
    inner ℂ (sourceBasis m i) (unitaryAction m U a) =
      ∑ j : Fin (m + 1), inner ℂ (sourceBasis m j) a * matrixEntry m i j U := by
  conv_lhs => rw [← (sourceBasis m).sum_repr' a]
  simp only [map_sum, map_smul, inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact inner_smul_right (sourceBasis m i) (unitaryAction m U (sourceBasis m j)) _

/-- The dual functional and orbit vector use the same existing Hilbert
realization. This finite identity is independent of the later density proof. -/
theorem coefficient_expansion (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) :
    coefficient m φ v =
      ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
        (φ ((carrierEquiv m).symm (sourceBasis m i)) *
          inner ℂ (sourceBasis m j) (carrierEquiv m v)) • matrixEntry m i j := by
  let ψ : HilbertCarrier m →ₗ[ℂ] ℂ := φ.comp (carrierEquiv m).symm.toLinearMap
  ext U
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul, coefficient_apply]
  have hsource : φ (sourceRepresentation m U v) = ψ (unitaryAction m U (carrierEquiv m v)) := by
    simp only [unitaryAction_apply_carrier, ψ, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [hsource, functional_expansion]
  apply Finset.sum_congr rfl
  intro i hi
  rw [orbit_coefficient_expansion, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  change (inner ℂ (sourceBasis m j) (carrierEquiv m v) * matrixEntry m i j U) *
    φ ((carrierEquiv m).symm (sourceBasis m i)) = _
  ring

theorem coefficient_toLp_mem_span (m : ℕ) (φ : Carrier m →ₗ[ℂ] ℂ) (v : Carrier m) :
    ContinuousMap.toLp 2 sourceHaar ℂ (coefficient m φ v) ∈ entrySpan := by
  rw [coefficient_expansion, map_sum]
  apply entrySpan.sum_mem
  intro i hi
  rw [map_sum]
  apply entrySpan.sum_mem
  intro j hj
  rw [map_smul]
  exact entrySpan.smul_mem _ (entry_mem_span m i j)

theorem coefficientSpan_toLp_mem_span {f : C(SU2, ℂ)} (hf : f ∈ coefficientSpan) :
    ContinuousMap.toLp 2 sourceHaar ℂ f ∈ entrySpan := by
  change f ∈ Submodule.span ℂ coefficientGenerators at hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨m, φ, v, rfl⟩ := hf
      exact coefficient_toLp_mem_span m φ v
  | zero => simpa only [map_zero] using entrySpan.zero_mem
  | add f g _ _ hf hg => rw [map_add]; exact entrySpan.add_mem hf hg
  | smul c f _ hf => rw [map_smul]; exact entrySpan.smul_mem c hf

/-- Completeness is proved in the entire original probability-Haar space. -/
theorem matrixCoefficients_dense : Dense (entrySpan : Set SourceL2) := by
  apply Dense.mono _ SourceCoefficientDensity.coefficientSpan_toLp_dense
  rintro _ ⟨f, rfl⟩
  exact coefficientSpan_toLp_mem_span f.property

theorem matrixCoefficients_complete : entrySpan.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp matrixCoefficients_dense

def basis : HilbertBasis Index ℂ SourceL2 :=
  HilbertBasis.mk basisVector_orthonormal (by rw [← matrixCoefficients_complete]; exact le_rfl)

@[simp] theorem basis_apply (a : Index) : basis a = basisVector a :=
  congrFun (HilbertBasis.coe_mk basisVector_orthonormal
    (by rw [← matrixCoefficients_complete]; exact le_rfl)) a

/-- The coefficient sequence is obtained after the all-degree completeness proof. -/
def coefficients : SourceL2 ≃ₗᵢ[ℂ] ℓ²(Index, ℂ) := basis.repr

theorem coefficients_apply (f : SourceL2) (a : Index) :
    coefficients f a = inner ℂ (basisVector a) f := by
  exact basis.repr_apply_apply f a |>.trans (by rw [basis_apply])

theorem coefficients_norm (f : SourceL2) : ‖coefficients f‖ = ‖f‖ :=
  coefficients.norm_map f

theorem hasSum_expansion (f : SourceL2) :
    HasSum (fun a : Index => inner ℂ (basisVector a) f • basisVector a) f := by
  simpa only [HilbertBasis.repr_apply_apply, basis_apply] using basis.hasSum_repr f

theorem eq_of_coefficients_eq {f g : SourceL2}
    (hfg : ∀ a : Index, inner ℂ (basisVector a) f = inner ℂ (basisVector a) g) : f = g := by
  apply coefficients.injective
  apply lp.ext
  funext a
  simpa only [coefficients_apply] using hfg a

end GeneratedFoundations.Geometry.SourceCompleteCoefficients
