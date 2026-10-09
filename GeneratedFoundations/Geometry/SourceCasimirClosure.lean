module

public import GeneratedFoundations.Geometry.SourceCompleteCoefficients
public import GeneratedFoundations.Geometry.SourceCoefficientDifferentiation
public import GeneratedFoundations.Geometry.SourceAxisMetric
public import GeneratedFoundations.Operations.FiniteEigenbasisCore

/-!
# The closed source Casimir on the original Haar space

Finite matrix-coefficient sums have continuous representatives on the actual
source group. Their second derivatives identify the finite coefficient
multiplier with the source Casimir. The closure is taken in the original
probability-Haar Hilbert space. Its domain and action are determined by the
complete matrix coefficients, and its self-adjoint extension is unique.

The eigenspaces retain both matrix indices. The eigenvalue classification
below concerns point spectrum; exclusion of continuous and residual spectrum
requires the subsequent resolvent construction.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate LinearPMap
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCoefficientDifferentiation
open GeneratedFoundations.Operations

namespace GeneratedFoundations.Geometry.SourceCasimirClosure

/-- The value already obtained from the actual three source derivatives. -/
def energy (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 2)

theorem energy_nonneg (m : ℕ) : 0 ≤ energy m := by
  unfold energy
  positivity

theorem energy_strictMono : StrictMono energy := by
  intro m n hmn
  have h : (m : ℝ) < (n : ℝ) := by exact_mod_cast hmn
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  unfold energy
  nlinarith

theorem energy_round_index (m : ℕ) : energy m = ((m + 1 : ℕ) : ℝ) ^ 2 - 1 := by
  simp only [energy, Nat.cast_add, Nat.cast_one]
  ring

def normalizedEntry (a : Index) : C(SU2, ℂ) :=
  normalization a.1 • matrixEntry a.1 a.2.1 a.2.2

theorem normalizedEntry_toLp (a : Index) :
    ContinuousMap.toLp 2 sourceHaar ℂ (normalizedEntry a) = basis a := by
  simp only [normalizedEntry, map_smul, basis_apply, basisVector, entry]

/-- Each finite Hilbert sum has this specific continuous representative. -/
def finiteRepresentative (c : Index →₀ ℂ) : C(SU2, ℂ) :=
  c.sum fun a z => z • normalizedEntry a

theorem finiteRepresentative_toLp (c : Index →₀ ℂ) :
    ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c) =
      FiniteEigenbasisCore.linearCombination basis c := by
  simp only [finiteRepresentative, Finsupp.sum, map_sum, map_smul,
    normalizedEntry_toLp, FiniteEigenbasisCore.linearCombination,
    Finsupp.linearCombination_apply]

/-- The continuous representative of the actual second-order expression. -/
def differentialRepresentative (c : Index →₀ ℂ) : C(SU2, ℂ) :=
  c.sum fun a z => z • ((energy a.1 : ℂ) • normalizedEntry a)

theorem differentialRepresentative_eq_casimir (c : Index →₀ ℂ) (g : SU2) :
    differentialRepresentative c g = sourceCasimir (finiteRepresentative c) g := by
  have hrep : (finiteRepresentative c : SU2 → ℂ) =
      fun U => ∑ a ∈ c.support, (c a * normalization a.1) *
        matrixCoefficient a.1 (sourceBasis a.1 a.2.1) (sourceBasis a.1 a.2.2) U := by
    funext U
    simp only [finiteRepresentative, Finsupp.sum, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, normalizedEntry, smul_eq_mul, matrixEntry, mul_assoc]
  rw [hrep, sourceCasimir_finset_matrixCoefficients]
  simp only [differentialRepresentative, Finsupp.sum, ContinuousMap.sum_apply,
    ContinuousMap.smul_apply, normalizedEntry, smul_eq_mul, matrixEntry, energy,
    Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  apply Finset.sum_congr rfl
  intro a ha
  ring

/-- The same expression uses the unit axes of the original trace metric. -/
theorem differentialRepresentative_eq_roundCasimir (c : Index →₀ ℂ) (g : SU2) :
    differentialRepresentative c g = SourceAxisMetric.roundCasimir (finiteRepresentative c) g := by
  rw [SourceAxisMetric.roundCasimir_eq_sourceCasimir]
  exact differentialRepresentative_eq_casimir c g

/-- This finite multiplier is identified with the actual differential
expression on every finite coefficient sum below. -/
def finiteCore : SourceL2 →ₗ.[ℂ] SourceL2 :=
  FiniteEigenbasisCore.finiteMultiplier basis (fun a => energy a.1)

theorem finiteRepresentative_mem_domain (c : Index →₀ ℂ) :
    ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c) ∈ finiteCore.domain := by
  rw [finiteRepresentative_toLp]
  exact FiniteEigenbasisCore.sum_mem_domain basis (fun a => energy a.1) c

theorem differentialRepresentative_toLp (c : Index →₀ ℂ) :
    ContinuousMap.toLp 2 sourceHaar ℂ (differentialRepresentative c) =
      finiteCore ⟨ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c),
        finiteRepresentative_mem_domain c⟩ := by
  have hx : (⟨ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c),
      finiteRepresentative_mem_domain c⟩ : finiteCore.domain) =
      ⟨FiniteEigenbasisCore.linearCombination basis c,
        FiniteEigenbasisCore.sum_mem_domain basis (fun a => energy a.1) c⟩ :=
    Subtype.ext (finiteRepresentative_toLp c)
  simp only [finiteCore] at hx ⊢
  rw [hx]
  rw [FiniteEigenbasisCore.finiteMultiplier_sum]
  simp only [differentialRepresentative, Finsupp.sum, map_sum, map_smul,
    normalizedEntry_toLp]

theorem finiteCore_continuous_representative (u : finiteCore.domain) :
    ∃! f : C(SU2, ℂ),
      ContinuousMap.toLp 2 sourceHaar ℂ f = (u : SourceL2) ∧
        ∃ c : Index →₀ ℂ, f = finiteRepresentative c := by
  obtain ⟨c, hc⟩ := FiniteEigenbasisCore.exists_linearCombination
    basis (fun a => energy a.1) u
  refine ⟨finiteRepresentative c, ⟨(finiteRepresentative_toLp c).trans hc, c, rfl⟩, ?_⟩
  intro f hf
  apply ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) sourceHaar
  exact hf.1.trans ((finiteRepresentative_toLp c).trans hc).symm

/-- Every vector in the finite core is acted on by the actual pointwise
second derivatives along the trace-unit source curves. -/
theorem finiteCore_is_roundCasimir (u : finiteCore.domain) :
    ∃ f h : C(SU2, ℂ),
      ContinuousMap.toLp 2 sourceHaar ℂ f = (u : SourceL2) ∧
      ContinuousMap.toLp 2 sourceHaar ℂ h = finiteCore u ∧
      ∀ g : SU2, h g = SourceAxisMetric.roundCasimir f g := by
  obtain ⟨c, hc⟩ := FiniteEigenbasisCore.exists_linearCombination
    basis (fun a => energy a.1) u
  have hr := (finiteRepresentative_toLp c).trans hc
  have hu : (⟨ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c),
      finiteRepresentative_mem_domain c⟩ : finiteCore.domain) = u := Subtype.ext hr
  refine ⟨finiteRepresentative c, differentialRepresentative c, hr, ?_,
    differentialRepresentative_eq_roundCasimir c⟩
  rw [differentialRepresentative_toLp, hu]

/-- Closure in the original source Haar Hilbert space. -/
def operator : SourceL2 →ₗ.[ℂ] SourceL2 := finiteCore.closure

theorem operator_selfAdjoint : IsSelfAdjoint operator :=
  FiniteEigenbasisCore.closure_selfAdjoint basis (fun a => energy a.1)

theorem selfAdjoint_extension_unique (T : SourceL2 →ₗ.[ℂ] SourceL2)
    (hT : IsSelfAdjoint T) (hcore : finiteCore ≤ T) : T = operator :=
  FiniteEigenbasisCore.selfAdjoint_extension_unique basis (fun a => energy a.1) T hT hcore

/-- The comparison is with every self-adjoint operator having the actual
second-order action on all finite source coefficients. -/
theorem selfAdjoint_extension_of_differential_identity (T : SourceL2 →ₗ.[ℂ] SourceL2)
    (hT : IsSelfAdjoint T)
    (hmem : ∀ c : Index →₀ ℂ,
      ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c) ∈ T.domain)
    (haction : ∀ c : Index →₀ ℂ,
      T ⟨ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c), hmem c⟩ =
        ContinuousMap.toLp 2 sourceHaar ℂ (differentialRepresentative c)) :
    T = operator := by
  apply selfAdjoint_extension_unique T hT
  constructor
  · intro f hf
    obtain ⟨c, hc⟩ := FiniteEigenbasisCore.exists_linearCombination
      basis (fun a => energy a.1) ⟨f, hf⟩
    have hr := (finiteRepresentative_toLp c).trans hc
    change ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c) = f at hr
    rw [← hr]
    exact hmem c
  · intro x y hxy
    obtain ⟨c, hc⟩ := FiniteEigenbasisCore.exists_linearCombination
      basis (fun a => energy a.1) x
    have hr := (finiteRepresentative_toLp c).trans hc
    have hx : (⟨ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c),
        finiteRepresentative_mem_domain c⟩ : finiteCore.domain) = x := Subtype.ext hr
    have hy : (⟨ContinuousMap.toLp 2 sourceHaar ℂ (finiteRepresentative c),
        hmem c⟩ : T.domain) = y := Subtype.ext (hr.trans hxy)
    rw [← hx, ← hy, haction]
    exact (differentialRepresentative_toLp c).symm

theorem operator_domain_iff (f : SourceL2) :
    f ∈ operator.domain ↔
      Summable (fun a : Index => energy a.1 ^ 2 * ‖inner ℂ (basisVector a) f‖ ^ 2) := by
  simpa only [operator, finiteCore, basis_apply] using
    FiniteEigenbasisCore.closure_domain_iff_summable basis (fun a => energy a.1) f

theorem operator_coefficients (f : operator.domain) (a : Index) :
    inner ℂ (basisVector a) (operator f) =
      (energy a.1 : ℂ) * inner ℂ (basisVector a) (f : SourceL2) := by
  simpa only [operator, finiteCore, basis_apply] using
    FiniteEigenbasisCore.closure_coefficients basis (fun a => energy a.1) f a

theorem basis_mem_domain (a : Index) : basisVector a ∈ operator.domain := by
  have hc := FiniteEigenbasisCore.basis_mem_domain basis (fun a => energy a.1) a
  have hle := FiniteEigenbasisCore.le_closure basis (fun a => energy a.1)
  simpa only [operator, finiteCore, basis_apply] using hle.1 hc

theorem operator_basis (a : Index) :
    operator ⟨basisVector a, basis_mem_domain a⟩ = (energy a.1 : ℂ) • basisVector a := by
  apply SourceCompleteCoefficients.eq_of_coefficients_eq
  intro b
  rw [operator_coefficients, inner_smul_right,
    orthonormal_iff_ite.mp basisVector_orthonormal]
  by_cases h : b = a
  · subst b
    rfl
  · simp only [h, ite_false, mul_zero]

/-- A nonzero eigenvector of the closed operator has one of the derived
source energies. No finite cutoff is imposed. -/
theorem eigenvalue_iff (z : ℂ) :
    (∃ f : operator.domain, (f : SourceL2) ≠ 0 ∧ operator f = z • (f : SourceL2)) ↔
      ∃ m : ℕ, z = (energy m : ℂ) := by
  constructor
  · rintro ⟨f, hf, he⟩
    have hnonzero : ∃ a : Index, inner ℂ (basisVector a) (f : SourceL2) ≠ 0 := by
      by_contra h
      push Not at h
      apply hf
      apply SourceCompleteCoefficients.eq_of_coefficients_eq
      intro a
      simpa only [inner_zero_right] using h a
    obtain ⟨a, ha⟩ := hnonzero
    refine ⟨a.1, ?_⟩
    have hc := operator_coefficients f a
    rw [he, inner_smul_right] at hc
    exact mul_right_cancel₀ ha hc
  · rintro ⟨m, rfl⟩
    let a : Index := ⟨m, 0, 0⟩
    exact ⟨⟨basisVector a, basis_mem_domain a⟩,
      basisVector_orthonormal.ne_zero a, operator_basis a⟩

theorem eigenvector_support_iff (m : ℕ) (f : operator.domain) :
    operator f = (energy m : ℂ) • (f : SourceL2) ↔
      ∀ a : Index, a.1 ≠ m → inner ℂ (basisVector a) (f : SourceL2) = 0 := by
  constructor
  · intro he a ham
    by_contra hc
    have h := operator_coefficients f a
    rw [he, inner_smul_right] at h
    have heq := Complex.ofReal_injective (mul_right_cancel₀ hc h)
    exact ham (energy_strictMono.injective heq).symm
  · intro hs
    apply SourceCompleteCoefficients.eq_of_coefficients_eq
    intro a
    rw [operator_coefficients, inner_smul_right]
    by_cases ham : a.1 = m
    · rw [ham]
    · rw [hs a ham, mul_zero, mul_zero]

def blockSum (m : ℕ) (f : SourceL2) : SourceL2 :=
  ∑ i : Fin (m + 1), ∑ j : Fin (m + 1),
    inner ℂ (basisVector ⟨m, i, j⟩) f • basisVector ⟨m, i, j⟩

theorem blockSum_mem (m : ℕ) (f : SourceL2) : blockSum m f ∈ blockSpace m := by
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.sum_mem
  intro j hj
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(i, j), rfl⟩

theorem blockSum_coefficients (m : ℕ) (f : SourceL2) (a : Index) :
    inner ℂ (basisVector a) (blockSum m f) =
      if a.1 = m then inner ℂ (basisVector a) f else 0 := by
  classical
  rcases a with ⟨n, i, j⟩
  by_cases hnm : n = m
  · subst n
    simp [blockSum, inner_sum, inner_smul_right, basisVector_inner_same, ite_and, mul_ite]
  · simp [blockSum, inner_sum, inner_smul_right, basisVector_inner_of_ne hnm, hnm]

theorem mem_blockSpace_iff (m : ℕ) (f : SourceL2) :
    f ∈ blockSpace m ↔
      ∀ a : Index, a.1 ≠ m → inner ℂ (basisVector a) f = 0 := by
  constructor
  · intro hf a ham
    induction hf using Submodule.span_induction with
    | mem v hv =>
        obtain ⟨⟨i, j⟩, rfl⟩ := hv
        exact basisVector_inner_of_ne ham _ _ i j
    | zero => exact inner_zero_right _
    | add u v _ _ hu hv => rw [inner_add_right, hu, hv, add_zero]
    | smul c v _ hv => rw [inner_smul_right, hv, mul_zero]
  · intro hf
    have he : f = blockSum m f := by
      apply SourceCompleteCoefficients.eq_of_coefficients_eq
      intro a
      rw [blockSum_coefficients]
      by_cases ham : a.1 = m
      · simp only [ham, ite_true]
      · simp only [ham, ite_false, hf a ham]
    rw [he]
    exact blockSum_mem m f

def shifted (z : ℂ) : operator.domain →ₗ[ℂ] SourceL2 :=
  operator.toFun - z • operator.domain.subtype

def eigenspace (z : ℂ) : Submodule ℂ SourceL2 :=
  (LinearMap.ker (shifted z)).map operator.domain.subtype

theorem mem_eigenspace_iff (z : ℂ) (f : SourceL2) :
    f ∈ eigenspace z ↔
      ∃ u : operator.domain, operator u = z • (u : SourceL2) ∧ (u : SourceL2) = f := by
  constructor
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, shifted, sub_eq_zero] using hu, huf⟩
  · rintro ⟨u, hu, huf⟩
    exact ⟨u, by simpa [LinearMap.mem_ker, shifted, sub_eq_zero] using hu, huf⟩

theorem eigenspace_eq_blockSpace (m : ℕ) : eigenspace (energy m : ℂ) = blockSpace m := by
  apply le_antisymm
  · intro f hf
    obtain ⟨u, hu, rfl⟩ := (mem_eigenspace_iff _ _).mp hf
    exact (mem_blockSpace_iff m _).mpr ((eigenvector_support_iff m u).mp hu)
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨i, j⟩, rfl⟩
    exact (mem_eigenspace_iff _ _).mpr
      ⟨⟨basisVector ⟨m, i, j⟩, basis_mem_domain _⟩, operator_basis _, rfl⟩

/-- The multiplicity is that of the actual closed source operator. -/
theorem eigenspace_finrank (m : ℕ) :
    Module.finrank ℂ (eigenspace (energy m : ℂ)) = (m + 1) ^ 2 := by
  rw [eigenspace_eq_blockSpace, blockSpace_finrank]

end GeneratedFoundations.Geometry.SourceCasimirClosure
