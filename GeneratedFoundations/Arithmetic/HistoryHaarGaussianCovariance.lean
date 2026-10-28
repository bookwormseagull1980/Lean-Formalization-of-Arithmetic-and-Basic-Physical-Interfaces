module

public import GeneratedFoundations.Arithmetic.HistoryHermitianContraction
public import GeneratedFoundations.Arithmetic.HistoryGaussianCovariance
public import GeneratedFoundations.Geometry.SourceProjectiveVolume
public import GeneratedFoundations.Geometry.SourceEndpointCasimir
public import GeneratedFoundations.Source.CanonicalRealization

/-!
# Isotropic covariance on the original three-direction Haar connection

The connection in `HistoryHaarSectionAction` has three source-geometric
directions. These are not the history-coordinate directions of the jet
connection in `HistoryGaussianCovariance`. Its real traceless fibre has
`d^2-1` independent generators in the complete trace metric.

The canonical correlation radius and measured projective volume are taken
from the common source geometry. The comparison is normalized by the already calculated unit
susceptibility. In this explicitly isotropic, unit-intensity comparison
class, these data determine the full component covariance uniquely. Contractions use
the independent basis itself, before any scalar coefficient is extracted.

The unit-trace basis differs from a half-trace basis by `sqrt(2)`. The
coordinate covariance must transform inversely. Both factors are retained
in the comparison below. This module normalizes the isotropic local fibre;
its unit intensity is not identified with the spectral variance of the
original joint Hessian. The latter is constructed independently in
`HistoryHaarSectionCovariance`. Neither construction selects a bandwidth.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Matrix

namespace GeneratedFoundations.Arithmetic.HistoryHaarGaussianCovariance

open HistoryCliffordAction (Algebra)
open HistoryHermitianBasis (GeneratorIndex generator)

abbrev ComponentIndex (N : ℕ) := Fin 3 × GeneratorIndex N

def componentCount (N : ℕ) : ℕ := Fintype.card (ComponentIndex N)

theorem componentCount_eq (N : ℕ) :
    componentCount N = 3 * (HistoryAdjointCasimir.dimension N ^ 2 - 1) := by
  unfold componentCount
  rw [Fintype.card_prod, HistoryHermitianBasis.generator_count, Fintype.card_fin]

theorem componentCount_pos (N : ℕ) : 0 < componentCount N := by
  have hd := HistoryAdjointCasimir.dimension_ge_four N
  rw [componentCount_eq]
  have hs : 16 ≤ HistoryAdjointCasimir.dimension N ^ 2 := by nlinarith
  omega

theorem componentCount_cast (N : ℕ) :
    (componentCount N : ℝ) = 3 * ((HistoryAdjointCasimir.dimension N : ℝ) ^ 2 - 1) := by
  have hd := HistoryAdjointCasimir.dimension_ge_four N
  have hs : 1 ≤ HistoryAdjointCasimir.dimension N ^ 2 := by nlinarith
  rw [componentCount_eq, Nat.cast_mul, Nat.cast_sub hs, Nat.cast_pow]
  norm_num

/-- The root radius is fixed before any covariance or response is formed. -/
def sourceRadius : ℝ := Geometry.SourceEndpointCasimir.radius Source.CanonicalRealization.width

theorem sourceRadius_pos : 0 < sourceRadius :=
  Geometry.SourceEndpointCasimir.radius_pos Source.CanonicalRealization.width_pos

def sourceVolume : ℝ := Geometry.SourceProjectiveVolume.roundVolume sourceRadius

theorem sourceVolume_eq : sourceVolume = Real.pi ^ 2 * sourceRadius ^ 3 :=
  Geometry.SourceProjectiveVolume.roundVolume_eq sourceRadius

theorem sourceVolume_pos : 0 < sourceVolume :=
  Geometry.SourceProjectiveVolume.roundVolume_pos sourceRadius_pos

def unitIntensity (N : ℕ) : ℝ := HistoryGaussianCovariance.generatedIntensity N

theorem unitIntensity_eq (N : ℕ) : unitIntensity N = 1 :=
  HistoryGaussianCovariance.generatedIntensity_eq N

def componentVariance (N : ℕ) : ℝ :=
  unitIntensity N / ((componentCount N : ℝ) * sourceVolume)

theorem componentVariance_pos (N : ℕ) : 0 < componentVariance N := by
  unfold componentVariance
  rw [unitIntensity_eq]
  exact div_pos zero_lt_one (mul_pos (Nat.cast_pos.mpr (componentCount_pos N)) sourceVolume_pos)

theorem componentVariance_total (N : ℕ) :
    (componentCount N : ℝ) * componentVariance N = unitIntensity N / sourceVolume := by
  have hc : (componentCount N : ℝ) ≠ 0 := by
    exact_mod_cast (componentCount_pos N).ne'
  unfold componentVariance
  field_simp

theorem componentVariance_unique (N : ℕ) (v : ℝ)
    (hv : (componentCount N : ℝ) * v = unitIntensity N / sourceVolume) :
    v = componentVariance N := by
  have hc : (componentCount N : ℝ) ≠ 0 := by
    exact_mod_cast (componentCount_pos N).ne'
  have ht := componentVariance_total N
  exact mul_left_cancel₀ hc (hv.trans ht.symm)

def covariance (N : ℕ) : Matrix (ComponentIndex N) (ComponentIndex N) ℝ :=
  componentVariance N • 1

/-- Uniqueness concerns the entire covariance matrix, not one selected
diagonal entry. Isotropy specifies the comparison class explicitly. -/
theorem covariance_unique (N : ℕ)
    (C : Matrix (ComponentIndex N) (ComponentIndex N) ℝ)
    (hisotropic : ∃ v : ℝ, C = v • 1)
    (htotal : Matrix.trace C = unitIntensity N / sourceVolume) :
    C = covariance N := by
  obtain ⟨v, rfl⟩ := hisotropic
  have hv : (componentCount N : ℝ) * v = unitIntensity N / sourceVolume := by
    simpa only [Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, mul_comm,
      componentCount] using htotal
  rw [componentVariance_unique N v hv]
  rfl

def definingShift (N : ℕ) : ℝ :=
  3 * componentVariance N *
    ((HistoryAdjointCasimir.dimension N : ℝ) - (HistoryAdjointCasimir.dimension N : ℝ)⁻¹)

def definingContraction (N : ℕ) : Algebra N :=
  ∑ _i : Fin 3, ∑ a : GeneratorIndex N,
    (componentVariance N : ℂ) • (generator N a * generator N a)

theorem definingContraction_eq (N : ℕ) :
    definingContraction N = (definingShift N : ℂ) • (1 : Algebra N) := by
  simp only [definingContraction, ← Finset.smul_sum]
  change (componentVariance N : ℂ) •
    (∑ _i : Fin 3, HistoryHermitianContraction.squareSum N) = _
  rw [HistoryHermitianContraction.squareSum_eq]
  simp only [← Finset.sum_smul, smul_smul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  simp only [definingShift, Complex.ofReal_mul, Complex.ofReal_sub,
    Complex.ofReal_inv, Complex.ofReal_natCast, Complex.ofReal_ofNat]
  ring

/-- Covariance normalization cancels the apparent growth of the unweighted
defining Casimir. No dimension is replaced by a fixed colour rank. -/
theorem definingShift_eq (N : ℕ) :
    definingShift N = unitIntensity N /
      ((HistoryAdjointCasimir.dimension N : ℝ) * sourceVolume) := by
  have hd : (HistoryAdjointCasimir.dimension N : ℝ) ≠ 0 := by
    exact_mod_cast (HistoryAdjointCasimir.dimension_pos N).ne'
  have hg : (HistoryAdjointCasimir.dimension N : ℝ) ^ 2 - 1 ≠ 0 := by
    have h := componentCount_pos N
    have hr : 0 < (componentCount N : ℝ) := by exact_mod_cast h
    rw [componentCount_cast] at hr
    nlinarith
  unfold definingShift componentVariance
  rw [componentCount_cast]
  field_simp

theorem definingShift_pos (N : ℕ) : 0 < definingShift N := by
  rw [definingShift_eq, unitIntensity_eq]
  exact div_pos zero_lt_one
    (mul_pos (Nat.cast_pos.mpr (HistoryAdjointCasimir.dimension_pos N)) sourceVolume_pos)

def transverseShift (N : ℕ) : ℝ :=
  4 * componentVariance N * HistoryAdjointCasimir.dimension N

def transverseContraction (N : ℕ) (i : Fin 3) (X : Algebra N) : Algebra N :=
  ∑ _j ∈ Finset.univ.erase i,
    (componentVariance N : ℂ) • HistoryHermitianContraction.doubleCommutator N X

theorem transverseContraction_eq (N : ℕ) (i : Fin 3) (X : Algebra N) :
    transverseContraction N i X = (4 * (componentVariance N : ℂ)) •
      HistoryAdjointCasimir.casimir N X := by
  have hc : (Finset.univ.erase i).card = 2 := by simp
  unfold transverseContraction
  rw [HistoryHermitianContraction.doubleCommutator_eq_twice_adjoint,
    Finset.sum_const, hc]
  simp only [two_nsmul, smul_smul, ← add_smul]
  congr 1
  ring

theorem transverseContraction_traceless (N : ℕ) (i : Fin 3) (X : Algebra N)
    (hX : Matrix.trace X = 0) :
    transverseContraction N i X = (transverseShift N : ℂ) • X := by
  rw [transverseContraction_eq, HistoryAdjointCasimir.casimir_traceless N X hX, smul_smul]
  congr 1
  simp only [transverseShift, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_ofNat]

theorem transverseContraction_scalar (N : ℕ) (i : Fin 3) (c : ℂ) :
    transverseContraction N i (c • (1 : Algebra N)) = 0 := by
  rw [transverseContraction_eq]
  simp [HistoryAdjointCasimir.casimir, Operations.MatrixAdjointCasimir.casimir_scalar]

theorem transverseShift_pos (N : ℕ) : 0 < transverseShift N := by
  exact mul_pos (mul_pos (by norm_num) (componentVariance_pos N))
    (Nat.cast_pos.mpr (HistoryAdjointCasimir.dimension_pos N))

/-- The half-trace coordinate variance is twice the unit-trace variance.
The accompanying quadratic generator sum is half as large. -/
theorem halfTrace_normalization_cancels (N : ℕ) :
    ((2 * componentVariance N : ℝ) : ℂ) •
      ((1 / 2 : ℂ) • HistoryHermitianContraction.squareSum N) =
        (componentVariance N : ℂ) • HistoryHermitianContraction.squareSum N := by
  rw [smul_smul]
  congr 1
  push_cast
  ring

structure Conclusions : Prop where
  actual_component_count : ∀ N,
    componentCount N = 3 * (HistoryAdjointCasimir.dimension N ^ 2 - 1)
  canonical_volume_positive : 0 < sourceVolume
  source_unit_normalization : ∀ N, unitIntensity N = 1
  exact_total_intensity : ∀ N,
    (componentCount N : ℝ) * componentVariance N = unitIntensity N / sourceVolume
  unique_isotropic_covariance : ∀ N C, (∃ v : ℝ, C = v • 1) →
    Matrix.trace C = unitIntensity N / sourceVolume → C = covariance N
  full_defining_contraction : ∀ N,
    definingContraction N = (definingShift N : ℂ) • (1 : Algebra N)
  normalized_defining_response : ∀ N,
    definingShift N = unitIntensity N /
      ((HistoryAdjointCasimir.dimension N : ℝ) * sourceVolume)
  full_transverse_contraction : ∀ N i X,
    transverseContraction N i X = (4 * (componentVariance N : ℂ)) •
      HistoryAdjointCasimir.casimir N X

theorem generated : Conclusions where
  actual_component_count := componentCount_eq
  canonical_volume_positive := sourceVolume_pos
  source_unit_normalization := unitIntensity_eq
  exact_total_intensity := componentVariance_total
  unique_isotropic_covariance := covariance_unique
  full_defining_contraction := definingContraction_eq
  normalized_defining_response := definingShift_eq
  full_transverse_contraction := transverseContraction_eq

end GeneratedFoundations.Arithmetic.HistoryHaarGaussianCovariance
