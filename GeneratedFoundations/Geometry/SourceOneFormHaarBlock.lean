module

public import GeneratedFoundations.Geometry.SourceOneFormHodgeBlock
public import GeneratedFoundations.Geometry.SourceQuotientHilbert

/-!
# Isometric one-form synthesis in the original quotient Haar space

Every source-degree row is embedded by its actual normalized matrix
coefficients. The map is an isometry because Schur orthogonality has already
been proved for the complete quotient Haar basis. All three frame components
are retained. The pointwise differential intertwining is proved for the same
continuous matrix coefficients, before transferring the norm estimate.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceOneFormSpectralCore
open GeneratedFoundations.Geometry.SourceCoclosedDifferentialBlock
open GeneratedFoundations.Geometry.SourceOneFormHodgeBlock

namespace GeneratedFoundations.Geometry.SourceOneFormHaarBlock

abbrev OneFormL2 := PiLp 2 (fun _ : Fin 3 => QuotientL2)

instance oneFormL2Inner : InnerProductSpace ℂ OneFormL2 :=
  PiLp.innerProductSpace (fun _ : Fin 3 => QuotientL2)

def rowLinear {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    HilbertCarrier m →ₗ[ℂ] QuotientL2 :=
  (sourceBasis m).toBasis.constr ℂ
    (fun j => quotientBasisVector ⟨⟨m, i, j⟩, hm⟩)

@[simp] theorem rowLinear_basis {m : ℕ} (hm : Even m) (i j : Fin (m + 1)) :
    rowLinear hm i (sourceBasis m j) = quotientBasisVector ⟨⟨m, i, j⟩, hm⟩ :=
  (sourceBasis m).toBasis.constr_basis ℂ _ j

theorem row_image_orthonormal {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    Orthonormal ℂ ((rowLinear hm i) ∘ (sourceBasis m).toBasis) := by
  have hi : Function.Injective (fun j : Fin (m + 1) =>
      (⟨⟨m, i, j⟩, hm⟩ : EvenIndex)) := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun a : EvenIndex => a.val.2.2.val) h
  have h := quotientBasisVector_orthonormal.comp _ hi
  have heq : ((rowLinear hm i) ∘ (sourceBasis m).toBasis) =
      quotientBasisVector ∘ (fun j : Fin (m + 1) =>
        (⟨⟨m, i, j⟩, hm⟩ : EvenIndex)) := by
    funext j
    exact rowLinear_basis hm i j
  rw [heq]
  exact h

def rowIsometry {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    HilbertCarrier m →ₗᵢ[ℂ] QuotientL2 :=
  (rowLinear hm i).isometryOfOrthonormal
    (v := (sourceBasis m).toBasis)
    (by simpa only [OrthonormalBasis.coe_toBasis] using (sourceBasis m).orthonormal)
    (row_image_orthonormal hm i)

@[simp] theorem rowIsometry_basis {m : ℕ} (hm : Even m) (i j : Fin (m + 1)) :
    rowIsometry hm i (sourceBasis m j) = quotientBasisVector ⟨⟨m, i, j⟩, hm⟩ :=
  rowLinear_basis hm i j

def matrixCoefficientLinear (m : ℕ) (v : HilbertCarrier m) :
    HilbertCarrier m →ₗ[ℂ] C(SU2, ℂ) where
  toFun a := matrixCoefficient m v a
  map_add' a b := by
    apply ContinuousMap.ext
    intro U
    simp only [matrixCoefficient_apply, map_add, inner_add_right, ContinuousMap.add_apply]
  map_smul' c a := by
    apply ContinuousMap.ext
    intro U
    simp only [matrixCoefficient_apply, map_smul, ContinuousMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    exact inner_smul_right v ((unitaryAction m U) a) c

def sourceRowLinear (m : ℕ) (i : Fin (m + 1)) : HilbertCarrier m →ₗ[ℂ] SourceL2 :=
  normalization m • ((ContinuousMap.toLp 2 sourceHaar ℂ).toLinearMap.comp
    (matrixCoefficientLinear m (sourceBasis m i)))

/-- The isometric row map is the Haar class of the original continuous
matrix coefficient, with its derived Schur normalization. -/
theorem pullback_rowIsometry {m : ℕ} (hm : Even m) (i : Fin (m + 1))
    (a : HilbertCarrier m) :
    pullbackL2 (rowIsometry hm i a) =
      normalization m • ContinuousMap.toLp 2 sourceHaar ℂ
        (matrixCoefficient m (sourceBasis m i) a) := by
  have h : pullbackL2.toLinearMap.comp (rowLinear hm i) = sourceRowLinear m i := by
    apply (sourceBasis m).toBasis.ext
    intro j
    change pullbackL2 (rowLinear hm i (sourceBasis m j)) =
      normalization m • ContinuousMap.toLp 2 sourceHaar ℂ
        (matrixCoefficient m (sourceBasis m i) (sourceBasis m j))
    rw [rowLinear_basis, pullbackL2_basisVector]
    rfl
  exact LinearMap.congr_fun h a

def frameRowLinear {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    FrameCarrier m →ₗ[ℂ] OneFormL2 where
  toFun A := WithLp.toLp 2 (fun r => rowIsometry hm i (A r))
  map_add' A B := by
    apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
    funext r
    exact map_add (rowIsometry hm i) (A r) (B r)
  map_smul' c A := by
    apply (WithLp.equiv 2 (Fin 3 → QuotientL2)).injective
    funext r
    exact map_smul (rowIsometry hm i) c (A r)

theorem frameRowLinear_inner {m : ℕ} (hm : Even m) (i : Fin (m + 1))
    (A B : FrameCarrier m) :
    inner ℂ (frameRowLinear hm i A) (frameRowLinear hm i B) = inner ℂ A B := by
  simp only [PiLp.inner_apply, frameRowLinear, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometry.inner_map_map]

def frameRowIsometry {m : ℕ} (hm : Even m) (i : Fin (m + 1)) :
    FrameCarrier m →ₗᵢ[ℂ] OneFormL2 :=
  (frameRowLinear hm i).isometryOfInner (frameRowLinear_inner hm i)

/-- A continuous representative of this very Haar field. -/
def normalizedSynthesis (m : ℕ) (i : Fin (m + 1)) (A : FrameCarrier m) : SourceOneForm :=
  coefficientForm m (sourceBasis m i) ((normalization m) • (fun r => A r))

theorem curl_normalizedSynthesis (m : ℕ) (i : Fin (m + 1)) (A : FrameCarrier m) :
    curl (normalizedSynthesis m i A) = normalizedSynthesis m i (curlOperator m A) := by
  rw [normalizedSynthesis, curl_coefficientForm, coefficientCurl_smul]
  rfl

theorem coclosed_Haar_norm_sq_ge_four {m : ℕ} (hm : Even m) (i : Fin (m + 1))
    (A : coclosedSpace m) :
    4 * ‖frameRowIsometry hm i (A : FrameCarrier m)‖ ^ 2 ≤
      ‖frameRowIsometry hm i (curlOperator m (A : FrameCarrier m))‖ ^ 2 := by
  rw [(frameRowIsometry hm i).norm_map, (frameRowIsometry hm i).norm_map]
  exact coclosedCurl_norm_sq_ge_four hm A

end GeneratedFoundations.Geometry.SourceOneFormHaarBlock
