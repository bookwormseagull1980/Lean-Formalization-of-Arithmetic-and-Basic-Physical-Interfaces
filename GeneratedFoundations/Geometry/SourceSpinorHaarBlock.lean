module

public import GeneratedFoundations.Geometry.SourceSpinorMultiplicity
public import GeneratedFoundations.Geometry.SourceSpinorCovariantDerivative
public import GeneratedFoundations.Geometry.SourceOneFormHaarBlock

/-!
# Actual Haar spinor fields and their differentiated source blocks

The two spin coefficients are functions on the original source group.
Every homogeneous row is synthesized from the existing continuous matrix
coefficients, with the Schur normalization fixed by Haar integration.
Both central parities are retained here; their quotient restrictions will
be taken only after constructing the common differential operator.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped BigOperators ComplexConjugate lp
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceOneFormDifferential
open GeneratedFoundations.Geometry.SourceSpinorSpectralCore

namespace GeneratedFoundations.Geometry.SourceSpinorHaarBlock

abbrev SpinorL2 := PiLp 2 (fun _ : Fin 2 => SourceL2)

instance spinorL2Inner : InnerProductSpace ℂ SpinorL2 :=
  PiLp.innerProductSpace (fun _ : Fin 2 => SourceL2)

def scalarRowLinear (m : ℕ) (i : Fin (m + 1)) :
    HilbertCarrier m →ₗ[ℂ] SourceL2 :=
  SourceOneFormHaarBlock.sourceRowLinear m i

@[simp] theorem scalarRowLinear_basis (m : ℕ) (i j : Fin (m + 1)) :
    scalarRowLinear m i (sourceBasis m j) = basisVector ⟨m, i, j⟩ := rfl

theorem scalarRow_image_orthonormal (m : ℕ) (i : Fin (m + 1)) :
    Orthonormal ℂ ((scalarRowLinear m i) ∘ (sourceBasis m).toBasis) := by
  have hi : Function.Injective (fun j : Fin (m + 1) => (⟨m, i, j⟩ : Index)) := by
    intro j k h
    apply Fin.ext
    exact congrArg (fun a : Index => a.2.2.val) h
  have heq : ((scalarRowLinear m i) ∘ (sourceBasis m).toBasis) =
      basisVector ∘ (fun j : Fin (m + 1) => (⟨m, i, j⟩ : Index)) := by
    funext j
    exact scalarRowLinear_basis m i j
  rw [heq]
  exact basisVector_orthonormal.comp _ hi

def scalarRowIsometry (m : ℕ) (i : Fin (m + 1)) :
    HilbertCarrier m →ₗᵢ[ℂ] SourceL2 :=
  (scalarRowLinear m i).isometryOfOrthonormal
    (v := (sourceBasis m).toBasis)
    (by simpa only [OrthonormalBasis.coe_toBasis] using (sourceBasis m).orthonormal)
    (scalarRow_image_orthonormal m i)

@[simp] theorem scalarRowIsometry_basis (m : ℕ) (i j : Fin (m + 1)) :
    scalarRowIsometry m i (sourceBasis m j) = basisVector ⟨m, i, j⟩ :=
  scalarRowLinear_basis m i j

theorem scalarRow_original_representative (m : ℕ) (i : Fin (m + 1))
    (a : HilbertCarrier m) :
    scalarRowIsometry m i a = normalization m •
      ContinuousMap.toLp 2 sourceHaar ℂ
        (matrixCoefficient m (sourceBasis m i) a) := rfl

def spinRowLinear (m : ℕ) (i : Fin (m + 1)) :
    SpinorBlock m →ₗ[ℂ] SpinorL2 where
  toFun A := WithLp.toLp 2 (fun r => scalarRowIsometry m i (A r))
  map_add' A B := by
    apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
    exact funext fun r => map_add (scalarRowIsometry m i) (A r) (B r)
  map_smul' c A := by
    apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
    exact funext fun r => map_smul (scalarRowIsometry m i) c (A r)

theorem spinRowLinear_inner (m : ℕ) (i : Fin (m + 1)) (A B : SpinorBlock m) :
    inner ℂ (spinRowLinear m i A) (spinRowLinear m i B) = inner ℂ A B := by
  simp only [PiLp.inner_apply, spinRowLinear, LinearMap.coe_mk, AddHom.coe_mk,
    LinearIsometry.inner_map_map]

def spinRowIsometry (m : ℕ) (i : Fin (m + 1)) :
    SpinorBlock m →ₗᵢ[ℂ] SpinorL2 :=
  (spinRowLinear m i).isometryOfInner (spinRowLinear_inner m i)

abbrev SourceSpinor := Fin 2 → SU2 → ℂ

/-- Clifford contraction of the original source derivatives, including the
connection term computed from the metric Koszul formula. -/
def differential (F : SourceSpinor) : SourceSpinor := fun r g =>
  ![Complex.I * unitAxisDerivative 2 (F 0) g -
      Complex.I * unitAxisDerivative 0 (F 1) g + unitAxisDerivative 1 (F 1) g,
    -Complex.I * unitAxisDerivative 0 (F 0) g - unitAxisDerivative 1 (F 0) g -
      Complex.I * unitAxisDerivative 2 (F 1) g] r + (3 / 2 : ℂ) * F r g

def normalizedSynthesis (m : ℕ) (i : Fin (m + 1)) (A : SpinorBlock m) :
    SourceSpinor :=
  fun r => matrixCoefficient m (sourceBasis m i) (normalization m • A r)

/-- The finite operator is proved to differentiate its own continuous Haar
representative. No spectral assumption enters this identity. -/
theorem differential_normalizedSynthesis (m : ℕ) (i : Fin (m + 1))
    (A : SpinorBlock m) :
    differential (normalizedSynthesis m i A) =
      normalizedSynthesis m i (diracBlock m A) := by
  funext r g
  fin_cases r <;>
    simp [differential, normalizedSynthesis, diracBlock, unitAxisDerivative_matrixCoefficient,
      matrixCoefficient_apply, inner_add_right, inner_sub_right, inner_smul_right, smul_add,
      smul_sub, smul_smul] <;> ring

abbrev FieldIndex := Fin 2 × Index

def fieldBasisVector (a : FieldIndex) : SpinorL2 :=
  PiLp.single 2 a.1 (basisVector a.2)

theorem field_single_inner (r : Fin 2) (v : SourceL2) (A : SpinorL2) :
    inner ℂ (PiLp.single 2 r v : SpinorL2) A = inner ℂ v (A r) := by
  classical
  change (∑ i : Fin 2, inner ℂ ((PiLp.single 2 r v : SpinorL2) i) (A i)) = _
  rw [Finset.sum_eq_single r]
  · simp only [PiLp.single_eq_same]
  · intro i _ hir
    simp only [PiLp.single_eq_of_ne _ hir, inner_zero_left]
  · simp

theorem fieldBasisVector_orthonormal : Orthonormal ℂ fieldBasisVector := by
  classical
  rw [orthonormal_iff_ite]
  rintro ⟨r, a⟩ ⟨s, b⟩
  by_cases hrs : r = s
  · subst s
    simp [fieldBasisVector, field_single_inner, PiLp.single_eq_same,
      orthonormal_iff_ite.mp basisVector_orthonormal]
  · have hpair : (r, a) ≠ (s, b) := fun h => hrs (congrArg Prod.fst h)
    simp only [fieldBasisVector, field_single_inner, PiLp.single_eq_of_ne _ hrs,
      inner_zero_right, ite_eq_right hpair]

def finiteFieldCore : Submodule ℂ SpinorL2 :=
  Submodule.span ℂ (Set.range fieldBasisVector)

theorem finiteFieldCore_orthogonal : finiteFieldCoreᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro A hA
  have hall (r : Fin 2) (a : Index) : inner ℂ (basisVector a) (A r) = 0 := by
    have h := (finiteFieldCore.mem_orthogonal A).mp hA
      (fieldBasisVector (r, a)) (Submodule.subset_span (Set.mem_range_self (r, a)))
    simpa only [fieldBasisVector, field_single_inner] using h
  have hz (r : Fin 2) : A r = 0 := by
    apply SourceCompleteCoefficients.basis.repr.injective
    apply lp.ext
    funext a
    simp only [HilbertBasis.repr_apply_apply, basis_apply, hall, inner_zero_right]
  change A = 0
  apply (WithLp.equiv 2 (Fin 2 → SourceL2)).injective
  exact funext hz

def fieldBasis : HilbertBasis FieldIndex ℂ SpinorL2 :=
  HilbertBasis.mkOfOrthogonalEqBot fieldBasisVector_orthonormal finiteFieldCore_orthogonal

@[simp] theorem fieldBasis_apply (a : FieldIndex) : fieldBasis a = fieldBasisVector a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    fieldBasisVector_orthonormal finiteFieldCore_orthogonal) a

theorem finiteFieldCore_dense : Dense (finiteFieldCore : Set SpinorL2) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff]
  exact finiteFieldCore_orthogonal

end GeneratedFoundations.Geometry.SourceSpinorHaarBlock
