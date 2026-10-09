module

public import GeneratedFoundations.Geometry.SourcePolarMetric
public import GeneratedFoundations.Geometry.SourceOrthogonalTopology
public import GeneratedFoundations.Geometry.SourceProjectiveCovering
public import Mathlib.LinearAlgebra.Prod

/-!
# Three-dimensional rotations of the generated imaginary amplitudes

The imaginary amplitude space is the orthogonal complement of the real
unit in the actual quaternion carrier. Its rotation group consists of all
determinant-one real linear isometries, independently of the source action.
Each such isometry extends by the identity on the real axis. The full
four-dimensional left--right classification then makes this extension a
quaternion conjugation. Thus the actual source group maps onto all of the
three-dimensional rotations, with exactly its two-element centre as kernel.

The target has its finite-dimensional matrix topology. The resulting
topological quotient identification agrees with the previously constructed
projective readout on every source operation.
-/

@[expose] public section

noncomputable section

open Topology
open scoped Quaternion RealInnerProductSpace
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourcePolarMetric
open GeneratedFoundations.Geometry.SourceInvariantMetric
open GeneratedFoundations.Geometry.SourceSpecialOrthogonal
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceProjectiveGeometry
open GeneratedFoundations.Geometry.SourceOrthogonalCover

namespace GeneratedFoundations.Geometry.SourceThreeRotations

abbrev Imag := angularSpace (1 : ℍ)

theorem imag_finrank : Module.finrank ℝ Imag = 3 := angular_finrank (norm_one : ‖(1 : ℍ)‖ = 1)

/-- The established radial decomposition at unit radius and real pole. -/
def realImagEquiv : (ℝ × Imag) ≃ₗ[ℝ] ℍ :=
  polarLinearEquiv (norm_one : ‖(1 : ℍ)‖ = 1) (one_ne_zero : (1 : ℝ) ≠ 0)

theorem realImagEquiv_apply (x : ℝ × Imag) :
    realImagEquiv x = x.1 • (1 : ℍ) + (x.2 : ℍ) := by
  change x.1 • (1 : ℍ) + (1 : ℝ) • (x.2 : ℍ) = _
  rw [one_smul]

theorem realImagEquiv_norm_sq (x : ℝ × Imag) :
    ‖realImagEquiv x‖ ^ 2 = x.1 ^ 2 + ‖x.2‖ ^ 2 := by
  change ‖polarLinear 1 1 x‖ ^ 2 = _
  simpa only [one_pow, one_mul, Submodule.norm_coe] using
    polar_norm_sq (norm_one : ‖(1 : ℍ)‖ = 1) (1 : ℝ) x

def extensionLinear (e : Imag ≃ₗᵢ[ℝ] Imag) : ℍ ≃ₗ[ℝ] ℍ :=
  (realImagEquiv.symm.trans ((LinearEquiv.refl ℝ ℝ).prodCongr e.toLinearEquiv)).trans
    realImagEquiv

theorem extensionLinear_realImag (e : Imag ≃ₗᵢ[ℝ] Imag) (x : ℝ × Imag) :
    extensionLinear e (realImagEquiv x) = realImagEquiv (x.1, e x.2) := by
  simp only [extensionLinear, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply, LinearIsometryEquiv.coe_toLinearEquiv]

/-- Every imaginary isometry extends by fixing the real axis pointwise. -/
def extension (e : Imag ≃ₗᵢ[ℝ] Imag) : ℍ ≃ₗᵢ[ℝ] ℍ where
  toLinearEquiv := extensionLinear e
  norm_map' z := by
    obtain ⟨x, rfl⟩ := realImagEquiv.surjective z
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [extensionLinear_realImag, realImagEquiv_norm_sq, realImagEquiv_norm_sq,
      e.norm_map]

theorem extension_realImag (e : Imag ≃ₗᵢ[ℝ] Imag) (x : ℝ × Imag) :
    extension e (realImagEquiv x) = realImagEquiv (x.1, e x.2) :=
  extensionLinear_realImag e x

theorem extension_one (e : Imag ≃ₗᵢ[ℝ] Imag) : extension e 1 = 1 := by
  have h := extension_realImag e (1, 0)
  simpa only [realImagEquiv_apply, one_smul, map_zero, Submodule.coe_zero, add_zero] using h

theorem extension_imag (e : Imag ≃ₗᵢ[ℝ] Imag) (v : Imag) :
    extension e (v : ℍ) = (e v : ℍ) := by
  have h := extension_realImag e (0, v)
  simpa only [realImagEquiv_apply, zero_smul, zero_add] using h

theorem extension_identity : extension (1 : Imag ≃ₗᵢ[ℝ] Imag) = 1 := by
  apply LinearIsometryEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := realImagEquiv.surjective z
  rw [extension_realImag]
  rfl

/-- Adding the fixed real direction does not change the determinant. -/
theorem extension_det (e : Imag ≃ₗᵢ[ℝ] Imag) :
    (extension e).toLinearMap.det = e.toLinearMap.det := by
  have hm : (extension e).toLinearMap =
      realImagEquiv.toLinearMap ∘ₗ
        (LinearMap.prodMap (LinearMap.id : ℝ →ₗ[ℝ] ℝ) e.toLinearMap) ∘ₗ
        realImagEquiv.symm.toLinearMap := by
    apply LinearMap.ext
    intro z
    rfl
  rw [hm, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul]

theorem preserves_imag (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e 1 = 1) (v : Imag) :
    e (v : ℍ) ∈ Imag := by
  apply mem_angularSpace.mpr
  rw [← he, e.inner_map_map]
  exact angular_inner 1 v

theorem inverse_fixes_one (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e 1 = 1) : e.symm 1 = 1 := by
  calc
    e.symm 1 = e.symm (e 1) := congrArg e.symm he.symm
    _ = 1 := e.symm_apply_apply 1

def restriction (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e 1 = 1) : Imag ≃ₗᵢ[ℝ] Imag where
  toFun v := ⟨e (v : ℍ), preserves_imag e he v⟩
  invFun v := ⟨e.symm (v : ℍ), preserves_imag e.symm (inverse_fixes_one e he) v⟩
  left_inv v := Subtype.ext (e.symm_apply_apply v)
  right_inv v := Subtype.ext (e.apply_symm_apply v)
  map_add' v w := Subtype.ext (e.map_add (v : ℍ) (w : ℍ))
  map_smul' c v := Subtype.ext (e.map_smul c (v : ℍ))
  norm_map' v := e.norm_map (v : ℍ)

@[simp] theorem restriction_apply (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e 1 = 1) (v : Imag) :
    (restriction e he v : ℍ) = e (v : ℍ) := rfl

theorem extension_restriction (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e 1 = 1) :
    extension (restriction e he) = e := by
  apply LinearIsometryEquiv.ext
  intro z
  obtain ⟨x, rfl⟩ := realImagEquiv.surjective z
  rw [extension_realImag, realImagEquiv_apply, realImagEquiv_apply,
    map_add, map_smul, he, restriction_apply]

theorem restriction_det (e : ℍ ≃ₗᵢ[ℝ] ℍ) (he : e 1 = 1) :
    (restriction e he).toLinearMap.det = e.toLinearMap.det := by
  rw [← extension_det, extension_restriction]

/-- All orientation-preserving real isometries of the three-dimensional space. -/
def rotations : Subgroup (Imag ≃ₗᵢ[ℝ] Imag) where
  carrier := {e | e.toLinearMap.det = 1}
  one_mem' := LinearMap.det_id
  mul_mem' {e f} he hf := by
    change (e.toLinearMap.comp f.toLinearMap).det = 1
    rw [LinearMap.det_comp, he, hf, one_mul]
  inv_mem' {e} he := by
    have hm : ((e⁻¹ * e).toLinearMap).det = 1 := by
      rw [inv_mul_cancel]
      exact LinearMap.det_id
    change ((e⁻¹).toLinearMap.comp e.toLinearMap).det = 1 at hm
    rwa [LinearMap.det_comp, he, mul_one] at hm

theorem sourceConjugation_one (U : SU2) : sourceRepresentation (U, U) 1 = 1 := by
  change (unitaryEquiv.symm U : ℍ) * 1 * star (unitaryEquiv.symm U : ℍ) = 1
  rw [mul_one]
  exact Unitary.mul_star_self_of_mem (unitaryEquiv.symm U).property

/-- Conjugation on the actual imaginary amplitudes. -/
def sourceRotations : SU2 →* rotations where
  toFun U := ⟨restriction (sourceRepresentation (U, U)) (sourceConjugation_one U), by
    change (restriction (sourceRepresentation (U, U))
      (sourceConjugation_one U)).toLinearMap.det = 1
    rw [restriction_det]
    exact sourceRepresentation_det (U, U)⟩
  map_one' := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun e : ℍ ≃ₗᵢ[ℝ] ℍ => e (v : ℍ)) sourceRepresentation.map_one
  map_mul' U V := by
    apply Subtype.ext
    apply LinearIsometryEquiv.ext
    intro v
    apply Subtype.ext
    exact congrArg (fun e : ℍ ≃ₗᵢ[ℝ] ℍ => e (v : ℍ))
      (sourceRepresentation.map_mul (U, U) (V, V))

@[simp] theorem sourceRotations_apply (U : SU2) (v : Imag) :
    ((sourceRotations U).val v : ℍ) = sourceRepresentation (U, U) (v : ℍ) := rfl

theorem sourceRotations_quaternion (U : SU2) (v : Imag) :
    ((sourceRotations U).val v : ℍ) =
      (unitaryEquiv.symm U : ℍ) * (v : ℍ) * star (unitaryEquiv.symm U : ℍ) := rfl

/-- Surjectivity is onto the entire independently defined rotation group. -/
theorem sourceRotations_surjective : Function.Surjective sourceRotations := by
  intro e
  obtain ⟨a, b, hab⟩ := leftRight_surjective (extension e.val)
    ((extension_det e.val).trans e.property)
  have hfix : leftRight a b 1 = 1 := by rw [hab, extension_one]
  have hu : a * (1 : unitary ℍ) * b⁻¹ = 1 := by
    apply Subtype.ext
    exact (leftRight_unit a b 1).symm.trans hfix
  have hsame : a = b := by simpa only [mul_one, mul_inv_eq_one] using hu
  subst b
  refine ⟨unitaryEquiv a, ?_⟩
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro v
  apply Subtype.ext
  change leftRight (unitaryEquiv.symm (unitaryEquiv a))
    (unitaryEquiv.symm (unitaryEquiv a)) (v : ℍ) = (e.val v : ℍ)
  simp only [ContinuousMulEquiv.symm_apply_apply]
  rw [hab, extension_imag]

theorem sourceRotations_eq_one_iff (U : SU2) :
    sourceRotations U = 1 ↔ U = 1 ∨ U = negativeIdentity := by
  have hfull : sourceRotations U = 1 ↔ sourceRepresentation (U, U) = 1 := by
    constructor
    · intro h
      have he := congrArg (fun r : rotations => extension r.val) h
      change extension (restriction (sourceRepresentation (U, U)) (sourceConjugation_one U)) =
        extension (1 : Imag ≃ₗᵢ[ℝ] Imag) at he
      rwa [extension_restriction, extension_identity] at he
    · intro h
      apply Subtype.ext
      apply LinearIsometryEquiv.ext
      intro v
      apply Subtype.ext
      change sourceRepresentation (U, U) (v : ℍ) = (v : ℍ)
      rw [h]
      rfl
  rw [hfull, sourceRepresentation_eq_one_iff,
    GeneratedFoundations.Geometry.SourceLeftRightAction.sourceAction_kernel]
  simp only [Prod.mk.injEq, and_self]

theorem sourceRotations_kernel : sourceRotations.ker = Subgroup.center SU2 := by
  ext U
  change sourceRotations U = 1 ↔ U ∈ Subgroup.center SU2
  rw [sourceRotations_eq_one_iff, mem_centre_iff]

theorem sourceRotations_eq_iff (U V : SU2) :
    sourceRotations U = sourceRotations V ↔ U = V ∨ U = negativeIdentity * V := by
  have h : sourceRotations U = sourceRotations V ↔ sourceRotations (U * V⁻¹) = 1 := by
    rw [map_mul, map_inv, mul_inv_eq_one]
  rw [h, sourceRotations_eq_one_iff, mul_inv_eq_one, mul_inv_eq_iff_eq_mul]

def imaginaryBasis : Module.Basis (Fin 3) ℝ Imag :=
  Module.finBasisOfFinrankEq ℝ Imag imag_finrank

def rotationMatrix (e : rotations) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix imaginaryBasis imaginaryBasis e.val.toLinearMap

theorem rotationMatrix_injective : Function.Injective rotationMatrix := by
  intro e f h
  have hm : e.val.toLinearMap = f.val.toLinearMap :=
    (LinearMap.toMatrix imaginaryBasis imaginaryBasis).injective h
  apply Subtype.ext
  apply LinearIsometryEquiv.ext
  intro v
  exact congrArg (fun L : Module.End ℝ Imag => L v) hm

/-- Matrix coordinates on all rotations, fixed before taking the source quotient. -/
instance : TopologicalSpace rotations := TopologicalSpace.induced rotationMatrix inferInstance

theorem rotationMatrix_isEmbedding : Topology.IsEmbedding rotationMatrix :=
  rotationMatrix_injective.isEmbedding_induced

instance : T2Space rotations := rotationMatrix_isEmbedding.t2Space

theorem sourceRotations_continuous_apply (v : Imag) :
    Continuous (fun U : SU2 => (sourceRotations U).val v) := by
  apply continuous_induced_rng.mpr
  exact (SourceOrthogonalTopology.sourceRepresentation_continuous_apply (v : ℍ)).comp
    (continuous_id.prodMk continuous_id)

theorem sourceRotations_continuous : Continuous sourceRotations := by
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  change Continuous (fun U : SU2 => rotationMatrix (sourceRotations U) i j)
  simp only [rotationMatrix, LinearMap.toMatrix_apply]
  exact (imaginaryBasis.coord i).continuous_of_finiteDimensional.comp
    (sourceRotations_continuous_apply (imaginaryBasis j))

theorem sourceRotations_isQuotientMap : IsQuotientMap sourceRotations :=
  .of_surjective_continuous sourceRotations_surjective sourceRotations_continuous

theorem sourceRotations_kernel_isDiscrete : IsDiscrete (sourceRotations.ker : Set SU2) := by
  rw [sourceRotations_kernel]
  exact SourceProjectiveCovering.centre_isDiscrete

theorem sourceRotations_isQuotientCoveringMap :
    IsQuotientCoveringMap sourceRotations sourceRotations.ker :=
  sourceRotations_isQuotientMap.isQuotientCoveringMap_of_isDiscrete_ker_monoidHom
    sourceRotations_kernel_isDiscrete

theorem sourceRotations_isCoveringMap : IsCoveringMap sourceRotations :=
  sourceRotations_isQuotientCoveringMap.isCoveringMap

theorem sourceRotations_fibre_card (e : rotations) :
    Nat.card (sourceRotations ⁻¹' {e}) = 2 := by
  obtain ⟨U, hU⟩ := sourceRotations_surjective e
  rw [Nat.card_congr
    (sourceRotations_isQuotientCoveringMap.fiberEquivGroup ⟨U, hU⟩), sourceRotations_kernel]
  exact centre_card

instance : IsTopologicalGroup rotations where
  continuous_mul := by
    have hq := sourceRotations_isQuotientCoveringMap.isOpenQuotientMap
    apply (hq.prodMap hq).isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, Prod.map, Pi.mul_apply, map_mul] using
      sourceRotations_continuous.comp (continuous_fst.mul continuous_snd :
        Continuous (fun p : SU2 × SU2 => p.1 * p.2))
  continuous_inv := by
    apply sourceRotations_isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, map_inv] using
      sourceRotations_continuous.comp (continuous_inv : Continuous (Inv.inv : SU2 → SU2))

def centralRotationsEquiv : CentralQuotient ≃* rotations :=
  (QuotientGroup.quotientMulEquivOfEq sourceRotations_kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective sourceRotations sourceRotations_surjective)

@[simp] theorem centralRotationsEquiv_source (U : SU2) :
    centralRotationsEquiv (quotientContinuous U) = sourceRotations U := by
  change centralRotationsEquiv (QuotientGroup.mk U) = sourceRotations U
  simp only [centralRotationsEquiv, MulEquiv.trans_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

theorem centralRotationsEquiv_continuous : Continuous centralRotationsEquiv := by
  apply quotientContinuous_isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, centralRotationsEquiv_source] using sourceRotations_continuous

def centralRotationsHomeomorph : CentralQuotient ≃ₜ rotations :=
  centralRotationsEquiv.toEquiv.toHomeomorphOfContinuousClosed
    centralRotationsEquiv_continuous centralRotationsEquiv_continuous.isClosedMap

def centralRotationsContinuousEquiv : CentralQuotient ≃ₜ* rotations where
  toMulEquiv := centralRotationsEquiv
  continuous_toFun := centralRotationsHomeomorph.continuous
  continuous_invFun := centralRotationsHomeomorph.symm.continuous

/-- The independent projective readout and the full rotation group describe the same quotient. -/
def projectiveRotationsHomeomorph : RP3 ≃ₜ rotations :=
  centralProjectiveHomeomorph.symm.trans centralRotationsHomeomorph

@[simp] theorem projectiveRotationsHomeomorph_source (U : SU2) :
    projectiveRotationsHomeomorph (sourceProjection U) = sourceRotations U := by
  change centralRotationsHomeomorph
    (centralProjectiveHomeomorph.symm (sourceProjection U)) = sourceRotations U
  rw [← projectiveDescend_apply U]
  change centralRotationsHomeomorph
    (centralProjectiveHomeomorph.symm (centralProjectiveHomeomorph (quotientContinuous U))) = _
  rw [Homeomorph.symm_apply_apply]
  exact centralRotationsEquiv_source U

theorem projectiveRotationsHomeomorph_unique (e : RP3 ≃ₜ rotations)
    (he : ∀ U : SU2, e (sourceProjection U) = sourceRotations U) :
    e = projectiveRotationsHomeomorph := by
  apply Homeomorph.ext
  intro p
  obtain ⟨U, rfl⟩ := sourceProjection_isQuotientMap.surjective p
  exact (he U).trans (projectiveRotationsHomeomorph_source U).symm

end GeneratedFoundations.Geometry.SourceThreeRotations
