module

public import GeneratedFoundations.Geometry.SourceScalarResponse
public import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# Antiunitary source reversal and independent Hilbert frames

The fixed Gaussian-normalized source coordinates give an explicit antiunitary
reversal on the actual degree-one Haar carrier.  Its inner-product identity is
proved in those coordinates; neither antiunitarity nor norm preservation is an
additional hypothesis.  Its square is minus the identity and its inverse is
minus itself.

Independent unitary frames on distinct left and right Hilbert carriers transport
this structure and the elementary connector classification.  Arbitrary unitary
changes transport the reversal covariantly.  A change preserves the fixed source
reversal exactly when its source matrix belongs to the already generated SU(2).
This last assertion quantifies over all complex unitary changes of source frame.
-/

@[expose] public section

noncomputable section

open scoped ComplexConjugate
open GeneratedFoundations.Geometry.SourceJointResponse (S)
open GeneratedFoundations.Operations.ReversalRealConnector (Spinor Mat2 reversal)
open GeneratedFoundations.Operations
open GeneratedFoundations.Operations.SourceSpinCornerGroup (SU2)

namespace GeneratedFoundations.Geometry.SourceReversalIsometry

private def coordinateReversal (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  WithLp.toLp 2 (reversal (WithLp.ofLp v))

private theorem coordinateReversal_inner (x y : EuclideanSpace ℂ (Fin 2)) :
    inner ℂ (coordinateReversal x) (coordinateReversal y) = inner ℂ y x := by
  simp [coordinateReversal, PiLp.inner_apply, RCLike.inner_apply,
    ReversalRealConnector.reversal, Fin.sum_univ_two]
  ring

private theorem transportedReversal_coordinates (s : S) :
    SourceSpinIdentification.coordinateUnitary.symm
        (SourceScalarResponse.transportedReversal s) =
      coordinateReversal (SourceSpinIdentification.coordinateUnitary.symm s) := by
  apply WithLp.ofLp_injective 2
  exact SourceScalarResponse.spinCoordinates_reversal s

theorem transportedReversal_inner (x y : S) :
    inner ℂ (SourceScalarResponse.transportedReversal x)
        (SourceScalarResponse.transportedReversal y) = inner ℂ y x := by
  calc
    _ = inner ℂ (SourceSpinIdentification.coordinateUnitary.symm
          (SourceScalarResponse.transportedReversal x))
        (SourceSpinIdentification.coordinateUnitary.symm
          (SourceScalarResponse.transportedReversal y)) :=
      (SourceSpinIdentification.coordinateUnitary.symm.inner_map_map _ _).symm
    _ = inner ℂ (SourceSpinIdentification.coordinateUnitary.symm y)
        (SourceSpinIdentification.coordinateUnitary.symm x) := by
      rw [transportedReversal_coordinates, transportedReversal_coordinates,
        coordinateReversal_inner]
    _ = inner ℂ y x := SourceSpinIdentification.coordinateUnitary.symm.inner_map_map y x

theorem transportedReversal_norm (x : S) :
    ‖SourceScalarResponse.transportedReversal x‖ = ‖x‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (SourceScalarResponse.transportedReversal x),
    norm_eq_sqrt_re_inner (𝕜 := ℂ) x, transportedReversal_inner]

theorem transportedReversal_neg (x : S) :
    SourceScalarResponse.transportedReversal (-x) =
      -SourceScalarResponse.transportedReversal x := by
  exact map_neg (AddMonoidHom.mk' SourceScalarResponse.transportedReversal
    SourceScalarResponse.transportedReversal_add) x

/-- The existing source reversal, now bundled with its proved antiunitarity and inverse. -/
def sourceReversal : S ≃ₗᵢ⋆[ℂ] S where
  toFun := SourceScalarResponse.transportedReversal
  invFun := fun x => -SourceScalarResponse.transportedReversal x
  left_inv x := by simp [SourceScalarResponse.transportedReversal_square]
  right_inv x := by
    rw [transportedReversal_neg, SourceScalarResponse.transportedReversal_square, neg_neg]
  map_add' := SourceScalarResponse.transportedReversal_add
  map_smul' := SourceScalarResponse.transportedReversal_smul
  norm_map' := transportedReversal_norm

@[simp] theorem sourceReversal_apply (x : S) :
    sourceReversal x = SourceScalarResponse.transportedReversal x := rfl

theorem sourceReversal_inner (x y : S) :
    inner ℂ (sourceReversal x) (sourceReversal y) = inner ℂ y x :=
  transportedReversal_inner x y

theorem sourceReversal_inner_conjugate (x y : S) :
    inner ℂ (sourceReversal x) (sourceReversal y) = conj (inner ℂ x y) :=
  (sourceReversal_inner x y).trans (inner_conj_symm (𝕜 := ℂ) y x).symm

@[simp] theorem sourceReversal_square (x : S) : sourceReversal (sourceReversal x) = -x :=
  SourceScalarResponse.transportedReversal_square x

@[simp] theorem sourceReversal_symm_apply (x : S) : sourceReversal.symm x = -sourceReversal x := rfl

theorem spinCoordinates_basis (i : Fin 2) :
    SourceScalarResponse.spinCoordinates (SourceSpinIdentification.spinBasis i) =
      Pi.single i 1 := by
  change WithLp.ofLp (SourceSpinIdentification.coordinateUnitary.symm
    (SourceSpinIdentification.spinBasis i)) = _
  rw [SourceSpinIdentification.spinBasis_apply, LinearIsometryEquiv.symm_apply_apply]

theorem sourceReversal_basis_zero :
    sourceReversal (SourceSpinIdentification.spinBasis 0) =
      -SourceSpinIdentification.spinBasis 1 := by
  apply SourceScalarResponse.spinCoordinates.injective
  change SourceScalarResponse.spinCoordinates (SourceScalarResponse.transportedReversal
    (SourceSpinIdentification.spinBasis 0)) =
    SourceScalarResponse.spinCoordinates (-SourceSpinIdentification.spinBasis 1)
  rw [SourceScalarResponse.spinCoordinates_reversal, map_neg,
    spinCoordinates_basis, spinCoordinates_basis]
  funext i
  fin_cases i <;> simp [ReversalRealConnector.reversal]

theorem sourceReversal_basis_one :
    sourceReversal (SourceSpinIdentification.spinBasis 1) =
      SourceSpinIdentification.spinBasis 0 := by
  apply SourceScalarResponse.spinCoordinates.injective
  change SourceScalarResponse.spinCoordinates (SourceScalarResponse.transportedReversal
    (SourceSpinIdentification.spinBasis 1)) =
    SourceScalarResponse.spinCoordinates (SourceSpinIdentification.spinBasis 0)
  rw [SourceScalarResponse.spinCoordinates_reversal,
    spinCoordinates_basis, spinCoordinates_basis]
  funext i
  fin_cases i <;> simp [ReversalRealConnector.reversal]

/-- Compatibility with the fixed source reversal is an equation on an arbitrary unitary map. -/
def PseudorealFrameChange (u : S ≃ₗᵢ[ℂ] S) : Prop :=
  ∀ x, u (sourceReversal x) = sourceReversal (u x)

private theorem sourceMatrix_eq_orthonormal (h : Module.End ℂ S) :
    SourceScalarResponse.sourceMatrix h = LinearMap.toMatrixOrthonormal SourceSpinIdentification.spinBasis h := by
  have he := SourceSpinIdentification.spinAction_matrix
    (SourceScalarResponse.sourceMatrix h)
  simpa only [SourceScalarResponse.spinAction_sourceMatrix] using he.symm

theorem sourceMatrix_unitary (u : S ≃ₗᵢ[ℂ] S) :
    SourceScalarResponse.sourceMatrix u.toLinearEquiv.toLinearMap ∈
      Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [sourceMatrix_eq_orthonormal]
  exact u.toMatrix_mem_unitaryGroup SourceSpinIdentification.spinBasis SourceSpinIdentification.spinBasis

private theorem unitary_reversalReal_specialUnitary (M : Mat2)
    (hu : M ∈ Matrix.unitaryGroup (Fin 2) ℂ) (hr : ReversalRealConnector.ReversalReal M) :
    M ∈ SU2 := by
  obtain ⟨h10, h11⟩ := (ReversalRealConnector.reversalReal_iff_entries M).mp hr
  have hrow : M 0 0 * star (M 0 0) + M 0 1 * star (M 0 1) = 1 := by
    have h := congrArg (fun A : Mat2 => A 0 0) (Matrix.mem_unitaryGroup_iff.mp hu)
    simpa [Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply, Fin.sum_univ_two] using h
  refine Matrix.mem_specialUnitaryGroup_iff.mpr ⟨hu, ?_⟩
  rw [Matrix.det_fin_two, h10, h11]
  simpa only [mul_neg, sub_neg_eq_add] using hrow

/-- All unitary source frame changes preserving `J` are exactly SU(2) in the fixed source frame. -/
theorem pseudorealFrameChange_iff_specialUnitary (u : S ≃ₗᵢ[ℂ] S) :
    PseudorealFrameChange u ↔
      SourceScalarResponse.sourceMatrix u.toLinearEquiv.toLinearMap ∈ SU2 := by
  change SourceScalarResponse.ReversalCompatible u.toLinearEquiv.toLinearMap ↔ _
  rw [SourceScalarResponse.reversalCompatible_iff_matrix]
  constructor
  · exact unitary_reversalReal_specialUnitary _ (sourceMatrix_unitary u)
  · intro hu
    exact SourceScalarResponse.specialUnitary_reversalReal ⟨_, hu⟩

theorem sourceUnitary_pseudoreal (U : SU2) :
    PseudorealFrameChange (Geometry.SourceSymmetricUnitary.unitaryAction 1 U) := by
  have h := SourceScalarResponse.sourceOperator_reversalCompatible U
  rw [SourceJointResponse.sourceOperator_eq_unitary] at h
  exact h

section Frames

variable {E F E' F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

/-- A frame points from its own Hilbert carrier to the fixed source spin carrier. -/
def framedReversal (e : E ≃ₗᵢ[ℂ] S) : E ≃ₗᵢ⋆[ℂ] E :=
  e.trans (sourceReversal.trans e.symm)

@[simp] theorem framedReversal_apply (e : E ≃ₗᵢ[ℂ] S) (x : E) :
    framedReversal e x = e.symm (sourceReversal (e x)) := rfl

theorem framedReversal_inner (e : E ≃ₗᵢ[ℂ] S) (x y : E) :
    inner ℂ (framedReversal e x) (framedReversal e y) = inner ℂ y x := by
  simp only [framedReversal_apply, e.symm.inner_map_map, sourceReversal_inner, e.inner_map_map]

@[simp] theorem framedReversal_square (e : E ≃ₗᵢ[ℂ] S) (x : E) :
    framedReversal e (framedReversal e x) = -x := by
  simp only [framedReversal_apply, e.apply_symm_apply, sourceReversal_square,
    map_neg, e.symm_apply_apply]

theorem framedReversal_symm_apply (e : E ≃ₗᵢ[ℂ] S) (x : E) :
    (framedReversal e).symm x = -framedReversal e x := by
  apply (framedReversal e).injective
  rw [LinearIsometryEquiv.apply_symm_apply, map_neg, framedReversal_square, neg_neg]

def framedCoordinates (e : E ≃ₗᵢ[ℂ] S) : E ≃ₗ[ℂ] Spinor :=
  e.toLinearEquiv.trans SourceScalarResponse.spinCoordinates

theorem framedReversal_eq_coordinates (e : E ≃ₗᵢ[ℂ] S) (x : E) :
    framedReversal e x =
      SourceReversalRealConnector.transportedReversal (framedCoordinates e) x := rfl

def IntertwinesReversal (eL : E ≃ₗᵢ[ℂ] S) (eR : F ≃ₗᵢ[ℂ] S) (h : F →ₗ[ℂ] E) : Prop :=
  ∀ x, h (framedReversal eR x) = framedReversal eL (h x)

def doubletMap (eL : E ≃ₗᵢ[ℂ] S) (eR : F ≃ₗᵢ[ℂ] S) (H : Spinor) : F →ₗ[ℂ] E :=
  SourceReversalRealConnector.sourceMap (framedCoordinates eL) (framedCoordinates eR)
    (ReversalRealConnector.connectorOfDoublet H)

/-- The left and right frames may have different carriers and are not identified. -/
theorem intertwinesReversal_iff_unique_doublet
    (eL : E ≃ₗᵢ[ℂ] S) (eR : F ≃ₗᵢ[ℂ] S) (h : F →ₗ[ℂ] E) :
    IntertwinesReversal eL eR h ↔ ∃! H : Spinor, h = doubletMap eL eR H := by
  change SourceReversalRealConnector.IntertwinesReversal
      (framedCoordinates eL) (framedCoordinates eR) h ↔ _
  exact SourceReversalRealConnector.intertwinesReversal_iff_unique_doublet _ _ h

private theorem sourceMap_eq_spinAction (M : Mat2) :
    SourceReversalRealConnector.sourceMap SourceScalarResponse.spinCoordinates
        SourceScalarResponse.spinCoordinates M = SourceSpinIdentification.spinAction M := by
  apply LinearMap.ext
  intro s
  apply SourceScalarResponse.spinCoordinates.injective
  change SourceScalarResponse.spinCoordinates
    (SourceScalarResponse.spinCoordinates.symm
      (M.mulVec (SourceScalarResponse.spinCoordinates s))) = _
  rw [SourceScalarResponse.spinCoordinates.apply_symm_apply,
    SourceScalarResponse.spinCoordinates_spinAction]

theorem doubletMap_apply (eL : E ≃ₗᵢ[ℂ] S) (eR : F ≃ₗᵢ[ℂ] S)
    (H : Spinor) (x : F) :
    doubletMap eL eR H x = eL.symm (SourceScalarResponse.doubletLift H (eR x)) := by
  have h := LinearMap.congr_fun
    (sourceMap_eq_spinAction (ReversalRealConnector.connectorOfDoublet H)) (eR x)
  exact congrArg eL.symm h

theorem framedReversal_changeFrame (e : E ≃ₗᵢ[ℂ] S) (u : S ≃ₗᵢ[ℂ] S)
    (hu : PseudorealFrameChange u) : framedReversal (e.trans u) = framedReversal e := by
  ext x
  apply e.injective
  simp only [framedReversal_apply, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, e.apply_symm_apply]
  apply u.injective
  rw [u.apply_symm_apply, hu]

/-- General unitary changes need not preserve a fixed `J`; they transport it by conjugation. -/
theorem framedReversal_transport (e : E ≃ₗᵢ[ℂ] S) (u : E ≃ₗᵢ[ℂ] E') (x : E) :
    framedReversal (u.symm.trans e) (u x) = u (framedReversal e x) := by
  simp only [framedReversal_apply, LinearIsometryEquiv.symm_trans,
    LinearIsometryEquiv.trans_apply, u.symm_apply_apply, LinearIsometryEquiv.symm_symm]

def transportConnector (uL : E ≃ₗᵢ[ℂ] E') (uR : F ≃ₗᵢ[ℂ] F')
    (h : F →ₗ[ℂ] E) : F' →ₗ[ℂ] E' :=
  uL.toLinearEquiv.toLinearMap.comp (h.comp uR.symm.toLinearEquiv.toLinearMap)

@[simp] theorem transportConnector_apply (uL : E ≃ₗᵢ[ℂ] E') (uR : F ≃ₗᵢ[ℂ] F')
    (h : F →ₗ[ℂ] E) (x : F) : transportConnector uL uR h (uR x) = uL (h x) := by
  change uL (h (uR.symm (uR x))) = _
  rw [uR.symm_apply_apply]

theorem intertwinesReversal_transport_iff
    (eL : E ≃ₗᵢ[ℂ] S) (eR : F ≃ₗᵢ[ℂ] S)
    (uL : E ≃ₗᵢ[ℂ] E') (uR : F ≃ₗᵢ[ℂ] F') (h : F →ₗ[ℂ] E) :
    IntertwinesReversal (uL.symm.trans eL) (uR.symm.trans eR)
        (transportConnector uL uR h) ↔ IntertwinesReversal eL eR h := by
  constructor
  · intro hh x
    have he := hh (uR x)
    rw [framedReversal_transport, transportConnector_apply, transportConnector_apply,
      framedReversal_transport] at he
    exact uL.injective he
  · intro hh x'
    obtain ⟨x, rfl⟩ := uR.surjective x'
    rw [framedReversal_transport, transportConnector_apply, transportConnector_apply,
      framedReversal_transport, hh]

end Frames

variable {b : ℝ} (hb : 0 < b)

/-- The same antiunitary on the original Gaussian two-mode source, at every positive width. -/
def gaussianReversal : SourceVacuumTransport.V hb ≃ₗᵢ⋆[ℂ] SourceVacuumTransport.V hb :=
  framedReversal (SourceSpinIdentification.sourceUnitary hb)

theorem gaussianReversal_intertwines (x : SourceVacuumTransport.V hb) :
    SourceSpinIdentification.sourceUnitary hb (gaussianReversal hb x) =
      sourceReversal (SourceSpinIdentification.sourceUnitary hb x) :=
  (SourceSpinIdentification.sourceUnitary hb).apply_symm_apply _

theorem gaussianReversal_vacuum :
    gaussianReversal hb (SourceVacuumTransport.basisVector hb 0) =
      -SourceVacuumTransport.basisVector hb 1 := by
  apply (SourceSpinIdentification.sourceUnitary hb).injective
  rw [gaussianReversal_intertwines, SourceSpinIdentification.sourceUnitary_basis,
    map_neg, SourceSpinIdentification.sourceUnitary_basis, sourceReversal_basis_zero]

theorem gaussianReversal_excitation :
    gaussianReversal hb (SourceVacuumTransport.basisVector hb 1) =
      SourceVacuumTransport.basisVector hb 0 := by
  apply (SourceSpinIdentification.sourceUnitary hb).injective
  rw [gaussianReversal_intertwines, SourceSpinIdentification.sourceUnitary_basis,
    SourceSpinIdentification.sourceUnitary_basis, sourceReversal_basis_one]

end GeneratedFoundations.Geometry.SourceReversalIsometry
