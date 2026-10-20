module

public import GeneratedFoundations.Arithmetic.HistoryCompleteSourceGroup
public import GeneratedFoundations.Arithmetic.HistoryJointSourceTransport

/-!
# The complete joint group and the elementary arithmetic connector

The same unitary coordinates transport all matrix coefficients, not only
source frames. The relative phase commutes with the uniform source
connector, while the two independent source frames transform its doublet.
The covariance below is thus a theorem for the complete joint action.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Kronecker

namespace GeneratedFoundations.Arithmetic.HistoryCompleteConnector

open HistoryCompleteSourceGroup
open Operations.SourceCliffordConnector (ChiralMatrix)
open Operations.ReversalRealConnector (Spinor)

def transport (N : ℕ) : Module.End ℂ (HistoryCliffordAction.Space N) ≃ₐ[ℂ]
    Module.End ℂ (Space N) := (coordinates N).toLinearEquiv.conjAlgEquiv ℂ

def uniform (N : ℕ) (M : ChiralMatrix) : Module.End ℂ (Space N) :=
  transport N (HistoryCliffordAction.action N
    ((1 : Matrix (HistoryCliffordAction.HistoryLabel N)
      (HistoryCliffordAction.HistoryLabel N) ℂ) ⊗ₖ M))

theorem uniform_component (N : ℕ) (M : ChiralMatrix) (x : Space N)
    (b : HistoryRootSectors.Roots N) (s : HistoryJointChargeLattice.Spin) :
    uniform N M x b s = ∑ t, M s t • x b t := by
  apply PiLp.ext
  intro i
  change (∑ j, (((1 : Matrix (HistoryCliffordAction.HistoryLabel N)
      (HistoryCliffordAction.HistoryLabel N) ℂ) ⊗ₖ M)
      (⟨b, i⟩, s) j) * (coordinates N).symm x j) = _
  simp [Fintype.sum_prod_type, Matrix.one_apply,
    HistoryCompleteSourceGroup.coordinates_symm_apply]

theorem uniform_mul (N : ℕ) (M K : ChiralMatrix) :
    uniform N (M * K) = uniform N M * uniform N K := by
  unfold uniform
  rw [← map_mul, ← map_mul, ← Matrix.mul_kronecker_mul, one_mul]

theorem uniform_source (N : ℕ) (g : Geometry.SourceScalarResponse.Frame) :
    uniform N (sourceMatrix g) = source N g := by
  apply LinearMap.ext
  intro x
  ext b s i
  rw [uniform_component, source_apply]

theorem uniform_relative_commute (N : ℕ) (M : ChiralMatrix) (z : Circle) :
    uniform N M * relative N z = relative N z * uniform N M := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro b
  apply PiLp.ext
  intro s
  rw [Module.End.mul_apply, Module.End.mul_apply, uniform_component, relative_component,
    uniform_component, map_sum]
  simp only [relative_component, map_smul]

def connector (N : ℕ) (H : Spinor) : Module.End ℂ (Space N) :=
  transport N (HistoryCliffordAction.action N (HistoryElementaryConnector.scalarConnector N H))

theorem connector_eq_uniform (N : ℕ) (H : Spinor) :
    connector N H = uniform N
      (Operations.SourceCliffordComplex.connector
        (Operations.ReversalRealConnector.connectorOfDoublet H)) := rfl

theorem connector_intertwines (N : ℕ) (H : Spinor)
    (x : HistoryCliffordAction.Space N) :
    connector N H (coordinates N x) = coordinates N
      (HistoryCliffordAction.action N (HistoryElementaryConnector.scalarConnector N H) x) := by
  change coordinates N (HistoryCliffordAction.action N _
    ((coordinates N).symm (coordinates N x))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem connector_relative_commute (N : ℕ) (H : Spinor) (z : Circle) :
    connector N H * relative N z = relative N z * connector N H := by
  rw [connector_eq_uniform]
  exact uniform_relative_commute N _ z

theorem connector_source_covariant (N : ℕ) (g : Geometry.SourceScalarResponse.Frame)
    (H : Spinor) :
    source N g * connector N H * source N g⁻¹ =
      connector N (Geometry.SourceScalarResponse.frameDoublet g H) := by
  have h := congrArg (fun A => transport N (HistoryCliffordAction.action N A))
    (HistoryElementaryConnector.scalarConnector_covariant N g H)
  rw [HistoryElementaryConnector.frame_adjoint] at h
  simp only [map_mul] at h
  change source N g * connector N H * source N g⁻¹ = _ at h
  exact h

/-- The rank-derived relative phase and both source frames act together;
there is no projection to a chosen root or a diagonal response here. -/
theorem connector_joint_covariant (N : ℕ) (g : Presentation) (H : Spinor) :
    representation N g * connector N H * representation N g⁻¹ =
      connector N (Geometry.SourceScalarResponse.frameDoublet g.1 H) := by
  change (source N g.1 * relative N g.2) * connector N H *
    (source N g.1⁻¹ * relative N g.2⁻¹) = _
  calc
    _ = source N g.1 * (relative N g.2 * connector N H) *
        source N g.1⁻¹ * relative N g.2⁻¹ := by simp only [mul_assoc]
    _ = source N g.1 * (connector N H * relative N g.2) *
        source N g.1⁻¹ * relative N g.2⁻¹ := by rw [connector_relative_commute]
    _ = (source N g.1 * connector N H * source N g.1⁻¹) *
        (relative N g.2 * relative N g.2⁻¹) := by
      simp only [mul_assoc]
      apply congrArg (fun U => source N g.1 * (connector N H * U))
      rw [← mul_assoc, ← source_relative_commute N g.1⁻¹ g.2, mul_assoc]
    _ = _ := by
      rw [← map_mul, mul_inv_cancel, map_one, mul_one, connector_source_covariant]

theorem complete_response (N : ℕ) (H : Spinor)
    (x y : HistoryCliffordAction.Space N) :
    inner ℂ (coordinates N x) (connector N H (coordinates N y)) =
      inner ℂ x (HistoryCliffordAction.action N
        (HistoryElementaryConnector.scalarConnector N H) y) := by
  rw [connector_intertwines, (coordinates N).inner_map_map]

/-- The canonical neutral vector is fixed by its actual generated circle;
the full source exchange need not fix it. -/
theorem circle_neutralSection (n : ℕ) (z : Circle) :
    HistoryJointCircleAction.action n n 1 z (HistoryJointSourceTransport.neutralSection n) =
      HistoryJointSourceTransport.neutralSection n := by
  have hs : HistoryChargeSectors.sectorSection n (false, .inr 0)
      (HistoryJointSourceTransport.constant n) = HistoryJointSourceTransport.neutralSection n := by
    ext s i
    simp [HistoryChargeSectors.sectorSection_apply, HistoryChargeSectors.phaseProjection,
      HistoryJointSourceTransport.neutralSection, HistoryJointCharge.inclusion,
      HistoryJointSourceTransport.projection_constant]
  rw [← hs, HistoryJointCircleAction.action_sector]
  simp [HistoryJointChargeLattice.weight, HistoryJointChargeLattice.relativeWeight,
    HistoryJointChargeLattice.rightWeight]

structure Conclusions : Prop where
  all_source_coefficients : ∀ N M x b s,
    uniform N M x b s = ∑ t, M s t • x b t
  relative_phase_commutes : ∀ N H z,
    connector N H * relative N z = relative N z * connector N H
  complete_group_covariance : ∀ N g H,
    representation N g * connector N H * representation N g⁻¹ =
      connector N (Geometry.SourceScalarResponse.frameDoublet g.1 H)
  full_observation : ∀ N H x y,
    inner ℂ (coordinates N x) (connector N H (coordinates N y)) =
      inner ℂ x (HistoryCliffordAction.action N
        (HistoryElementaryConnector.scalarConnector N H) y)

theorem generated : Conclusions where
  all_source_coefficients := uniform_component
  relative_phase_commutes := connector_relative_commute
  complete_group_covariance := connector_joint_covariant
  full_observation := complete_response

end GeneratedFoundations.Arithmetic.HistoryCompleteConnector
