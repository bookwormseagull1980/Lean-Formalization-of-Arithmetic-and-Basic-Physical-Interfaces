module

public import GeneratedFoundations.Physical.SourceGeneratedGaugeGroup
public import GeneratedFoundations.Physical.SourceGaugeCocycle
public import GeneratedFoundations.Physical.SourceHermitianReadout
public import Mathlib.Tactic.Abel

/-!
# Four-dimensional gauge kinematics from the generated source

The four-coordinate carrier is the Hermitian readout of the same two Gaussian
source modes used by the physical interface.  Its determinant is the Lorentz
quadratic form.  The gauge group acting on the matter fibre is the intrinsic
source-generated operator group, equivalently the effective central quotient
already computed from the source action.

Connections and matter jets below are variables in the configuration spaces
constructed on this carrier.  They are not fields of the root datum.  Their
curvature and passive transformation law use only the generated four
coordinates and the faithful generated gauge action.  No lattice, second base
space, regulator or additional gauge group is introduced.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Physical.SourceChiralCarrier

namespace GeneratedFoundations.Physical.SourceFourDimensionalGaugeKinematics

open SourceHermitianReadout

/-- The four-real-coordinate carrier read from the generated Hermitian
two-mode source algebra. -/
abbrev FourCarrier := RealCoordinates
abbrev CoordinateIndex := Fin 4

/-- The determinant readout is the Lorentz quadratic form on the generated
four-carrier. -/
abbrev lorentzForm : FourCarrier → ℝ := determinantForm

theorem fourCarrier_finrank : Module.finrank ℝ FourCarrier = 4 := by
  simp [FourCarrier]

theorem hermitian_determinant_is_lorentz (q : FourCarrier) :
    (hermitianMatrix q).det = (lorentzForm q : ℂ) :=
  det_hermitianMatrix q

theorem lorentz_signature_formula (q : FourCarrier) :
    lorentzForm q = q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 := rfl

/-- The source-generated effective group, already identified with the
intrinsic group of matter operators. -/
abbrev EffectiveGaugeGroup := SourceGlobalGaugeGroup.EffectiveGroup

/-- Its faithful action on the complete generated matter carrier. -/
def matterOperator : EffectiveGaugeGroup →* Module.End ℂ FullMatter :=
  SourceGlobalGaugeGroup.effectiveRepresentation

theorem matterOperator_faithful : Function.Injective matterOperator :=
  SourceGlobalGaugeGroup.effectiveRepresentation_injective

/-- The effective quotient and the intrinsic operator group are two
presentations of the same source-generated gauge group. -/
def effectiveEquivIntrinsic :
    EffectiveGaugeGroup ≃* SourceGeneratedGaugeGroup.GeneratedGaugeGroup :=
  SourceGlobalGaugeGroup.effectiveGroupEquivRange

@[simp] theorem matterOperator_inv_apply (g : EffectiveGaugeGroup) (v : FullMatter) :
    matterOperator g⁻¹ (matterOperator g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

@[simp] theorem matterOperator_apply_inv (g : EffectiveGaugeGroup) (v : FullMatter) :
    matterOperator g (matterOperator g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul]
  simp

abbrev MatterEnd := Module.End ℂ FullMatter
abbrev MatterConnection := CoordinateIndex → MatterEnd
abbrev ConnectionDerivative := CoordinateIndex → CoordinateIndex → MatterEnd
abbrev GaugeDerivative := CoordinateIndex → MatterEnd

/-- The first jet of a four-dimensional generated connection.  Both entries
are internal variables: `derivative mu nu` represents `partial_mu A_nu`. -/
structure ConnectionJet where
  value : MatterConnection
  derivative : ConnectionDerivative

/-- The first jet of a matter field on the generated four-carrier. -/
structure MatterJet where
  value : FullMatter
  derivative : CoordinateIndex → FullMatter

/-- Component curvature of the generated connection,
`F_mu_nu = partial_mu A_nu - partial_nu A_mu + [A_mu,A_nu]`. -/
def curvatureComponent (A : ConnectionJet) (μ ν : CoordinateIndex) : MatterEnd :=
  A.derivative μ ν - A.derivative ν μ +
    (A.value μ * A.value ν - A.value ν * A.value μ)

theorem curvatureComponent_swap (A : ConnectionJet) (μ ν : CoordinateIndex) :
    curvatureComponent A ν μ = -curvatureComponent A μ ν := by
  simp only [curvatureComponent]
  abel

@[simp] theorem curvatureComponent_self (A : ConnectionJet) (μ : CoordinateIndex) :
    curvatureComponent A μ μ = 0 := by
  simp [curvatureComponent]

def zeroConnectionJet : ConnectionJet where
  value := 0
  derivative := 0

@[simp] theorem zeroConnectionJet_value (μ : CoordinateIndex) :
    zeroConnectionJet.value μ = 0 := rfl

@[simp] theorem zeroConnectionJet_derivative (μ ν : CoordinateIndex) :
    zeroConnectionJet.derivative μ ν = 0 := rfl

@[simp] theorem zeroConnection_flat (μ ν : CoordinateIndex) :
    curvatureComponent zeroConnectionJet μ ν = 0 := by
  simp [curvatureComponent]

/-- Covariant derivative of a matter jet in one of the four generated
coordinate directions. -/
def covariantComponent (A : MatterConnection) (ψ : MatterJet)
    (μ : CoordinateIndex) : FullMatter :=
  ψ.derivative μ + A μ ψ.value

/-- Passive transformation of the connection at a point.  `dg` is the first
derivative of the generated group action at that point. -/
def transformConnection (g : EffectiveGaugeGroup) (dg : GaugeDerivative)
    (A : MatterConnection) : MatterConnection := fun μ =>
  matterOperator g⁻¹ * A μ * matterOperator g + matterOperator g⁻¹ * dg μ

/-- Passive transformation of a matter first jet. -/
def transformMatterJet (g : EffectiveGaugeGroup) (dg : GaugeDerivative)
    (ψ : MatterJet) : MatterJet where
  value := matterOperator g⁻¹ ψ.value
  derivative := fun μ =>
    matterOperator g⁻¹ (ψ.derivative μ) -
      matterOperator g⁻¹ (dg μ (matterOperator g⁻¹ ψ.value))

/-- The generated connection law makes the matter derivative transform
covariantly in all four directions. -/
theorem covariantComponent_transform (g : EffectiveGaugeGroup)
    (dg : GaugeDerivative) (A : MatterConnection) (ψ : MatterJet)
    (μ : CoordinateIndex) :
    covariantComponent (transformConnection g dg A)
        (transformMatterJet g dg ψ) μ =
      matterOperator g⁻¹ (covariantComponent A ψ μ) := by
  simp [covariantComponent, transformConnection, transformMatterJet,
    Module.End.mul_apply, map_add]

/-- Collected output of the four-dimensional generated gauge interface. -/
structure Conclusions where
  carrier_dimension : Module.finrank ℝ FourCarrier = 4
  determinant_readout : ∀ q : FourCarrier,
    (hermitianMatrix q).det = (lorentzForm q : ℂ)
  gauge_action_faithful : Function.Injective matterOperator
  intrinsic_group : EffectiveGaugeGroup ≃*
    SourceGeneratedGaugeGroup.GeneratedGaugeGroup
  curvature_antisymmetric : ∀ (A : ConnectionJet) μ ν,
    curvatureComponent A ν μ = -curvatureComponent A μ ν
  zero_connection_flat : ∀ μ ν,
    curvatureComponent zeroConnectionJet μ ν = 0
  derivative_covariant : ∀ g dg A ψ μ,
    covariantComponent (transformConnection g dg A)
        (transformMatterJet g dg ψ) μ =
      matterOperator g⁻¹ (covariantComponent A ψ μ)

def sourceFourDimensionalGaugeKinematics : Conclusions where
  carrier_dimension := fourCarrier_finrank
  determinant_readout := hermitian_determinant_is_lorentz
  gauge_action_faithful := matterOperator_faithful
  intrinsic_group := effectiveEquivIntrinsic
  curvature_antisymmetric := curvatureComponent_swap
  zero_connection_flat := zeroConnection_flat
  derivative_covariant := covariantComponent_transform

/-- Pure proposition exported through the common root theorem. -/
structure Properties : Prop where
  carrier_dimension : Module.finrank ℝ FourCarrier = 4
  determinant_readout : ∀ q : FourCarrier,
    (hermitianMatrix q).det = (lorentzForm q : ℂ)
  gauge_action_faithful : Function.Injective matterOperator
  intrinsic_group : Nonempty
    (EffectiveGaugeGroup ≃* SourceGeneratedGaugeGroup.GeneratedGaugeGroup)
  curvature_antisymmetric : ∀ (A : ConnectionJet) μ ν,
    curvatureComponent A ν μ = -curvatureComponent A μ ν
  zero_connection_flat : ∀ μ ν,
    curvatureComponent zeroConnectionJet μ ν = 0
  derivative_covariant : ∀ g dg A ψ μ,
    covariantComponent (transformConnection g dg A)
        (transformMatterJet g dg ψ) μ =
      matterOperator g⁻¹ (covariantComponent A ψ μ)

theorem sourceFourDimensionalGaugeProperties : Properties where
  carrier_dimension := fourCarrier_finrank
  determinant_readout := hermitian_determinant_is_lorentz
  gauge_action_faithful := matterOperator_faithful
  intrinsic_group := ⟨effectiveEquivIntrinsic⟩
  curvature_antisymmetric := curvatureComponent_swap
  zero_connection_flat := zeroConnection_flat
  derivative_covariant := covariantComponent_transform

end GeneratedFoundations.Physical.SourceFourDimensionalGaugeKinematics
