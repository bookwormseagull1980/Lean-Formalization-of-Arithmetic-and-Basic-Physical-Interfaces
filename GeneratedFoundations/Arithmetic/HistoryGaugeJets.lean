module

public import GeneratedFoundations.Arithmetic.HistoryEffectiveFrames
public import GeneratedFoundations.Geometry.ConnectionJetAlgebra
public import GeneratedFoundations.Geometry.HilbertTraceQuadratic

/-!
# Connection jets on the actual arithmetic source carrier

Coordinate directions are the retained arithmetic history--phase labels.
The fibre is the complete state space, with both source sectors and every
matrix coefficient. Its group of source frames is the already generated
faithful state action. Taking a quotient of response operators must not
erase the central sign on this state space.

Connections, matter jets and changes of frame are configuration variables on
these fixed carriers. They are not new inputs to the canonical source. All
noncommutative curvature and mixed terms are retained. Local covariance is
an exact two-jet identity; actual differentiable-frame covariance is proved
separately in `HistoryGaussianConnection` and the common connection module.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryGaugeJets

open HistoryCliffordAction (HistoryLabel Space)
open HistoryElementaryConnector (Frame)
open HistoryEffectiveFrames (stateResponse)

abbrev CoordinateIndex (N : ℕ) := HistoryLabel N
abbrev CoordinateCarrier (N : ℕ) := EuclideanSpace ℝ (CoordinateIndex N)
abbrev Operator (N : ℕ) := Module.End ℂ (Space N)
abbrev Connection (N : ℕ) := CoordinateIndex N → Operator N
abbrev ConnectionDerivative (N : ℕ) := CoordinateIndex N → CoordinateIndex N → Operator N
abbrev GaugeDerivative (N : ℕ) := CoordinateIndex N → Operator N
abbrev ConnectionJet (N : ℕ) :=
  Geometry.ConnectionJetAlgebra.ConnectionJet (CoordinateIndex N) (Operator N)
abbrev ConnectionTwoJet (N : ℕ) :=
  Geometry.ConnectionJetAlgebra.ConnectionTwoJet (CoordinateIndex N) (Operator N)

theorem coordinate_dimension (N : ℕ) :
    Module.finrank ℝ (CoordinateCarrier N) = Fintype.card (HistoryLabel N) := by simp

def frameUnits (N : ℕ) (g : Frame) : (Operator N)ˣ where
  val := stateResponse N g
  inv := stateResponse N g⁻¹
  val_inv := by rw [← map_mul, mul_inv_cancel, map_one]
  inv_val := by rw [← map_mul, inv_mul_cancel, map_one]

theorem frameOperator_faithful (N : ℕ) : Function.Injective (stateResponse N) :=
  HistoryEffectiveFrames.frame_action_faithful N

@[simp] theorem frameOperator_inv_apply (N : ℕ) (g : Frame) (v : Space N) :
    stateResponse N g⁻¹ (stateResponse N g v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

@[simp] theorem frameOperator_apply_inv (N : ℕ) (g : Frame) (v : Space N) :
    stateResponse N g (stateResponse N g⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
  rfl

abbrev curvature {N : ℕ} :=
  @Geometry.ConnectionJetAlgebra.curvature (CoordinateIndex N) (Operator N) _

theorem curvature_swap (N : ℕ) (A : ConnectionJet N) (μ ν : CoordinateIndex N) :
    curvature A ν μ = -curvature A μ ν :=
  Geometry.ConnectionJetAlgebra.curvature_swap A μ ν

@[simp] theorem curvature_self (N : ℕ) (A : ConnectionJet N) (μ : CoordinateIndex N) :
    curvature A μ μ = 0 := Geometry.ConnectionJetAlgebra.curvature_self A μ

def zeroConnectionJet (N : ℕ) : ConnectionJet N :=
  Geometry.ConnectionJetAlgebra.zeroConnectionJet

@[simp] theorem zeroConnectionJet_value (N : ℕ) (μ : CoordinateIndex N) :
    (zeroConnectionJet N).value μ = 0 := rfl

@[simp] theorem zeroConnectionJet_derivative (N : ℕ) (μ ν : CoordinateIndex N) :
    (zeroConnectionJet N).derivative μ ν = 0 := rfl

@[simp] theorem zeroConnection_flat (N : ℕ) (μ ν : CoordinateIndex N) :
    curvature (zeroConnectionJet N) μ ν = 0 :=
  Geometry.ConnectionJetAlgebra.zeroConnection_flat μ ν

structure MatterJet (N : ℕ) where
  value : Space N
  derivative : CoordinateIndex N → Space N

def covariantComponent (N : ℕ) (A : CoordinateIndex N → Operator N)
    (ψ : MatterJet N) (μ : CoordinateIndex N) : Space N :=
  ψ.derivative μ + A μ ψ.value

def transformConnection (N : ℕ) (g : Frame) (dg : CoordinateIndex N → Operator N)
    (A : CoordinateIndex N → Operator N) : CoordinateIndex N → Operator N := fun μ =>
  stateResponse N g⁻¹ * A μ * stateResponse N g + stateResponse N g⁻¹ * dg μ

def transformMatterJet (N : ℕ) (g : Frame) (dg : CoordinateIndex N → Operator N)
    (ψ : MatterJet N) : MatterJet N where
  value := stateResponse N g⁻¹ ψ.value
  derivative μ := stateResponse N g⁻¹ (ψ.derivative μ) -
    stateResponse N g⁻¹ (dg μ (stateResponse N g⁻¹ ψ.value))

theorem covariantComponent_transform (N : ℕ) (g : Frame)
    (dg : CoordinateIndex N → Operator N) (A : CoordinateIndex N → Operator N)
    (ψ : MatterJet N) (μ : CoordinateIndex N) :
    covariantComponent N (transformConnection N g dg A)
      (transformMatterJet N g dg ψ) μ =
      stateResponse N g⁻¹ (covariantComponent N A ψ μ) := by
  have hi (x : Space N) : stateResponse N g (stateResponse N g⁻¹ x) = x := by
    change (stateResponse N g * stateResponse N g⁻¹) x = x
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  simp [covariantComponent, transformConnection, transformMatterJet,
    Module.End.mul_apply, map_add, hi]

structure GaugeTwoJet (N : ℕ) where
  value : Frame
  first : CoordinateIndex N → Operator N
  second : CoordinateIndex N → CoordinateIndex N → Operator N
  mixed_second : ∀ μ ν, second μ ν = second ν μ

def algebraicGaugeJet (N : ℕ) (q : GaugeTwoJet N) :
    Geometry.ConnectionJetAlgebra.GaugeTwoJet (CoordinateIndex N) (Operator N) where
  value := frameUnits N q.value
  first := q.first
  second := q.second
  mixed_second := q.mixed_second

def transformConnectionJet (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N) :
    ConnectionJet N := Geometry.ConnectionJetAlgebra.transform (algebraicGaugeJet N q) A

def conjugate (N : ℕ) (g : Frame) (X : Operator N) : Operator N :=
  Geometry.ConnectionJetAlgebra.conjugate (frameUnits N g) X

theorem curvature_transform (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N)
    (μ ν : CoordinateIndex N) :
    curvature (transformConnectionJet N q A) μ ν = conjugate N q.value (curvature A μ ν) :=
  Geometry.ConnectionJetAlgebra.curvature_transform (algebraicGaugeJet N q) A μ ν

theorem bianchi (N : ℕ) (A : ConnectionTwoJet N) (ξ μ ν : CoordinateIndex N) :
    Geometry.ConnectionJetAlgebra.covariantCurvature A ξ μ ν +
      Geometry.ConnectionJetAlgebra.covariantCurvature A μ ν ξ +
      Geometry.ConnectionJetAlgebra.covariantCurvature A ν ξ μ = 0 :=
  Geometry.ConnectionJetAlgebra.bianchi A ξ μ ν

def quadratic (N : ℕ) (X : Operator N) : ℝ := Geometry.HilbertTraceQuadratic.energy X

theorem quadratic_nonneg (N : ℕ) (X : Operator N) : 0 ≤ quadratic N X :=
  Geometry.HilbertTraceQuadratic.energy_nonneg X

theorem quadratic_eq_zero_iff (N : ℕ) (X : Operator N) :
    quadratic N X = 0 ↔ X = 0 := Geometry.HilbertTraceQuadratic.energy_eq_zero_iff X

/-- On skew-adjoint directions this is exactly minus the trace of the square. -/
theorem quadratic_skew (N : ℕ) (X : Operator N) (hX : X.adjoint = -X) :
    quadratic N X = -(LinearMap.trace ℂ (Space N) (X * X)).re := by
  simp [quadratic, Geometry.HilbertTraceQuadratic.energy, hX]

theorem quadratic_conjugate (N : ℕ) (g : Frame) (X : Operator N) :
    quadratic N (conjugate N g X) = quadratic N X :=
  Geometry.HilbertTraceQuadratic.conjugate_energy (frameUnits N g)
    (HistoryEffectiveFrames.stateResponse_adjoint N g) X

def curvatureDensity (N : ℕ) (A : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, quadratic N (curvature A μ ν)

theorem curvatureDensity_nonneg (N : ℕ) (A : ConnectionJet N) :
    0 ≤ curvatureDensity N A :=
  Finset.sum_nonneg fun μ _ => Finset.sum_nonneg fun ν _ =>
    quadratic_nonneg N (curvature A μ ν)

theorem curvatureDensity_eq_zero_iff (N : ℕ) (A : ConnectionJet N) :
    curvatureDensity N A = 0 ↔ ∀ μ ν, curvature A μ ν = 0 := by
  constructor
  · intro h μ ν
    have hμ : ∑ ν, quadratic N (curvature A μ ν) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => Finset.sum_nonneg fun j _ => quadratic_nonneg N _)).mp h μ
          (Finset.mem_univ μ)
    have hμν := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => quadratic_nonneg N (curvature A μ j))).mp hμ ν (Finset.mem_univ ν)
    exact (quadratic_eq_zero_iff N _).mp hμν
  · intro h
    simp [curvatureDensity, h, quadratic, Geometry.HilbertTraceQuadratic.energy_zero]

theorem curvatureDensity_transform (N : ℕ) (q : GaugeTwoJet N) (A : ConnectionJet N) :
    curvatureDensity N (transformConnectionJet N q A) = curvatureDensity N A := by
  simp [curvatureDensity, curvature_transform, quadratic_conjugate]

structure Conclusions : Prop where
  actual_dimension : ∀ N, Module.finrank ℝ (CoordinateCarrier N) =
    Fintype.card (HistoryLabel N)
  faithful_frame_action : ∀ N, Function.Injective (stateResponse N)
  matter_covariant : ∀ N g dg A ψ μ,
    covariantComponent N (transformConnection N g dg A)
      (transformMatterJet N g dg ψ) μ = stateResponse N g⁻¹ (covariantComponent N A ψ μ)
  curvature_covariant : ∀ N q A μ ν,
    curvature (transformConnectionJet N q A) μ ν = conjugate N q.value (curvature A μ ν)
  full_bianchi : ∀ N (A : ConnectionTwoJet N) ξ μ ν,
    Geometry.ConnectionJetAlgebra.covariantCurvature A ξ μ ν +
      Geometry.ConnectionJetAlgebra.covariantCurvature A μ ν ξ +
      Geometry.ConnectionJetAlgebra.covariantCurvature A ν ξ μ = 0
  positive_density : ∀ N A, 0 ≤ curvatureDensity N A
  definite_density : ∀ N A, curvatureDensity N A = 0 ↔ ∀ μ ν, curvature A μ ν = 0
  invariant_density : ∀ N q A,
    curvatureDensity N (transformConnectionJet N q A) = curvatureDensity N A

theorem generated : Conclusions where
  actual_dimension := coordinate_dimension
  faithful_frame_action := frameOperator_faithful
  matter_covariant := covariantComponent_transform
  curvature_covariant := curvature_transform
  full_bianchi := bianchi
  positive_density := curvatureDensity_nonneg
  definite_density := curvatureDensity_eq_zero_iff
  invariant_density := curvatureDensity_transform

end GeneratedFoundations.Arithmetic.HistoryGaugeJets
