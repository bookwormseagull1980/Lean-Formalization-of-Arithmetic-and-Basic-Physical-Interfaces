module

public import GeneratedFoundations.Physical.SourceFourDimensionalGaugeKinematics
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Tactic

/-!
# Nonlinear tensor density on the generated four-carrier

The same four-coordinate carrier supports the metric-density and connection
configuration variables. The first-order curvature density contains both
the derivative term and the quadratic connection term before variation.

The affine-dilation Ward identity uniquely fixes the cubic self-coupling
inside the unit-normalized quadratic-plus-cubic comparison family. This is
a necessary nonlinear covariance test, proved by differentiating the actual
density along the infinitesimal tensor-density transformation. It does not
assert the full local-diffeomorphism identity or the metric field equations.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceNonlinearTensorAction

abbrev Index := SourceFourDimensionalGaugeKinematics.CoordinateIndex
abbrev Tensor := Index → Index → ℝ
abbrev Connection := Index → Index → Index → ℝ
abbrev ConnectionDerivative := Index → Index → Index → Index → ℝ

/-- The determinant signature already derived from the source Hermitian readout. -/
def background : Tensor := fun i j => if i = j then (if i = 0 then 1 else -1) else 0

def pairing (q R : Tensor) : ℝ := ∑ i, ∑ j, q i j * R i j

theorem background_source_signature
    (v : SourceFourDimensionalGaugeKinematics.FourCarrier) :
    pairing background (fun i j => v i * v j) =
      SourceFourDimensionalGaugeKinematics.lorentzForm v := by
  simp [pairing, background, Fin.sum_univ_succ,
    SourceFourDimensionalGaugeKinematics.lorentzForm,
    SourceHermitianReadout.determinantForm]
  ring

def linearRicci (dA : ConnectionDerivative) : Tensor := fun i j =>
  ∑ r, (dA r r i j - dA j r i r)

def quadraticRicci (A : Connection) : Tensor := fun i j =>
  ∑ r, ∑ s, (A r r s * A s i j - A r j s * A s i r)

/-- The full local first-order curvature density, not a quadratic Hessian. -/
def density (q : Tensor) (A : Connection) (dA : ConnectionDerivative) : ℝ :=
  pairing q (linearRicci dA) + pairing q (quadraticRicci A)

/-- Only the relative cubic coefficient is varied in this comparison class. -/
def comparisonDensity (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) : ℝ :=
  pairing q (linearRicci dA) +
    (1 - c) * pairing background (quadraticRicci A) +
    c * pairing q (quadraticRicci A)

@[simp] theorem comparisonDensity_one (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) : comparisonDensity 1 q A dA = density q A dA := by
  simp [comparisonDensity, density]

theorem pairing_smul_left (t : ℝ) (q R : Tensor) :
    pairing (fun i j => t * q i j) R = t * pairing q R := by
  simp only [pairing, mul_assoc, ← Finset.mul_sum]

theorem pairing_smul_right (t : ℝ) (q R : Tensor) :
    pairing q (fun i j => t * R i j) = t * pairing q R := by
  simp only [pairing]
  simp_rw [show ∀ i j, q i j * (t * R i j) = t * (q i j * R i j) by
    intro i j; ring]
  simp only [← Finset.mul_sum]

theorem linearRicci_smul (t : ℝ) (dA : ConnectionDerivative) :
    linearRicci (fun a r i j => t * dA a r i j) =
      fun i j => t * linearRicci dA i j := by
  funext i j
  simp [linearRicci, mul_sub, Finset.mul_sum]

theorem quadraticRicci_smul (t : ℝ) (A : Connection) :
    quadraticRicci (fun r i j => t * A r i j) =
      fun i j => t ^ 2 * quadraticRicci A i j := by
  funext i j
  simp only [quadraticRicci]
  simp_rw [show ∀ r s,
    (t * A r r s) * (t * A s i j) - (t * A r j s) * (t * A s i r) =
      t ^ 2 * (A r r s * A s i j - A r j s * A s i r) by
    intro r s; ring]
  simp only [← Finset.mul_sum]

def dilationGradient : Tensor := fun i j => if i = j then 1 else 0

/-- Lie variation of a contravariant density of weight one at xi=0. -/
def densityLieAtOrigin (q X : Tensor) : Tensor := fun i j =>
  (∑ a, X a a) * q i j -
    ∑ a, (q a j * X a i + q i a * X a j)

/-- The affine part of the torsion-free connection transformation. -/
def connectionLieAtOrigin (A : Connection) (X : Tensor) : Connection := fun r i j =>
  ∑ s, (-A s i j * X s r + A r s j * X i s + A r i s * X j s)

/-- Differentiating the same affine transformation adds its covector-index term. -/
def connectionDerivativeLieAtOrigin (dA : ConnectionDerivative) (X : Tensor) :
    ConnectionDerivative := fun a r i j =>
  ∑ s, (X a s * dA s r i j - dA a s i j * X s r +
    dA a r s j * X i s + dA a r i s * X j s)

theorem densityLieAtOrigin_dilation (q : Tensor) :
    densityLieAtOrigin q dilationGradient = fun i j => 2 * q i j := by
  funext i j
  simp [densityLieAtOrigin, dilationGradient, Finset.sum_add_distrib]
  ring

theorem connectionLieAtOrigin_dilation (A : Connection) :
    connectionLieAtOrigin A dilationGradient = A := by
  funext r i j
  simp [connectionLieAtOrigin, dilationGradient, Finset.sum_add_distrib]

theorem connectionDerivativeLieAtOrigin_dilation (dA : ConnectionDerivative) :
    connectionDerivativeLieAtOrigin dA dilationGradient = fun a r i j => 2 * dA a r i j := by
  funext a r i j
  simp [connectionDerivativeLieAtOrigin, dilationGradient, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

/-- At the origin, xi(x)=x acts by delta q=2q, delta A=A,
and delta(dA)=2dA. These are the four-dimensional density weights. -/
def dilationRay (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) (t : ℝ) : ℝ :=
  comparisonDensity c (fun i j => (1 + 2 * t) * q i j)
    (fun r i j => (1 + t) * A r i j)
    (fun a r i j => (1 + 2 * t) * dA a r i j)

/-- The ray is exactly the first variation along the actual affine Lie action. -/
theorem dilationRay_eq_liePath (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) (t : ℝ) :
    dilationRay c q A dA t = comparisonDensity c
      (fun i j => q i j + t * densityLieAtOrigin q dilationGradient i j)
      (fun r i j => A r i j + t * connectionLieAtOrigin A dilationGradient r i j)
      (fun a r i j => dA a r i j +
        t * connectionDerivativeLieAtOrigin dA dilationGradient a r i j) := by
  rw [densityLieAtOrigin_dilation, connectionLieAtOrigin_dilation,
    connectionDerivativeLieAtOrigin_dilation]
  have hq : (fun i j => q i j + t * (2 * q i j)) =
      (fun i j => (1 + 2 * t) * q i j) := by funext i j; ring
  have hA : (fun r i j => A r i j + t * A r i j) =
      (fun r i j => (1 + t) * A r i j) := by funext r i j; ring
  have hdA : (fun a r i j => dA a r i j + t * (2 * dA a r i j)) =
      (fun a r i j => (1 + 2 * t) * dA a r i j) := by funext a r i j; ring
  rw [hq, hA, hdA]
  rfl

theorem dilationRay_expansion (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) (t : ℝ) :
    dilationRay c q A dA t =
      (1 + 2 * t) ^ 2 * pairing q (linearRicci dA) +
      (1 + t) ^ 2 * ((1 - c) * pairing background (quadraticRicci A) +
        (c * pairing q (quadraticRicci A)) * (1 + 2 * t)) := by
  unfold dilationRay comparisonDensity
  rw [linearRicci_smul, quadraticRicci_smul]
  simp only [pairing_smul_left, pairing_smul_right]
  ring

theorem dilationRay_hasDerivAt_zero (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) :
    HasDerivAt (dilationRay c q A dA)
      (4 * pairing q (linearRicci dA) +
        2 * (1 - c) * pairing background (quadraticRicci A) +
        4 * c * pairing q (quadraticRicci A)) 0 := by
  have htwo : HasDerivAt (fun t : ℝ => 1 + 2 * t) 2 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).const_mul 2).const_add 1 using 1 <;> ring
  have hone : HasDerivAt (fun t : ℝ => 1 + t) 1 0 := by
    convert! (hasDerivAt_id (0 : ℝ)).const_add 1 using 1 <;> ring
  have h := ((htwo.pow 2).mul_const (pairing q (linearRicci dA))).add
    ((hone.pow 2).mul
      ((hasDerivAt_const (0 : ℝ)
        ((1 - c) * pairing background (quadraticRicci A))).add
        (htwo.const_mul (c * pairing q (quadraticRicci A)))))
  have heq : dilationRay c q A dA = fun t =>
      (1 + 2 * t) ^ 2 * pairing q (linearRicci dA) +
      (1 + t) ^ 2 * ((1 - c) * pairing background (quadraticRicci A) +
        (c * pairing q (quadraticRicci A)) * (1 + 2 * t)) :=
    funext (dilationRay_expansion c q A dA)
  rw [heq]
  convert! h using 1 <;> norm_num <;> ring

def dilationWardResidual (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) : ℝ :=
  deriv (dilationRay c q A dA) 0 - 4 * comparisonDensity c q A dA

/-- This residual is obtained from the derivative, not defined to vanish. -/
theorem dilationWardResidual_eq (c : ℝ) (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) :
    dilationWardResidual c q A dA =
      2 * (c - 1) * pairing background (quadraticRicci A) := by
  rw [dilationWardResidual, (dilationRay_hasDerivAt_zero c q A dA).deriv]
  unfold comparisonDensity
  ring

theorem generated_dilationWard (q : Tensor) (A : Connection)
    (dA : ConnectionDerivative) : dilationWardResidual 1 q A dA = 0 := by
  rw [dilationWardResidual_eq]
  ring

/-- A torsion-free source-coordinate configuration detects the cubic term. -/
def witnessConnection : Connection := fun r i j =>
  if r = 0 ∧ i = 1 ∧ j = 1 then 1
  else if r = 1 ∧ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) then 2 else 0

theorem witnessConnection_torsionFree (r i j : Index) :
    witnessConnection r i j = witnessConnection r j i := by
  fin_cases r <;> fin_cases i <;> fin_cases j <;> norm_num [witnessConnection]

theorem witnessConnection_contraction :
    pairing background (quadraticRicci witnessConnection) = -2 := by
  norm_num [pairing, background, quadraticRicci, witnessConnection, Fin.sum_univ_succ]

/-- Even the affine part of nonlinear covariance forces unit self-coupling. -/
theorem cubicCoefficient_unique {c : ℝ}
    (hward : dilationWardResidual c background witnessConnection (fun _ _ _ _ => 0) = 0) :
    c = 1 := by
  rw [dilationWardResidual_eq, witnessConnection_contraction] at hward
  linarith

/-- Covariance throughout the comparison class holds for exactly one coefficient. -/
theorem cubicCoefficient_iff (c : ℝ) :
    (∀ q A dA, dilationWardResidual c q A dA = 0) ↔ c = 1 := by
  constructor
  · intro h
    exact cubicCoefficient_unique (h background witnessConnection (fun _ _ _ _ => 0))
  · rintro rfl
    exact generated_dilationWard

structure Conclusions : Prop where
  density_weight : ∀ q, densityLieAtOrigin q dilationGradient = fun i j => 2 * q i j
  connection_weight : ∀ A, connectionLieAtOrigin A dilationGradient = A
  derivative_weight : ∀ dA,
    connectionDerivativeLieAtOrigin dA dilationGradient = fun a r i j => 2 * dA a r i j
  nonlinear_covariance_test : ∀ q A dA, dilationWardResidual 1 q A dA = 0
  unique_cubic_coefficient : ∀ c,
    dilationWardResidual c background witnessConnection (fun _ _ _ _ => 0) = 0 → c = 1
  unique_covariant_member : ∀ c,
    (∀ q A dA, dilationWardResidual c q A dA = 0) ↔ c = 1
  actual_derivative : ∀ c q A dA,
    HasDerivAt (dilationRay c q A dA)
      (4 * pairing q (linearRicci dA) +
        2 * (1 - c) * pairing background (quadraticRicci A) +
        4 * c * pairing q (quadraticRicci A)) 0

/-- The nonlinear density and its unique relative cubic coefficient have
no supplied coupling or background-carrier argument. -/
theorem generated : Conclusions where
  density_weight := densityLieAtOrigin_dilation
  connection_weight := connectionLieAtOrigin_dilation
  derivative_weight := connectionDerivativeLieAtOrigin_dilation
  nonlinear_covariance_test := generated_dilationWard
  unique_cubic_coefficient := fun _ => cubicCoefficient_unique
  unique_covariant_member := cubicCoefficient_iff
  actual_derivative := dilationRay_hasDerivAt_zero

end GeneratedFoundations.Physical.SourceNonlinearTensorAction
