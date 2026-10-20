module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel

/-!
# Connection jets and their noncommutative curvature

These are algebraic jet identities over an arbitrary unital ring. The value
of a change of frame is a unit; its first and symmetric second derivatives
remain jet variables. The transformation of the connection jet is the product
rule, from which curvature covariance is proved. No curvature covariance or
vanishing mixed term is included as a premise.

The Bianchi identity separately uses the symmetry of the actual second-jet
slots. These finite identities make no claim that an arbitrary algebraic jet
is realized by a differentiable group-valued map.
-/

@[expose] public section

namespace GeneratedFoundations.Geometry.ConnectionJetAlgebra

variable {ι A : Type*} [Ring A]

structure ConnectionJet (ι A : Type*) where
  value : ι → A
  derivative : ι → ι → A

def curvature (C : ConnectionJet ι A) (μ ν : ι) : A :=
  C.derivative μ ν - C.derivative ν μ +
    (C.value μ * C.value ν - C.value ν * C.value μ)

theorem curvature_swap (C : ConnectionJet ι A) (μ ν : ι) :
    curvature C ν μ = -curvature C μ ν := by
  simp only [curvature]
  abel

@[simp] theorem curvature_self (C : ConnectionJet ι A) (μ : ι) :
    curvature C μ μ = 0 := by simp [curvature]

def zeroConnectionJet : ConnectionJet ι A := ⟨fun _ => 0, fun _ _ => 0⟩

@[simp] theorem zeroConnection_flat (μ ν : ι) :
    curvature (zeroConnectionJet : ConnectionJet ι A) μ ν = 0 := by
  simp [curvature, zeroConnectionJet]

def add (C B : ConnectionJet ι A) : ConnectionJet ι A :=
  ⟨fun μ => C.value μ + B.value μ, fun μ ν => C.derivative μ ν + B.derivative μ ν⟩

/-- The mixed connection term is retained before any quadratic estimate. -/
theorem curvature_add (C B : ConnectionJet ι A) (μ ν : ι) :
    curvature (add C B) μ ν = curvature C μ ν + curvature B μ ν +
      (C.value μ * B.value ν + B.value μ * C.value ν -
        C.value ν * B.value μ - B.value ν * C.value μ) := by
  simp only [curvature, add]
  noncomm_ring

structure GaugeTwoJet (ι A : Type*) [Ring A] where
  value : Aˣ
  first : ι → A
  second : ι → ι → A
  mixed_second : ∀ μ ν, second μ ν = second ν μ

def inverseDerivative (q : GaugeTwoJet ι A) (μ : ι) : A :=
  -((↑q.value⁻¹ : A) * q.first μ * (↑q.value⁻¹ : A))

def conjugate (g : Aˣ) (X : A) : A := (↑g⁻¹ : A) * X * (↑g : A)

def transform (q : GaugeTwoJet ι A) (C : ConnectionJet ι A) : ConnectionJet ι A where
  value μ := (↑q.value⁻¹ : A) * C.value μ * (↑q.value : A) +
    (↑q.value⁻¹ : A) * q.first μ
  derivative μ ν :=
    inverseDerivative q μ * C.value ν * (↑q.value : A) +
    (↑q.value⁻¹ : A) * C.derivative μ ν * (↑q.value : A) +
    (↑q.value⁻¹ : A) * C.value ν * q.first μ +
    inverseDerivative q μ * q.first ν + (↑q.value⁻¹ : A) * q.second μ ν

/-- Noncommutative curvature covariance follows from the full product rule. -/
theorem curvature_transform (q : GaugeTwoJet ι A) (C : ConnectionJet ι A) (μ ν : ι) :
    curvature (transform q C) μ ν = conjugate q.value (curvature C μ ν) := by
  have huv : (↑q.value : A) * (↑q.value⁻¹ : A) = 1 := Units.mul_inv _
  have hvu : (↑q.value⁻¹ : A) * (↑q.value : A) = 1 := Units.inv_mul _
  have huv_assoc (X : A) : (↑q.value : A) * ((↑q.value⁻¹ : A) * X) = X := by
    rw [← mul_assoc, huv, one_mul]
  have hvu_assoc (X : A) : (↑q.value⁻¹ : A) * ((↑q.value : A) * X) = X := by
    rw [← mul_assoc, hvu, one_mul]
  have hmix := q.mixed_second μ ν
  simp only [curvature, transform, inverseDerivative, conjugate]
  noncomm_ring [huv, hvu, huv_assoc, hvu_assoc, hmix]

theorem conjugate_mul (g : Aˣ) (X Y : A) :
    conjugate g X * conjugate g Y = conjugate g (X * Y) := by
  simp [conjugate, mul_assoc]

structure ConnectionTwoJet (ι A : Type*) where
  firstJet : ConnectionJet ι A
  second : ι → ι → ι → A
  mixed_second : ∀ ξ μ ν, second ξ μ ν = second μ ξ ν

def curvatureDerivative (C : ConnectionTwoJet ι A) (ξ μ ν : ι) : A :=
  C.second ξ μ ν - C.second ξ ν μ +
    C.firstJet.derivative ξ μ * C.firstJet.value ν +
    C.firstJet.value μ * C.firstJet.derivative ξ ν -
    C.firstJet.derivative ξ ν * C.firstJet.value μ -
    C.firstJet.value ν * C.firstJet.derivative ξ μ

def covariantCurvature (C : ConnectionTwoJet ι A) (ξ μ ν : ι) : A :=
  curvatureDerivative C ξ μ ν +
    (C.firstJet.value ξ * curvature C.firstJet μ ν -
      curvature C.firstJet μ ν * C.firstJet.value ξ)

/-- The full cyclic identity includes all derivative and commutator terms. -/
theorem bianchi (C : ConnectionTwoJet ι A) (ξ μ ν : ι) :
    covariantCurvature C ξ μ ν + covariantCurvature C μ ν ξ +
      covariantCurvature C ν ξ μ = 0 := by
  have h₁ := C.mixed_second ξ μ ν
  have h₂ := C.mixed_second μ ν ξ
  have h₃ := C.mixed_second ν ξ μ
  simp only [covariantCurvature, curvatureDerivative, curvature]
  noncomm_ring [h₁, h₂, h₃]

end GeneratedFoundations.Geometry.ConnectionJetAlgebra
