module

public import GeneratedFoundations.Geometry.SourceAxisMetric
public import GeneratedFoundations.Operations.SourceSpinCornerFlow
public import Mathlib.Analysis.Normed.Algebra.QuaternionExponential
public import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# Arbitrary directional steps of the original source

Every real combination of the three actual source velocities gives a
determinant-one unitary matrix exponential. Membership is proved through
the already constructed quaternion amplitude map: the same generator is
purely imaginary, so its exponential is a unit quaternion. No target-group
membership is an input. The half-angle normalization is retained, and the
same step acts on the original Gaussian corner with the complementary
identity required by its ambient Hilbert space.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Quaternion Matrix.Norms.Elementwise
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Operations.SourceSpinCornerFlow
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourcePolarMetric
open GeneratedFoundations.Geometry.SourceAxisMetric

namespace GeneratedFoundations.Geometry.SourceDirectionalStep

/-- A direction uses the actual half-angle source velocities `i J_a`. -/
def generator (ξ : Fin 3 → ℝ) : Mat2 :=
  ∑ a : Fin 3, (ξ a : ℂ) • axisVelocity a

theorem generator_eq_source_axes (ξ : Fin 3 → ℝ) :
    generator ξ = ∑ a : Fin 3, (ξ a : ℂ) • (Complex.I • spinMatrix a) := rfl

/-- The same direction in the original quaternion amplitude algebra. -/
def directionQuaternion (ξ : Fin 3 → ℝ) : ℍ :=
  ∑ a : Fin 3, (ξ a / 2) • unitQuaternion a

@[simp] theorem directionQuaternion_re (ξ : Fin 3 → ℝ) :
    (directionQuaternion ξ).re = 0 := by
  simp [directionQuaternion, Fin.sum_univ_three, unitQuaternion]

theorem directionQuaternion_continuous : Continuous directionQuaternion := by
  unfold directionQuaternion
  fun_prop

theorem matrixMap_directionQuaternion (ξ : Fin 3 → ℝ) :
    matrixMap (directionQuaternion ξ) = generator ξ := by
  simp only [directionQuaternion, generator, map_sum, map_smul,
    matrixMap_unitQuaternion, unitAxis,
    RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  push_cast
  ring_nf
  rfl

theorem generator_skew (ξ : Fin 3 → ℝ) :
    (generator ξ).conjTranspose = -generator ξ := by
  rw [← matrixMap_directionQuaternion, ← matrixMap_star,
    Quaternion.star_eq_neg.mpr (directionQuaternion_re ξ), map_neg]

theorem generator_trace (ξ : Fin 3 → ℝ) : Matrix.trace (generator ξ) = 0 := by
  rw [← matrixMap_directionQuaternion, trace_matrixMap, directionQuaternion_re]
  simp

/-- This is the actual matrix exponential, not a postulated group-valued curve. -/
def matrixStep (ξ : Fin 3 → ℝ) (t : ℝ) : Mat2 :=
  NormedSpace.exp ((t : ℂ) • generator ξ)

set_option backward.isDefEq.respectTransparency false in
open scoped Matrix.Norms.Operator in
theorem matrixMap_exp (q : ℍ) :
    matrixMap (NormedSpace.exp q) = NormedSpace.exp (matrixMap q) := by
  let +nondep : NormedAlgebra ℚ ℍ := .restrictScalars ℚ ℝ ℍ
  exact NormedSpace.map_exp matrixMap
    matrixMap.toLinearMap.continuous_of_finiteDimensional q

theorem matrixStep_eq_quaternion (ξ : Fin 3 → ℝ) (t : ℝ) :
    matrixStep ξ t = matrixMap (NormedSpace.exp (t • directionQuaternion ξ)) := by
  rw [matrixMap_exp, map_smul, matrixMap_directionQuaternion,
    RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

/-- All directions, including the zero direction, land in the actual source group. -/
theorem matrixStep_mem (ξ : Fin 3 → ℝ) (t : ℝ) : matrixStep ξ t ∈ SU2 := by
  rw [matrixStep_eq_quaternion, matrixMap_mem_specialUnitary_iff, Quaternion.normSq_exp]
  simp

@[simp] theorem matrixStep_zero (ξ : Fin 3 → ℝ) : matrixStep ξ 0 = 1 := by
  simp [matrixStep]

theorem matrixStep_add (ξ : Fin 3 → ℝ) (s t : ℝ) :
    matrixStep ξ (s + t) = matrixStep ξ s * matrixStep ξ t := by
  simp only [matrixStep, Complex.ofReal_add, add_smul]
  exact Matrix.exp_add_of_commute _ _
    (((Commute.refl (generator ξ)).smul_left (s : ℂ)).smul_right (t : ℂ))

private theorem map_curve_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {u : ℝ → E} {v : E} {t : ℝ}
    (hu : HasDerivAt u v t) :
    HasDerivAt (fun s => L (u s)) (L v) t :=
  L.hasFDerivAt.comp_hasDerivAt t hu

/-- Derivative in the original matrix topology, obtained from the same quaternion curve. -/
theorem matrixStep_hasDerivAt (ξ : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (matrixStep ξ) (matrixStep ξ t * generator ξ) t := by
  have h := map_curve_derivative (E := ℍ) (F := Mat2) matrixMapCLM
    (_root_.hasDerivAt_exp_smul_const (directionQuaternion ξ) t)
  change HasDerivAt
    (fun s : ℝ => matrixMap (NormedSpace.exp (s • directionQuaternion ξ)))
    (matrixMap (NormedSpace.exp (t • directionQuaternion ξ) * directionQuaternion ξ)) t at h
  simpa only [map_mul, ← matrixStep_eq_quaternion, matrixMap_directionQuaternion] using! h

theorem matrixStep_hasDerivAt_zero (ξ : Fin 3 → ℝ) :
    HasDerivAt (matrixStep ξ) (generator ξ) 0 := by
  simpa only [matrixStep_zero, one_mul] using matrixStep_hasDerivAt ξ 0

theorem matrixStep_continuous (ξ : Fin 3 → ℝ) : Continuous (matrixStep ξ) :=
  continuous_iff_continuousAt.mpr fun t => (matrixStep_hasDerivAt ξ t).continuousAt

theorem matrixStep_joint_continuous :
    Continuous (fun p : (Fin 3 → ℝ) × ℝ => matrixStep p.1 p.2) := by
  let +nondep : NormedAlgebra ℚ ℍ := .restrictScalars ℚ ℝ ℍ
  simp_rw [matrixStep_eq_quaternion]
  exact matrixMap.toLinearMap.continuous_of_finiteDimensional.comp
    (NormedSpace.exp_continuous.comp
      (continuous_snd.smul (directionQuaternion_continuous.comp continuous_fst)))

def step (ξ : Fin 3 → ℝ) (t : ℝ) : SU2 := ⟨matrixStep ξ t, matrixStep_mem ξ t⟩

@[simp] theorem step_coe (ξ : Fin 3 → ℝ) (t : ℝ) : (step ξ t : Mat2) = matrixStep ξ t := rfl

@[simp] theorem step_zero (ξ : Fin 3 → ℝ) : step ξ 0 = 1 :=
  Subtype.ext (matrixStep_zero ξ)

theorem step_add (ξ : Fin 3 → ℝ) (s t : ℝ) :
    step ξ (s + t) = step ξ s * step ξ t := Subtype.ext (matrixStep_add ξ s t)

theorem step_neg (ξ : Fin 3 → ℝ) (t : ℝ) : step ξ (-t) = (step ξ t)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← step_add, neg_add_cancel, step_zero]

theorem step_continuous (ξ : Fin 3 → ℝ) : Continuous (step ξ) :=
  (matrixStep_continuous ξ).subtype_mk _

theorem step_joint_continuous :
    Continuous (fun p : (Fin 3 → ℝ) × ℝ => step p.1 p.2) :=
  matrixStep_joint_continuous.subtype_mk _

theorem step_hasDerivAt (ξ : Fin 3 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (step ξ s : Mat2))
      ((step ξ t : Mat2) * generator ξ) t := matrixStep_hasDerivAt ξ t

theorem step_hasDerivAt_zero (ξ : Fin 3 → ℝ) :
    HasDerivAt (fun t : ℝ => (step ξ t : Mat2)) (generator ξ) 0 :=
  matrixStep_hasDerivAt_zero ξ

/-- The original Gaussian Hilbert space carries the very same directional step. -/
def controlledStep {b : ℝ} (hb : 0 < b) (ξ : Fin 3 → ℝ) (t : ℝ) : End :=
  control hb (matrixStep ξ t)

theorem controlledStep_mem_unitary {b : ℝ} (hb : 0 < b) (ξ : Fin 3 → ℝ) (t : ℝ) :
    controlledStep hb ξ t ∈ unitary End :=
  control_mem_unitary hb _ (Matrix.mem_specialUnitaryGroup_iff.mp (matrixStep_mem ξ t)).1

@[simp] theorem controlledStep_zero {b : ℝ} (hb : 0 < b) (ξ : Fin 3 → ℝ) :
    controlledStep hb ξ 0 = 1 := by simp [controlledStep]

theorem controlledStep_add {b : ℝ} (hb : 0 < b) (ξ : Fin 3 → ℝ) (s t : ℝ) :
    controlledStep hb ξ (s + t) = controlledStep hb ξ s * controlledStep hb ξ t := by
  simp only [controlledStep, matrixStep_add, control_mul]

/-- The complementary identity in `control` is retained in the source exponential. -/
theorem controlledStep_eq_exp {b : ℝ} (hb : 0 < b) (ξ : Fin 3 → ℝ) (t : ℝ) :
    controlledStep hb ξ t = NormedSpace.exp ((t : ℂ) • corner hb (generator ξ)) := by
  rw [← map_smul, exp_corner]
  rfl

end GeneratedFoundations.Geometry.SourceDirectionalStep
