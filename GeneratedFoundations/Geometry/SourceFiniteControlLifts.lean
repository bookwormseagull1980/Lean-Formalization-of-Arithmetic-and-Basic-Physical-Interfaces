module

public import GeneratedFoundations.Geometry.SourceFiniteRotations
public import GeneratedFoundations.Geometry.SourceDirectionalStep
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# Lifts of the finite rotation controls

Unit quaternions implement the four sign rotations, the quarter turn, and
the cyclic permutation in the source group. Their products lift all 24
controls. Conjugation intertwines the directional generators, their matrix
exponentials, and the corresponding Gaussian corner operations.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Quaternion Matrix
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceQuaternionAmplitude
open GeneratedFoundations.Geometry.SourceAxisMetric
open GeneratedFoundations.Geometry.SourceDirectionalStep
open GeneratedFoundations.Geometry.SourceDirectionalGenerator (Direction)
open GeneratedFoundations.Geometry.SourceFiniteRotations

namespace GeneratedFoundations.Geometry.SourceFiniteControlLifts

def halfSqrt : ℝ := Real.sqrt 2 / 2

private theorem halfSqrt_sq : halfSqrt ^ 2 = (1 / 2 : ℝ) := by
  unfold halfSqrt
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- The source axes have quaternion coordinates `k`, `-j`, and `-i`. -/
def signQuaternion (d : Fin 4) : ℍ :=
  ![1, unitQuaternion 0, unitQuaternion 1, unitQuaternion 2] d

def quarterQuaternion (q : Fin 2) : ℍ :=
  ![1, ⟨halfSqrt, halfSqrt, 0, 0⟩] q

def cycleQuaternion (c : Fin 3) : ℍ :=
  ![1, ⟨1 / 2, 1 / 2, 1 / 2, -1 / 2⟩,
    ⟨-1 / 2, 1 / 2, 1 / 2, -1 / 2⟩] c

@[simp] theorem normSq_signQuaternion (d : Fin 4) :
    Quaternion.normSq (signQuaternion d) = 1 := by
  fin_cases d <;> norm_num [signQuaternion, unitQuaternion, Quaternion.normSq_def']

@[simp] theorem normSq_quarterQuaternion (q : Fin 2) :
    Quaternion.normSq (quarterQuaternion q) = 1 := by
  fin_cases q <;> norm_num [quarterQuaternion, Quaternion.normSq_def', halfSqrt_sq]

@[simp] theorem normSq_cycleQuaternion (c : Fin 3) :
    Quaternion.normSq (cycleQuaternion c) = 1 := by
  fin_cases c <;> norm_num [cycleQuaternion, Quaternion.normSq_def']

theorem signQuaternion_conj (d : Fin 4) (ξ : Direction) :
    signQuaternion d * directionQuaternion ξ * star (signQuaternion d) =
      directionQuaternion (signFlip d ξ) := by
  fin_cases d <;> ext <;>
    simp [signQuaternion, signFlip, directionQuaternion, unitQuaternion,
      Fin.sum_univ_three] <;> ring

theorem quarterQuaternion_conj (q : Fin 2) (ξ : Direction) :
    quarterQuaternion q * directionQuaternion ξ * star (quarterQuaternion q) =
      directionQuaternion (quarter q ξ) := by
  fin_cases q <;> ext <;>
    simp [quarterQuaternion, quarter, directionQuaternion, unitQuaternion,
      Fin.sum_univ_three]
  all_goals (ring_nf; simp [halfSqrt_sq]; ring)

theorem cycleQuaternion_conj (c : Fin 3) (ξ : Direction) :
    cycleQuaternion c * directionQuaternion ξ * star (cycleQuaternion c) =
      directionQuaternion (cycle c ξ) := by
  fin_cases c <;> ext <;>
    simp [cycleQuaternion, cycle, directionQuaternion, unitQuaternion,
      Fin.sum_univ_three] <;> ring

private theorem conjugation_mul (p q x : ℍ) :
    (p * q) * x * star (p * q) = p * (q * x * star q) * star p := by
  simp only [star_mul, mul_assoc]

def controlQuaternion (r : Control) : ℍ :=
  cycleQuaternion r.1 * quarterQuaternion r.2.1 * signQuaternion r.2.2

@[simp] theorem normSq_controlQuaternion (r : Control) :
    Quaternion.normSq (controlQuaternion r) = 1 := by
  simp only [controlQuaternion, map_mul, normSq_signQuaternion,
    normSq_quarterQuaternion, normSq_cycleQuaternion, one_mul]

theorem controlQuaternion_conj (r : Control) (ξ : Direction) :
    controlQuaternion r * directionQuaternion ξ * star (controlQuaternion r) =
      directionQuaternion (rotate r ξ) := by
  unfold controlQuaternion
  rw [conjugation_mul, conjugation_mul, signQuaternion_conj,
    quarterQuaternion_conj, cycleQuaternion_conj]
  rfl

def controlLift (r : Control) : SU2 :=
  ⟨matrixMap (controlQuaternion r),
    (matrixMap_mem_specialUnitary_iff _).mpr (normSq_controlQuaternion r)⟩

@[simp] theorem controlLift_coe (r : Control) :
    (controlLift r : Mat2) = matrixMap (controlQuaternion r) := rfl

theorem controlLift_generator_conj (r : Control) (ξ : Direction) :
    (controlLift r : Mat2) * generator ξ * (controlLift r : Mat2).conjTranspose =
      generator (rotate r ξ) := by
  rw [controlLift_coe, ← matrixMap_directionQuaternion, ← matrixMap_star,
    ← map_mul, ← map_mul, controlQuaternion_conj, matrixMap_directionQuaternion]

private def controlUnits (r : Control) : Mat2ˣ where
  val := controlLift r
  inv := (controlLift r : Mat2).conjTranspose
  val_inv := (Matrix.mem_specialUnitaryGroup_iff.mp (controlLift r).property).1.2
  inv_val := (Matrix.mem_specialUnitaryGroup_iff.mp (controlLift r).property).1.1

theorem controlLift_matrixStep_conj (r : Control) (ξ : Direction) (t : ℝ) :
    (controlLift r : Mat2) * matrixStep ξ t * (controlLift r : Mat2).conjTranspose =
      matrixStep (rotate r ξ) t := by
  have hexp := Matrix.exp_units_conj (controlUnits r) ((t : ℂ) • generator ξ)
  change NormedSpace.exp
      ((controlLift r : Mat2) * ((t : ℂ) • generator ξ) *
        (controlLift r : Mat2).conjTranspose) =
    (controlLift r : Mat2) * matrixStep ξ t * (controlLift r : Mat2).conjTranspose at hexp
  rw [mul_smul_comm, smul_mul_assoc, controlLift_generator_conj] at hexp
  exact hexp.symm

theorem controlLift_step_conj (r : Control) (ξ : Direction) (t : ℝ) :
    controlLift r * step ξ t * (controlLift r)⁻¹ = step (rotate r ξ) t := by
  apply Subtype.ext
  exact controlLift_matrixStep_conj r ξ t

/-- Changing the sign of a lift leaves conjugation unchanged. -/
theorem neg_conjugation (U M : Mat2) :
    (-U) * M * (-U).conjTranspose = U * M * U.conjTranspose := by
  simp

def oppositeLift (r : Control) : SU2 := negativeIdentity * controlLift r

@[simp] theorem oppositeLift_coe (r : Control) :
    (oppositeLift r : Mat2) = -(controlLift r : Mat2) := by
  change (negativeIdentity : Mat2) * (controlLift r : Mat2) = _
  rw [negativeIdentity_coe, neg_one_mul]

theorem oppositeLift_generator_conj (r : Control) (ξ : Direction) :
    (oppositeLift r : Mat2) * generator ξ * (oppositeLift r : Mat2).conjTranspose =
      generator (rotate r ξ) := by
  rw [oppositeLift_coe, neg_conjugation, controlLift_generator_conj]

theorem oppositeLift_step_conj (r : Control) (ξ : Direction) (t : ℝ) :
    oppositeLift r * step ξ t * (oppositeLift r)⁻¹ = step (rotate r ξ) t := by
  apply Subtype.ext
  change (oppositeLift r : Mat2) * matrixStep ξ t *
    (oppositeLift r : Mat2).conjTranspose = matrixStep (rotate r ξ) t
  rw [oppositeLift_coe, neg_conjugation, controlLift_matrixStep_conj]

theorem controlLift_generated (r : Control) :
    controlLift r ∈ Subgroup.closure (Set.range zElement ∪ Set.range yElement) := by
  rw [generated_subgroup_eq_top]
  trivial

theorem controlLift_source_axes (r : Control) :
    ∃ a b c : ℝ,
      (controlLift r : Mat2) =
        NormedSpace.exp ((Complex.I * a) • spinMatrix3) *
        NormedSpace.exp ((Complex.I * b) • spinMatrix2) *
        NormedSpace.exp ((Complex.I * c) • spinMatrix3) :=
  source_axes_generate_all _ (controlLift r).property

theorem controlLift_controlledStep_conj {b : ℝ} (hb : 0 < b)
    (r : Control) (ξ : Direction) (t : ℝ) :
    control hb (controlLift r) * controlledStep hb ξ t *
        (control hb (controlLift r)).adjoint =
      controlledStep hb (rotate r ξ) t := by
  rw [control_adjoint]
  change control hb (controlLift r) * control hb (matrixStep ξ t) *
      control hb (controlLift r : Mat2).conjTranspose =
    control hb (matrixStep (rotate r ξ) t)
  rw [← control_mul, ← control_mul, controlLift_matrixStep_conj]

end GeneratedFoundations.Geometry.SourceFiniteControlLifts
