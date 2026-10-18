module

public import GeneratedFoundations.Physical.SourceInternalYangMillsResponse
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The generated radial block and the scalar constant mode

The manuscript's colour-intensity score and scalar constant mode are both
one-dimensional after normalization.  This file records that finite block
exactly: the score normalization, the unique complex unitary sending the
normalized radial generator to the normalized constant generator, and the
intertwining of the common scalar mass semigroup.  The coefficient positivity
uses the same generated conformal curvature and long-root eigenvalue.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Physical.SourceConformalResponse
open GeneratedFoundations.Physical.SourceInternalYangMillsResponse

namespace GeneratedFoundations.Physical.SourceRadialMassIntertwiner

/-- Number of long-root colour connection coefficients already computed from
the generated colour and source carriers. -/
def coefficientCount : ℝ := connectionCoefficientCount

@[simp] theorem coefficientCount_eq : coefficientCount = 120 := by
  norm_num [coefficientCount]

/-- Variance of the normalized quadratic intensity coordinate. -/
def scoreVariance (q : ℝ) : ℝ := 2 * q ^ 2 / coefficientCount

/-- The radial score normalization used by the generated intensity block. -/
def scoreScale (q : ℝ) : ℝ := Real.sqrt (coefficientCount / 2) / q

theorem coefficientCount_pos : 0 < coefficientCount := by
  norm_num [coefficientCount]

theorem scoreScale_sq_mul_variance {q : ℝ} (hq : q ≠ 0) :
    scoreScale q ^ 2 * scoreVariance q = 1 := by
  have hhalf : 0 ≤ coefficientCount / 2 := by
    exact (div_nonneg coefficientCount_pos.le (by norm_num))
  rw [scoreScale, scoreVariance, div_pow, Real.sq_sqrt hhalf]
  field_simp [hq, coefficientCount_pos.ne']

/-- After choosing the normalized generators, both one-dimensional blocks
have the same intrinsic coordinate space. -/
abbrev RadialBlock := ℂ

abbrev ScalarConstantBlock := ℂ

/-- The generated normalized radial-to-constant unitary. -/
def radialToConstant : RadialBlock ≃ₗᵢ[ℂ] ScalarConstantBlock :=
  LinearIsometryEquiv.refl ℂ ℂ

@[simp] theorem radialToConstant_generator :
    radialToConstant (1 : RadialBlock) = (1 : ScalarConstantBlock) := by
  rfl

/-- A complex-linear isometry between the normalized one-dimensional blocks
is fixed uniquely by the image of the generated unit vector. -/
theorem radialToConstant_unique
    (U : RadialBlock ≃ₗᵢ[ℂ] ScalarConstantBlock)
    (hU : U (1 : RadialBlock) = (1 : ScalarConstantBlock)) :
    U = radialToConstant := by
  apply LinearIsometryEquiv.ext
  intro z
  calc
    U z = U (z • (1 : RadialBlock)) := by simp
    _ = z • U (1 : RadialBlock) := U.map_smul z 1
    _ = z := by simp [hU]
    _ = radialToConstant z := rfl

/-- Scalar heat evolution on either normalized one-dimensional restriction. -/
def scalarMassEvolution (massSq time : ℝ) (z : ℂ) : ℂ :=
  (Real.exp (-time * massSq) : ℂ) * z

/-- The unique normalized unitary intertwines the two restrictions for every
mass and evolution parameter. -/
theorem radialToConstant_intertwines (massSq time : ℝ) (z : RadialBlock) :
    radialToConstant (scalarMassEvolution massSq time z) =
      scalarMassEvolution massSq time (radialToConstant z) := by
  rfl

/-- Coefficient of the normalized radial source projected onto the scalar
constant block, written entirely with the generated long-root eigenvalue,
complete curvature and response amplitude. -/
def radialProjectionCoefficient (L z : ℝ) : ℝ :=
  (longRootEigenvalue L + 2 * completeCurvature z * z) * z *
    Real.sqrt (2 / coefficientCount)

theorem radialProjectionCoefficient_pos {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) :
    0 < radialProjectionCoefficient L z := by
  have heigen : 0 < longRootEigenvalue L := by
    rw [longRootEigenvalue_eq]
    exact div_pos (by norm_num) (sq_pos_of_pos hL)
  have hcurv : 0 < completeCurvature z := completeCurvature_pos hz.le
  have hsqrt : 0 < Real.sqrt (2 / coefficientCount) := by
    apply Real.sqrt_pos.2
    exact div_pos (by norm_num) coefficientCount_pos
  unfold radialProjectionCoefficient
  exact mul_pos (mul_pos (add_pos heigen (mul_pos (mul_pos (by norm_num) hcurv) hz)) hz)
    hsqrt

/-- The finite conclusions of the generated radial/scalar identification. -/
structure Properties : Prop where
  coefficient_count : coefficientCount = 120
  score_normalized : ∀ {q : ℝ}, q ≠ 0 →
    scoreScale q ^ 2 * scoreVariance q = 1
  unitary_generator : radialToConstant (1 : RadialBlock) =
    (1 : ScalarConstantBlock)
  unitary_unique : ∀ U : RadialBlock ≃ₗᵢ[ℂ] ScalarConstantBlock,
    U 1 = 1 → U = radialToConstant
  semigroup_intertwining : ∀ massSq time z,
    radialToConstant (scalarMassEvolution massSq time z) =
      scalarMassEvolution massSq time (radialToConstant z)
  positive_projection : ∀ {L z : ℝ}, 0 < L → 0 < z →
    0 < radialProjectionCoefficient L z

theorem properties : Properties where
  coefficient_count := coefficientCount_eq
  score_normalized := fun hq => scoreScale_sq_mul_variance hq
  unitary_generator := radialToConstant_generator
  unitary_unique := fun U hU => radialToConstant_unique U hU
  semigroup_intertwining := radialToConstant_intertwines
  positive_projection := fun hL hz => radialProjectionCoefficient_pos hL hz

end GeneratedFoundations.Physical.SourceRadialMassIntertwiner
