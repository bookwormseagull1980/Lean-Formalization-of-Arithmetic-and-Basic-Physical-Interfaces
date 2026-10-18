module

public import GeneratedFoundations.Physical.SourceRadialMassIntertwiner
public import GeneratedFoundations.Physical.SourceRP3FieldSpectrum
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The generated Yang--Mills spectral bottom

The minimal-change construction has already produced the critical radius,
the unique condensed response, the normalized radial/scalar identification
and the projective coclosed one-form tower.  This file combines those results
into the mass operator used by Paper 4 and V5.  Its two invariant blocks are
the normalized radial intensity and the coclosed colour connection.  Both
have a strictly positive bottom on the condensed branch, hence so does their
orthogonal direct sum.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Physical.SourceConformalResponse
open GeneratedFoundations.Physical.SourceInternalYangMillsResponse
open GeneratedFoundations.Physical.SourceRadialMassIntertwiner
open GeneratedFoundations.Physical.SourceRP3FieldSpectrum

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsGap

/-- Round volume of the generated projective internal carrier. -/
def projectiveRoundVolume (L : ℝ) : ℝ := Real.pi ^ 2 * L ^ 3

/-- The source-generated adjoint-Casimir feedback coefficient: the computed
colour normalization divided by the round projective volume. -/
def generatedFeedback (L : ℝ) : ℝ :=
  colourNormalizationRatio / projectiveRoundVolume L

theorem generatedFeedback_eq (L : ℝ) :
    generatedFeedback L = 3 / (8 * Real.pi ^ 2 * L ^ 3) := by
  simp [generatedFeedback, projectiveRoundVolume, colourNormalizationRatio_eq]
  ring

theorem generatedFeedback_pos {L : ℝ} (hL : 0 < L) :
    0 < generatedFeedback L := by
  rw [generatedFeedback_eq]
  positivity

/-- The generated restoring target, with no independent coupling input. -/
def generatedTarget (L : ℝ) : ℝ :=
  responseTarget L (generatedFeedback L)

/-- The source-normalized radial mass squared.  The factor 120 is the actual
number of long-root colour-connection coefficients. -/
def normalizedRadialMassSq (z : ℝ) : ℝ :=
  z * generatedRadialGap z / (2 * coefficientCount)

theorem normalizedRadialMassSq_pos {z : ℝ} (hz : 0 < z) :
    0 < normalizedRadialMassSq z := by
  unfold normalizedRadialMassSq
  exact div_pos (mul_pos hz (generatedRadialGap_pos hz))
    (mul_pos (by norm_num) coefficientCount_pos)

/-- Common response shift of the coclosed colour-connection tower. -/
def coclosedResponseShift (L z : ℝ) : ℝ := 2 * z / (3 * L ^ 2)

theorem coclosedResponseShift_pos {L z : ℝ} (hL : 0 < L) (hz : 0 < z) :
    0 < coclosedResponseShift L z := by
  unfold coclosedResponseShift
  positivity

/-- Mass squared of a projective coclosed colour-connection shell. -/
def coclosedMassIndex (L z : ℝ) (l : ℕ) : ℝ :=
  vectorEigenvalue L l + coclosedResponseShift L z

theorem coclosedMassIndex_pos {L z : ℝ} (hL : 0 < L) (hz : 0 < z)
    (l : ℕ) : 0 < coclosedMassIndex L z l := by
  unfold coclosedMassIndex
  exact add_pos (vectorEigenvalue_pos hL.ne' l)
    (coclosedResponseShift_pos hL hz)

theorem vectorCasimir_one_le {l : ℕ} (hl : 1 ≤ l) :
    vectorCasimir 1 ≤ vectorCasimir l := by
  have hlr : (1 : ℝ) ≤ l := by exact_mod_cast hl
  have hproduct : 0 ≤ ((l : ℝ) - 1) * ((l : ℝ) + 3) := by
    exact mul_nonneg (sub_nonneg.mpr hlr) (by positivity)
  norm_num [vectorCasimir]
  nlinarith

/-- The degree-one projective vector shell is the bottom of the full
coclosed tower. -/
theorem coclosedMassIndex_one_le {L z : ℝ} {l : ℕ} (hl : 1 ≤ l) :
    coclosedMassIndex L z 1 ≤ coclosedMassIndex L z l := by
  unfold coclosedMassIndex vectorEigenvalue
  have hdiv := div_le_div_of_nonneg_right
    (vectorCasimir_one_le hl) (sq_nonneg L)
  exact add_le_add_left hdiv _

/-- Spectral bottom of the orthogonal radial/coclosed direct sum. -/
def generatedYangMillsGapSq (L z : ℝ) : ℝ :=
  min (normalizedRadialMassSq z) (coclosedMassIndex L z 1)

theorem generatedYangMillsGapSq_pos {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) :
    0 < generatedYangMillsGapSq L z := by
  rw [generatedYangMillsGapSq, lt_min_iff]
  exact ⟨normalizedRadialMassSq_pos hz,
    coclosedMassIndex_pos hL hz 1⟩

theorem generatedYangMillsGapSq_le_radial (L z : ℝ) :
    generatedYangMillsGapSq L z ≤ normalizedRadialMassSq z := by
  exact min_le_left _ _

theorem generatedYangMillsGapSq_le_coclosed {L z : ℝ}
    {l : ℕ} (hl : 1 ≤ l) :
    generatedYangMillsGapSq L z ≤ coclosedMassIndex L z l := by
  exact (min_le_right _ _).trans (coclosedMassIndex_one_le hl)

/-- The normalized radial block and scalar constant mode carry the same mass
semigroup under their unique source-generated unitary. -/
theorem normalizedRadial_intertwines_scalarConstant (z time : ℝ)
    (v : RadialBlock) :
    radialToConstant
        (scalarMassEvolution (normalizedRadialMassSq z) time v) =
      scalarMassEvolution (normalizedRadialMassSq z) time
        (radialToConstant v) := by
  exact radialToConstant_intertwines (normalizedRadialMassSq z) time v

/-- Above the generated critical radius there is one and only one positive
condensed response coordinate, and its complete generated Yang--Mills mass
operator has a positive spectral bottom. -/
theorem existsUnique_generatedYangMillsGap {L : ℝ}
    (hL : criticalRadius < L) :
    ∃! z : ℝ,
      0 < z ∧ completeResponse z = generatedTarget L ∧
      0 < generatedYangMillsGapSq L z := by
  have hLp : 0 < L := criticalRadius_pos.trans hL
  obtain ⟨z, hz, hunique⟩ :=
    existsUnique_response_with_scalarGap hL (generatedFeedback_pos hLp)
  refine ⟨z, ⟨hz.1, hz.2.1, generatedYangMillsGapSq_pos hLp hz.1⟩, ?_⟩
  intro y hy
  apply hunique y
  exact ⟨hy.1, hy.2.1, generatedRadialGap_pos hy.1,
    fun j => generatedRadialGap_le_massIndex j y,
    generatedScalarMassIndex_zero y⟩

/-- Bundled theorem interface for the generated Yang--Mills sector. -/
structure Properties : Prop where
  radial_positive : ∀ {z : ℝ}, 0 < z → 0 < normalizedRadialMassSq z
  coclosed_positive : ∀ {L z : ℝ}, 0 < L → 0 < z → ∀ l,
    0 < coclosedMassIndex L z l
  coclosed_bottom : ∀ {L z : ℝ}, 0 < L → ∀ {l}, 1 ≤ l →
    coclosedMassIndex L z 1 ≤ coclosedMassIndex L z l
  complete_gap_positive : ∀ {L z : ℝ}, 0 < L → 0 < z →
    0 < generatedYangMillsGapSq L z
  condensed_branch : ∀ {L : ℝ}, criticalRadius < L →
    ∃! z : ℝ,
      0 < z ∧ completeResponse z = generatedTarget L ∧
      0 < generatedYangMillsGapSq L z
  radial_scalar_intertwining : ∀ z time (v : RadialBlock),
    radialToConstant
        (scalarMassEvolution (normalizedRadialMassSq z) time v) =
      scalarMassEvolution (normalizedRadialMassSq z) time
        (radialToConstant v)

theorem properties : Properties where
  radial_positive := normalizedRadialMassSq_pos
  coclosed_positive := fun hL hz l => coclosedMassIndex_pos hL hz l
  coclosed_bottom := by
    intro L z hL l hl
    exact coclosedMassIndex_one_le hl
  complete_gap_positive := generatedYangMillsGapSq_pos
  condensed_branch := existsUnique_generatedYangMillsGap
  radial_scalar_intertwining := normalizedRadial_intertwines_scalarConstant

end GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
