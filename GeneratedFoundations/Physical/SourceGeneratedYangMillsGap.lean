module

public import GeneratedFoundations.Physical.SourceRadialMassIntertwiner
public import GeneratedFoundations.Physical.SourceAdjointComparison
public import GeneratedFoundations.Physical.SourceRP3FieldSpectrum
public import GeneratedFoundations.Geometry.SourceProjectiveVolume
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

`L` is a variable internal radius.  V5 evaluates this operator at the
finite-response TT endpoint `kL`; the zero-argument `CanonicalYangMills`
module evaluates it at the Gaussian IR edge `sqrt(2*pi)`.  This file proves
the common `L > criticalRadius` statement and does **not** identify those two
radii.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Physical.SourceConformalResponse
open GeneratedFoundations.Physical.SourceInternalYangMillsResponse
open GeneratedFoundations.Physical.SourceRadialMassIntertwiner
open GeneratedFoundations.Physical.SourceRP3FieldSpectrum
open GeneratedFoundations.Physical.SourceAdjointComparison

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsGap

/-- Round volume computed from the original ambient radial flux and the
actual two-sheeted source covering. -/
def projectiveRoundVolume (L : ℝ) : ℝ :=
  Geometry.SourceProjectiveVolume.roundVolume L

theorem projectiveRoundVolume_eq (L : ℝ) :
    projectiveRoundVolume L = Real.pi ^ 2 * L ^ 3 :=
  Geometry.SourceProjectiveVolume.roundVolume_eq L

/-- The source-generated adjoint-Casimir feedback coefficient: the computed
colour normalization divided by the round projective volume. -/
def generatedFeedback (L : ℝ) : ℝ :=
  colourNormalizationRatio / projectiveRoundVolume L

theorem generatedFeedback_eq (L : ℝ) :
    generatedFeedback L = 3 / (8 * Real.pi ^ 2 * L ^ 3) := by
  simp [generatedFeedback, projectiveRoundVolume_eq, colourNormalizationRatio_eq]
  ring

theorem generatedFeedback_pos {L : ℝ} (hL : 0 < L) :
    0 < generatedFeedback L := by
  rw [generatedFeedback_eq]
  positivity

/-- The generated restoring target, with no independent coupling input. -/
def generatedTarget (L : ℝ) : ℝ :=
  responseTarget L (generatedFeedback L) / adjointTraceMultiplicity

/-- Dimensionless response coordinate carried by a Gaussian connection of
source intensity `q`.  The factor is the already generated colour feedback
and the square of the internal radius; no independent conversion constant is
introduced. -/
def generatedDimensionlessIntensity (L q : ℝ) : ℝ :=
  generatedFeedback L * L ^ 2 * q

/-- The colour-covariance shift obtained from the same generated Gaussian
connection source. The contraction proved below computes its coefficient
from the 24 isotropic components, two transverse directions and adjoint
Casimir three. -/
def gaussianColourResponseShift (L q : ℝ) : ℝ :=
  (2 / 3 : ℝ) * generatedFeedback L * q

/-- The pointwise connection has the three generated spatial directions and
the eight trace-normalized colour directions. -/
def spatialColourComponentCount : ℕ := Fintype.card (Fin 3 × Fin 8)

theorem spatialColourComponentCount_eq : spatialColourComponentCount = 24 := by
  norm_num [spatialColourComponentCount]

/-- Equal component variance with total source intensity `q` per generated
projective volume. This fixes the covariance normalization before contraction. -/
def connectionComponentVariance (L q : ℝ) : ℝ :=
  q / ((spatialColourComponentCount : ℝ) * projectiveRoundVolume L)

theorem connectionComponentVariance_total (L q : ℝ) :
    (spatialColourComponentCount : ℝ) * connectionComponentVariance L q =
      q / projectiveRoundVolume L := by
  simp only [connectionComponentVariance, spatialColourComponentCount_eq]
  norm_num
  ring

/-- Isotropy and the given total intensity determine that component variance
uniquely; no covariance scale remains to be chosen. -/
theorem connectionComponentVariance_unique (L q v : ℝ)
    (hv : (spatialColourComponentCount : ℝ) * v = q / projectiveRoundVolume L) :
    v = connectionComponentVariance L q := by
  have hc := connectionComponentVariance_total L q
  rw [spatialColourComponentCount_eq] at hv hc
  nlinarith

/-- The contraction of one connection direction with the other spatial
directions uses the actual colour double commutator, not a Casimir label. -/
def transverseCovarianceAction (L q : ℝ) (i : Fin 3)
    (X : SourceColourAdjointCasimir.ColourMatrix) :
    SourceColourAdjointCasimir.ColourMatrix :=
  ∑ _j ∈ Finset.univ.erase i,
    (connectionComponentVariance L q : ℂ) •
      SourceColourAdjointCasimir.adjointCasimirOperator X

theorem six_mul_connectionComponentVariance (L q : ℝ) :
    6 * connectionComponentVariance L q = gaussianColourResponseShift L q := by
  simp [connectionComponentVariance, spatialColourComponentCount_eq,
    gaussianColourResponseShift, generatedFeedback, colourNormalizationRatio_eq,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- The actual double-commutator contraction computes precisely the existing
Gaussian response shift. The two transverse directions and adjoint Casimir
three are calculated before the common coefficient is read off. -/
theorem transverseCovarianceAction_eq (L q : ℝ) (i : Fin 3)
    (X : SourceColourAdjointCasimir.ColourMatrix) (hX : Matrix.trace X = 0) :
    transverseCovarianceAction L q i X = (gaussianColourResponseShift L q : ℂ) • X := by
  have hc : (Finset.univ.erase i).card = 2 := by simp
  unfold transverseCovarianceAction
  rw [SourceColourAdjointCasimir.adjointCasimir_of_trace_zero X hX,
    Finset.sum_const, hc]
  rw [two_nsmul, ← add_smul, smul_smul]
  have hs : (connectionComponentVariance L q : ℂ) + connectionComponentVariance L q =
      ((2 * connectionComponentVariance L q : ℝ) : ℂ) := by push_cast; ring
  rw [hs]
  have hf : ((2 * connectionComponentVariance L q : ℝ) : ℂ) * 3 =
      (gaussianColourResponseShift L q : ℂ) := by
    have hh := congrArg Complex.ofReal (six_mul_connectionComponentVariance L q)
    push_cast at hh ⊢
    linear_combination hh
  rw [hf]

/-- The source-normalized radial mass squared.  The factor 120 is the actual
number of long-root colour-connection coefficients. -/
def normalizedRadialMassSq (z : ℝ) : ℝ :=
  adjointTraceMultiplicity * z * generatedRadialGap z / (2 * coefficientCount)

/-- The normalized radial coefficient is not an independent mass insertion.
It is exactly the variance of the source-generated intensity score multiplied
by the curvature of the complete restoring response. -/
theorem normalizedRadialMassSq_eq_scoreVariance_mul_adjointCurvature
    (z : ℝ) :
    normalizedRadialMassSq z = scoreVariance z * adjointCurvature z := by
  unfold normalizedRadialMassSq scoreVariance generatedRadialGap adjointCurvature
  ring

theorem normalizedRadialMassSq_pos {z : ℝ} (hz : 0 < z) :
    0 < normalizedRadialMassSq z := by
  unfold normalizedRadialMassSq
  exact div_pos (mul_pos (mul_pos adjointTraceMultiplicity_pos hz)
    (generatedRadialGap_pos hz))
    (mul_pos (by norm_num) coefficientCount_pos)

/-- Common response shift of the coclosed colour-connection tower. -/
def coclosedResponseShift (L z : ℝ) : ℝ := 2 * z / (3 * L ^ 2)

/-- After the generated dimensionless change of variables, the shift used by
the coclosed tower is exactly the Gaussian colour-covariance shift. -/
theorem coclosedResponseShift_generatedIntensity {L q : ℝ} (hL : L ≠ 0) :
    coclosedResponseShift L (generatedDimensionlessIntensity L q) =
      gaussianColourResponseShift L q := by
  unfold coclosedResponseShift generatedDimensionlessIntensity
    gaussianColourResponseShift
  field_simp [hL]

theorem coclosedResponseShift_pos {L z : ℝ} (hL : 0 < L) (hz : 0 < z) :
    0 < coclosedResponseShift L z := by
  unfold coclosedResponseShift
  positivity

/-- Mass squared of a projective coclosed colour-connection shell. -/
def coclosedMassIndex (L z : ℝ) (l : ℕ) : ℝ :=
  vectorEigenvalue L l + coclosedResponseShift L z

/-- The `i`-th shell in a finite RP3 coclosed cutoff.  Ordinary one-forms
descend only at positive odd degree, so a cutoff enumerates `1,3,5,...`
rather than all positive natural degrees. -/
def coclosedShellDegree (i : ℕ) : ℕ := 2 * i + 1

@[simp] theorem coclosedShellDegree_zero : coclosedShellDegree 0 = 1 := by
  rfl

theorem coclosedShellDegree_positive (i : ℕ) : 1 ≤ coclosedShellDegree i := by
  simp [coclosedShellDegree]

theorem coclosedShellDegree_vectorDegree (i : ℕ) :
    VectorDegree (coclosedShellDegree i) := by
  constructor
  · exact ⟨i, by simp [coclosedShellDegree, Nat.two_mul]⟩
  · exact coclosedShellDegree_positive i

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
    existsUnique_root_with_scalarGap (div_pos
      (responseTarget_pos hL (generatedFeedback_pos hLp)) adjointTraceMultiplicity_pos)
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
