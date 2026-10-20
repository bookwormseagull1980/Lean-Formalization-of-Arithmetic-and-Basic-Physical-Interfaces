module

public import GeneratedFoundations.Correlation.Endpoints
public import GeneratedFoundations.Geometry.SourceCoclosedSelection
public import GeneratedFoundations.Geometry.SourceLeftRightRepresentations
public import GeneratedFoundations.Physical.SourceColourAdjointCasimir
public import GeneratedFoundations.Physical.SourceConformalResponse
public import GeneratedFoundations.Physical.SourceRP3FieldSpectrum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public meta import Lean.Elab.Tactic.Omega

/-!
# Generated internal Yang--Mills response

The critical radius is the already constructed infrared/ultraviolet endpoint
ratio.  The degree-one coclosed vector shell is the lowest generated symmetry
shell.  The long-root degree is defined, rather than supplied, as the least
admissible positive odd coclosed degree strictly above that shell.  It is
proved to be uniquely degree three; its positive source branch is consequently
the `(4,2)` representation.  Its dimension and Casimir are then computed by
the uniform left--right theorems.  The drive is the unique unit-slope affine
function of that eigenvalue which vanishes at the generated critical radius.
No second fifteen-dimensional space, long-root bidegree, critical scale or
response target is supplied as input.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Correlation.Endpoints
open GeneratedFoundations.Geometry.SourceLeftRightRepresentations
open GeneratedFoundations.Physical.SourceColourAdjointCasimir
open GeneratedFoundations.Physical.SourceConformalResponse
open GeneratedFoundations.Physical.SourceRP3FieldSpectrum

namespace GeneratedFoundations.Physical.SourceInternalYangMillsResponse

export GeneratedFoundations.Geometry.SourceCoclosedSelection (
  degree_one_isVectorDegree
  exists_vectorDegree
  lowestSymmetryShellDegree
  lowestSymmetryShellDegree_spec
  lowestSymmetryShellDegree_minimal
  lowestSymmetryShellDegree_eq
  IsPostSymmetryCoclosedDegree
  degree_three_isPostSymmetryCoclosedDegree
  exists_postSymmetryCoclosedDegree
  longRootDegree
  longRootDegree_spec
  longRootDegree_minimal
  three_le_of_postSymmetryCoclosedDegree
  longRootDegree_eq
  longRootDegree_unique
  LongRootCarrier
  longRootCarrier_eq_carrier_four_two
  longRoot_finrank
  longRootCasimirIndex
  longRootCasimirIndex_eq
  criticalRadius
  criticalRadius_pos
  criticalRadius_ne_zero
  criticalRadius_eq_endpointRatio
  longRootEigenvalue
  longRootEigenvalue_eq
  longRootDrive
  longRootDrive_eq
  longRootDrive_critical
  IsUnitSlopeAffineDrive
  longRootDrive_isUnitSlopeAffine
  unitSlopeAffineDrive_unique
  longRootDrive_neg
)

/-- Dimensionless restoring target formed from the generated drive and a
positive effective coefficient. -/
def responseTarget (L coupling : ℝ) : ℝ :=
  -longRootDrive L / (2 * (coupling * L ^ 2))

theorem responseTarget_pos {L coupling : ℝ}
    (hL : criticalRadius < L) (hc : 0 < coupling) :
    0 < responseTarget L coupling := by
  unfold responseTarget
  have hLp : 0 < L := criticalRadius_pos.trans hL
  exact div_pos (neg_pos.2 (longRootDrive_neg hL))
    (mul_pos (by norm_num) (mul_pos hc (sq_pos_of_pos hLp)))

/-- The generated long-root drive therefore selects one positive restoring
amplitude and the corresponding positive scalar spectral bottom. -/
theorem existsUnique_response_with_scalarGap {L coupling : ℝ}
    (hL : criticalRadius < L) (hc : 0 < coupling) :
    ∃! z : ℝ,
      0 < z ∧ completeResponse z = responseTarget L coupling ∧
      0 < generatedRadialGap z ∧
      (∀ j, generatedRadialGap z ≤ generatedScalarMassIndex j z) ∧
      generatedScalarMassIndex 0 z = generatedRadialGap z :=
  existsUnique_root_with_scalarGap (responseTarget_pos hL hc)

/-- Eight colour directions and the actual fifteen-dimensional long-root
carrier give 120 connection coefficients. -/
def colourDirectionCount : ℕ := 8

def longRootDimension : ℕ := Module.finrank ℂ LongRootCarrier

def connectionCoefficientCount : ℕ := colourDirectionCount * longRootDimension

@[simp] theorem longRootDimension_eq : longRootDimension = 15 :=
  longRoot_finrank

@[simp] theorem connectionCoefficientCount_eq : connectionCoefficientCount = 120 := by
  norm_num [connectionCoefficientCount, colourDirectionCount]

/-- Algebraic colour normalization supplied by the computed adjoint Casimir
and the eight generated colour directions, before insertion of a geometric
volume. -/
def colourNormalizationRatio : ℝ :=
  adjointCasimirIndex / colourDirectionCount

@[simp] theorem colourNormalizationRatio_eq :
    colourNormalizationRatio = 3 / 8 := by
  norm_num [colourNormalizationRatio, colourDirectionCount,
    adjointCasimirIndex]

/-- Bundled finite conclusions of the internal generated response. -/
structure Properties : Prop where
  endpoint_origin : ∀ {b : ℝ}, 0 < b →
    criticalRadius = irEndpoint b / uvEndpoint b
  long_root_dimension : Module.finrank ℂ LongRootCarrier = 15
  long_root_casimir : longRootCasimirIndex = 16
  colour_adjoint_casimir : adjointCasimirIndex = 3
  drive_at_critical : longRootDrive criticalRadius = 0
  drive_unique : ∀ f, IsUnitSlopeAffineDrive f → f criticalRadius = 0 →
    f = longRootDrive
  restoring_balance : ∀ {L coupling}, criticalRadius < L → 0 < coupling →
    ∃! z : ℝ,
      0 < z ∧ completeResponse z = responseTarget L coupling ∧
      0 < generatedRadialGap z ∧
      (∀ j, generatedRadialGap z ≤ generatedScalarMassIndex j z) ∧
      generatedScalarMassIndex 0 z = generatedRadialGap z
  connection_count : connectionCoefficientCount = 120
  colour_normalization : colourNormalizationRatio = 3 / 8

theorem properties : Properties where
  endpoint_origin := fun hb => criticalRadius_eq_endpointRatio hb
  long_root_dimension := longRoot_finrank
  long_root_casimir := longRootCasimirIndex_eq
  colour_adjoint_casimir := adjointCasimirIndex_eq
  drive_at_critical := longRootDrive_critical
  drive_unique := fun _f hf hcritical => unitSlopeAffineDrive_unique hf hcritical
  restoring_balance := fun hL hc => existsUnique_response_with_scalarGap hL hc
  connection_count := connectionCoefficientCount_eq
  colour_normalization := colourNormalizationRatio_eq

end GeneratedFoundations.Physical.SourceInternalYangMillsResponse
