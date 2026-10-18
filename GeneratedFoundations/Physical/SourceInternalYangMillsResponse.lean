module

public import GeneratedFoundations.Correlation.Endpoints
public import GeneratedFoundations.Geometry.SourceLeftRightRepresentations
public import GeneratedFoundations.Physical.SourceColourAdjointCasimir
public import GeneratedFoundations.Physical.SourceConformalResponse
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Generated internal Yang--Mills response

The critical radius is the already constructed infrared/ultraviolet endpoint
ratio.  The long-root carrier is the actual `(4,2)` source representation, so
its dimension and Casimir are computed by the uniform left--right theorems.
The drive is then the unique unit-slope affine function of that eigenvalue
which vanishes at the generated critical radius.  No second fifteen-dimensional
space, critical scale or response target is supplied as input.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Correlation.Endpoints
open GeneratedFoundations.Geometry.SourceLeftRightRepresentations
open GeneratedFoundations.Physical.SourceColourAdjointCasimir
open GeneratedFoundations.Physical.SourceConformalResponse

namespace GeneratedFoundations.Physical.SourceInternalYangMillsResponse

/-- The source long-root representation has bidegree `(4,2)`. -/
abbrev LongRootCarrier := Carrier 4 2

theorem longRoot_finrank : Module.finrank ℂ LongRootCarrier = 15 := by
  simpa [LongRootCarrier] using carrier_finrank 4 2

/-- Its dimensionless Casimir is computed from the source representation. -/
def longRootCasimirIndex : ℝ := casimirIndex 4 2

@[simp] theorem longRootCasimirIndex_eq : longRootCasimirIndex = 16 := by
  norm_num [longRootCasimirIndex, casimirIndex]

/-- The generated endpoint ratio, used as the internal critical radius. -/
def criticalRadius : ℝ := Real.sqrt Real.pi

theorem criticalRadius_pos : 0 < criticalRadius := by
  exact Real.sqrt_pos.2 Real.pi_pos

theorem criticalRadius_ne_zero : criticalRadius ≠ 0 := criticalRadius_pos.ne'

/-- The critical radius is not an extra scale: it is the endpoint ratio of
every positive-width Gaussian source window. -/
theorem criticalRadius_eq_endpointRatio {b : ℝ} (hb : 0 < b) :
    criticalRadius = irEndpoint b / uvEndpoint b := by
  exact (endpoint_ratio hb).symm

/-- Radius-scaled eigenvalue of the actual source long-root carrier. -/
def longRootEigenvalue (L : ℝ) : ℝ := longRootCasimirIndex / L ^ 2

theorem longRootEigenvalue_eq (L : ℝ) :
    longRootEigenvalue L = 16 / L ^ 2 := by
  simp [longRootEigenvalue]

/-- The generated affine drive, normalized by its own long-root eigenvalue. -/
def longRootDrive (L : ℝ) : ℝ :=
  longRootEigenvalue L - longRootEigenvalue criticalRadius

theorem longRootDrive_eq (L : ℝ) :
    longRootDrive L = 16 * (L ^ (-2 : ℤ) - criticalRadius ^ (-2 : ℤ)) := by
  rw [longRootDrive, longRootEigenvalue_eq, longRootEigenvalue_eq]
  simp only [zpow_neg, zpow_ofNat]
  ring

@[simp] theorem longRootDrive_critical : longRootDrive criticalRadius = 0 := by
  simp [longRootDrive]

/-- Comparison class used for the affine-drive uniqueness statement. -/
def IsUnitSlopeAffineDrive (f : ℝ → ℝ) : Prop :=
  ∃ c : ℝ, ∀ L : ℝ, f L = longRootEigenvalue L + c

theorem longRootDrive_isUnitSlopeAffine :
    IsUnitSlopeAffineDrive longRootDrive := by
  refine ⟨-longRootEigenvalue criticalRadius, ?_⟩
  intro L
  simp only [longRootDrive]
  ring

/-- Within the generated affine comparison class, vanishing at the generated
critical radius uniquely fixes the drive. -/
theorem unitSlopeAffineDrive_unique {f : ℝ → ℝ}
    (hf : IsUnitSlopeAffineDrive f) (hcritical : f criticalRadius = 0) :
    f = longRootDrive := by
  obtain ⟨c, hc⟩ := hf
  funext L
  have hc0 := hc criticalRadius
  rw [hcritical] at hc0
  rw [hc L, longRootDrive]
  linarith

theorem longRootDrive_neg {L : ℝ} (hL : criticalRadius < L) :
    longRootDrive L < 0 := by
  have hLc : 0 < L := criticalRadius_pos.trans hL
  rw [longRootDrive, longRootEigenvalue_eq, longRootEigenvalue_eq]
  have hs : criticalRadius ^ 2 < L ^ 2 := by
    nlinarith [criticalRadius_pos, hLc]
  have hi : 1 / L ^ 2 < 1 / criticalRadius ^ 2 := by
    exact one_div_lt_one_div_of_lt (sq_pos_of_pos criticalRadius_pos) hs
  have hscaled : 16 / L ^ 2 < 16 / criticalRadius ^ 2 := by
    simpa only [div_eq_mul_inv, one_mul] using
      mul_lt_mul_of_pos_left hi (by norm_num : (0 : ℝ) < 16)
  exact sub_neg.mpr hscaled

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
