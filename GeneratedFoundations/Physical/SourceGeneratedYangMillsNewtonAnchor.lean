module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsAction
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Newton calibration of the generated Yang--Mills gap

The generated carrier, response action, condensed coordinate, Hessian and
dimensionless spectral bottom are constructed before this file and do not
depend on a dimensional constant.  This module performs one operation only:
it attaches physical mass units to that completed dimensionless result.

The sole calibration datum is a positive Newton constant `G_N`.  We use the
reduced-Planck convention

`M_P = 1 / sqrt (8 * pi * G_N)`.

For a point of the already generated condensed branch `L > sqrt pi`, the
endpoint scale relation is

`M_G / M_P = sqrt pi / L`.

The absolute Yang--Mills gap is then `M_G` times the square root of the
already generated dimensionless spectral bottom.  In particular, `G_N`
does not occur in any carrier, action, Hessian, condensate or positivity
statement; it cancels exactly from all gap-to-emergence-scale ratios.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsNewtonAnchor

open SourceInternalYangMillsResponse
open SourceGeneratedYangMillsGap
open SourceGeneratedYangMillsAction

/-- The one permitted dimensional datum.  Positivity is part of the datum
because a Newton constant calibrates a real positive mass unit. -/
structure NewtonAnchor where
  G_N : ℝ
  G_N_pos : 0 < G_N

namespace NewtonAnchor

theorem G_N_ne_zero (a : NewtonAnchor) : a.G_N ≠ 0 := a.G_N_pos.ne'

/-- Reduced Planck mass in the convention `M_P = (8 pi G_N)^(-1/2)`. -/
def reducedPlanckMass (a : NewtonAnchor) : ℝ :=
  1 / Real.sqrt (8 * Real.pi * a.G_N)

theorem reducedPlanckMass_pos (a : NewtonAnchor) :
    0 < reducedPlanckMass a := by
  have hG := a.G_N_pos
  unfold reducedPlanckMass
  exact one_div_pos.mpr (Real.sqrt_pos.2 (by positivity))

theorem reducedPlanckMass_ne_zero (a : NewtonAnchor) :
    reducedPlanckMass a ≠ 0 :=
  (reducedPlanckMass_pos a).ne'

/-- Exact square form of the reduced-Planck calibration. -/
theorem reducedPlanckMass_sq (a : NewtonAnchor) :
    reducedPlanckMass a ^ 2 = 1 / (8 * Real.pi * a.G_N) := by
  have hG := a.G_N_pos
  have h : 0 ≤ 8 * Real.pi * a.G_N := by positivity
  simp [reducedPlanckMass, Real.sq_sqrt h]

end NewtonAnchor

/-- A scale on the generated condensed branch.  Its inequality is not a
model input: it is precisely the domain on which the unique condensed
coordinate has already been proved to exist. -/
def CondensedScale := { L : ℝ // criticalRadius < L }

namespace CondensedScale

instance : Coe CondensedScale ℝ := ⟨Subtype.val⟩

theorem radius_pos (L : CondensedScale) : 0 < (L : ℝ) :=
  criticalRadius_pos.trans L.property

theorem radius_ne_zero (L : CondensedScale) : (L : ℝ) ≠ 0 :=
  (radius_pos L).ne'

end CondensedScale

/-- The unique internally selected response coordinate at a condensed
scale. -/
def generatedCondensate (L : CondensedScale) : ℝ :=
  condensedAmplitude (L : ℝ) L.property

theorem generatedCondensate_pos (L : CondensedScale) :
    0 < generatedCondensate L :=
  (condensedAmplitude_spec (L : ℝ) L.property).1

/-- The dimensionless Yang--Mills bottom before dimensional calibration. -/
def dimensionlessGapSq (L : CondensedScale) : ℝ :=
  generatedYangMillsGapSq (L : ℝ) (generatedCondensate L)

theorem dimensionlessGapSq_pos (L : CondensedScale) :
    0 < dimensionlessGapSq L :=
  (condensedAmplitude_spec (L : ℝ) L.property).2.2

/-- Endpoint emergence mass.  Since `criticalRadius = sqrt pi`, this is the
existing relation `M_G = M_P sqrt(pi) / L`. -/
def emergenceMass (a : NewtonAnchor) (L : CondensedScale) : ℝ :=
  a.reducedPlanckMass * (criticalRadius / (L : ℝ))

theorem emergenceMass_eq (a : NewtonAnchor) (L : CondensedScale) :
    emergenceMass a L =
      a.reducedPlanckMass * (Real.sqrt Real.pi / (L : ℝ)) := by
  rfl

theorem emergenceMass_pos (a : NewtonAnchor) (L : CondensedScale) :
    0 < emergenceMass a L := by
  exact mul_pos (a.reducedPlanckMass_pos)
    (div_pos criticalRadius_pos L.radius_pos)

theorem emergenceMass_ne_zero (a : NewtonAnchor) (L : CondensedScale) :
    emergenceMass a L ≠ 0 :=
  (emergenceMass_pos a L).ne'

/-- The generated endpoint ratio is unchanged by dimensional calibration. -/
theorem emergenceMass_div_reducedPlanckMass
    (a : NewtonAnchor) (L : CondensedScale) :
    emergenceMass a L / a.reducedPlanckMass =
      criticalRadius / (L : ℝ) := by
  unfold emergenceMass
  exact mul_div_cancel_left₀ _ a.reducedPlanckMass_ne_zero

/-- Absolute Yang--Mills gap mass after the one dimensional calibration. -/
def anchoredGapMass (a : NewtonAnchor) (L : CondensedScale) : ℝ :=
  emergenceMass a L * Real.sqrt (dimensionlessGapSq L)

/-- The corresponding absolute mass squared. -/
def anchoredGapSq (a : NewtonAnchor) (L : CondensedScale) : ℝ :=
  emergenceMass a L ^ 2 * dimensionlessGapSq L

theorem anchoredGapMass_pos (a : NewtonAnchor) (L : CondensedScale) :
    0 < anchoredGapMass a L := by
  exact mul_pos (emergenceMass_pos a L)
    (Real.sqrt_pos.2 (dimensionlessGapSq_pos L))

theorem anchoredGapSq_pos (a : NewtonAnchor) (L : CondensedScale) :
    0 < anchoredGapSq a L := by
  exact mul_pos (sq_pos_of_pos (emergenceMass_pos a L))
    (dimensionlessGapSq_pos L)

/-- Attaching units commutes exactly with passing from mass to mass squared. -/
theorem anchoredGapMass_sq (a : NewtonAnchor) (L : CondensedScale) :
    anchoredGapMass a L ^ 2 = anchoredGapSq a L := by
  rw [anchoredGapMass, anchoredGapSq, mul_pow,
    Real.sq_sqrt (dimensionlessGapSq_pos L).le]

/-- Exact transport of the dimensionless gap through the emergence scale. -/
theorem anchoredGapMass_div_emergenceMass
    (a : NewtonAnchor) (L : CondensedScale) :
    anchoredGapMass a L / emergenceMass a L =
      Real.sqrt (dimensionlessGapSq L) := by
  unfold anchoredGapMass
  exact mul_div_cancel_left₀ _ (emergenceMass_ne_zero a L)

/-- Exact squared transport of the generated spectral bottom. -/
theorem anchoredGapSq_div_emergenceMass_sq
    (a : NewtonAnchor) (L : CondensedScale) :
    anchoredGapSq a L / emergenceMass a L ^ 2 =
      dimensionlessGapSq L := by
  unfold anchoredGapSq
  exact mul_div_cancel_left₀ _ (pow_ne_zero 2 (emergenceMass_ne_zero a L))

/-- The complete Planck-normalized readout: endpoint ratio times the
dimensionless generated gap. -/
theorem anchoredGapMass_div_reducedPlanckMass
    (a : NewtonAnchor) (L : CondensedScale) :
    anchoredGapMass a L / a.reducedPlanckMass =
      (criticalRadius / (L : ℝ)) * Real.sqrt (dimensionlessGapSq L) := by
  rw [anchoredGapMass, emergenceMass]
  field_simp [a.reducedPlanckMass_ne_zero]

/-- Two choices of positive Newton calibration change the common mass unit,
but not the generated Yang--Mills gap ratio. -/
theorem gapRatio_anchor_independent
    (a₁ a₂ : NewtonAnchor) (L : CondensedScale) :
    anchoredGapMass a₁ L / emergenceMass a₁ L =
      anchoredGapMass a₂ L / emergenceMass a₂ L := by
  rw [anchoredGapMass_div_emergenceMass,
    anchoredGapMass_div_emergenceMass]

/-- Bundled statement of the dimensional calibration layer. -/
structure Properties : Prop where
  planck_positive : ∀ a : NewtonAnchor, 0 < a.reducedPlanckMass
  emergence_positive : ∀ a L, 0 < emergenceMass a L
  gap_positive : ∀ a L, 0 < anchoredGapMass a L
  gap_square : ∀ a L, anchoredGapMass a L ^ 2 = anchoredGapSq a L
  ratio_transport : ∀ a L,
    anchoredGapMass a L / emergenceMass a L =
      Real.sqrt (dimensionlessGapSq L)
  square_transport : ∀ a L,
    anchoredGapSq a L / emergenceMass a L ^ 2 = dimensionlessGapSq L

theorem properties : Properties where
  planck_positive := NewtonAnchor.reducedPlanckMass_pos
  emergence_positive := emergenceMass_pos
  gap_positive := anchoredGapMass_pos
  gap_square := anchoredGapMass_sq
  ratio_transport := anchoredGapMass_div_emergenceMass
  square_transport := anchoredGapSq_div_emergenceMass_sq

end GeneratedFoundations.Physical.SourceGeneratedYangMillsNewtonAnchor
