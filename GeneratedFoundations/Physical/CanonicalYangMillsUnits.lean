module

public import GeneratedFoundations.Physical.CanonicalYangMills
public import GeneratedFoundations.Physical.SourceGeneratedYangMillsNewtonAnchor

/-!
# Units for the canonical generated Yang--Mills response

The dimensionless radius, condensed amplitude and closed Hessian are already
fixed by the canonical source. The only argument of the dimensional readout
is the positive Newton calibration. No radius is selected at this interface.

The generated endpoint ratio has square one half. Consequently the emergence
mass squared is `1 / (16 pi G_N)`, and multiplying by the already attained
dimensionless Hessian bottom gives the absolute gap squared. The calibration
does not enter the operator, its domain, or the proof of its spectral bottom.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.CanonicalYangMillsUnits

open CanonicalYangMills
open SourceGeneratedYangMillsNewtonAnchor (NewtonAnchor CondensedScale)

/-- The already generated infrared scale, with its proved branch condition. -/
def sourceScale : CondensedScale :=
  ⟨internalRadius, criticalRadius_lt_internalRadius⟩

@[simp] theorem sourceScale_radius : (sourceScale : ℝ) = internalRadius := rfl

theorem sourceScale_gap :
    SourceGeneratedYangMillsNewtonAnchor.dimensionlessGapSq sourceScale = gapSq := rfl

/-- The source emergence mass in the permitted Newton units. -/
def emergenceMass (a : NewtonAnchor) : ℝ :=
  SourceGeneratedYangMillsNewtonAnchor.emergenceMass a sourceScale

/-- Absolute mass of the attained canonical Hessian bottom. -/
def gapMass (a : NewtonAnchor) : ℝ :=
  SourceGeneratedYangMillsNewtonAnchor.anchoredGapMass a sourceScale

theorem emergenceMass_pos (a : NewtonAnchor) : 0 < emergenceMass a :=
  SourceGeneratedYangMillsNewtonAnchor.emergenceMass_pos a sourceScale

theorem gapMass_pos (a : NewtonAnchor) : 0 < gapMass a :=
  SourceGeneratedYangMillsNewtonAnchor.anchoredGapMass_pos a sourceScale

/-- The endpoint ratio removes the radius argument from the absolute units. -/
theorem emergenceMass_sq (a : NewtonAnchor) :
    emergenceMass a ^ 2 = 1 / (16 * Real.pi * a.G_N) := by
  change (a.reducedPlanckMass *
    (SourceInternalYangMillsResponse.criticalRadius / internalRadius)) ^ 2 = _
  rw [mul_pow, div_pow, a.reducedPlanckMass_sq,
    SourceInternalYangMillsResponse.criticalRadius, internalRadius_eq,
    Real.sq_sqrt Real.pi_pos.le,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  field_simp [Real.pi_ne_zero, a.G_N_ne_zero]
  ring

/-- The squared mass is the generated spectral bottom in the fixed units. -/
theorem gapMass_sq (a : NewtonAnchor) :
    gapMass a ^ 2 = gapSq / (16 * Real.pi * a.G_N) := by
  have h : gapMass a ^ 2 = emergenceMass a ^ 2 * gapSq := by
    change SourceGeneratedYangMillsNewtonAnchor.anchoredGapMass a sourceScale ^ 2 = _
    rw [SourceGeneratedYangMillsNewtonAnchor.anchoredGapMass_sq]
    rfl
  rw [h, emergenceMass_sq]
  ring

/-- The dimensional calibration cancels from the generated gap ratio. -/
theorem gapMass_div_emergenceMass (a : NewtonAnchor) :
    gapMass a / emergenceMass a = Real.sqrt gapSq := by
  exact (SourceGeneratedYangMillsNewtonAnchor.anchoredGapMass_div_emergenceMass
    a sourceScale).trans (congrArg Real.sqrt sourceScale_gap)

theorem gapRatio_independent (a b : NewtonAnchor) :
    gapMass a / emergenceMass a = gapMass b / emergenceMass b := by
  rw [gapMass_div_emergenceMass, gapMass_div_emergenceMass]

/-- Positivity fixes the mass itself once the one calibration is given. -/
theorem gapMass_unique (a : NewtonAnchor) {m : ℝ} (hm : 0 < m)
    (hsq : m ^ 2 = gapSq / (16 * Real.pi * a.G_N)) : m = gapMass a := by
  have hmass := gapMass_pos a
  have heq := gapMass_sq a
  nlinarith

structure Conclusions : Prop where
  generated_scale : (sourceScale : ℝ) = internalRadius
  generated_gap : SourceGeneratedYangMillsNewtonAnchor.dimensionlessGapSq sourceScale = gapSq
  positive_mass : ∀ a : NewtonAnchor, 0 < gapMass a
  emergence_units : ∀ a : NewtonAnchor,
    emergenceMass a ^ 2 = 1 / (16 * Real.pi * a.G_N)
  gap_units : ∀ a : NewtonAnchor,
    gapMass a ^ 2 = gapSq / (16 * Real.pi * a.G_N)
  invariant_ratio : ∀ a : NewtonAnchor,
    gapMass a / emergenceMass a = Real.sqrt gapSq
  unique_mass : ∀ (a : NewtonAnchor) (m : ℝ), 0 < m →
    m ^ 2 = gapSq / (16 * Real.pi * a.G_N) → m = gapMass a

theorem generated : Conclusions where
  generated_scale := sourceScale_radius
  generated_gap := sourceScale_gap
  positive_mass := gapMass_pos
  emergence_units := emergenceMass_sq
  gap_units := gapMass_sq
  invariant_ratio := gapMass_div_emergenceMass
  unique_mass := fun a _ => gapMass_unique a

end GeneratedFoundations.Physical.CanonicalYangMillsUnits
