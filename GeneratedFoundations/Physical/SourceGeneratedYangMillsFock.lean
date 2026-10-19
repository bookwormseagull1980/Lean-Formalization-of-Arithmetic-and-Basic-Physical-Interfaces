module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsPhysicalHessian
public import Mathlib.Data.Finsupp.Order
public import Mathlib.Tactic.Linarith

/-!
# Algebraic Fock completion of the generated Yang--Mills response

Finite bosonic occupations are formed from the same complete physical modes
that define the self-adjoint response Hessian.  Their additive energy has a
unique vacuum, every non-vacuum occupation lies above the generated spectral
bottom, and the minimizing one-particle state attains that bottom exactly.
-/

@[expose] public section

noncomputable section

open GeneratedFoundations.Physical.SourceGeneratedYangMillsGap
open GeneratedFoundations.Physical.SourceGeneratedYangMillsPhysicalHessian

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsFock

/-- Finite bosonic occupations of the complete generated response modes. -/
abbrev BosonicOccupation := PhysicalMode →₀ ℕ

/-- Empty occupation. -/
def vacuum : BosonicOccupation := 0

/-- Total occupation number. -/
def particleNumber (occupation : BosonicOccupation) : ℕ :=
  occupation.sum fun _ multiplicity => multiplicity

/-- Additive energy of a finite generated occupation. -/
def totalEnergy (L z : ℝ) (occupation : BosonicOccupation) : ℝ :=
  occupation.sum fun mode multiplicity =>
    (multiplicity : ℝ) * physicalEigenvalue L z mode

@[simp] theorem particleNumber_vacuum : particleNumber vacuum = 0 := by
  simp [particleNumber, vacuum]

@[simp] theorem totalEnergy_vacuum (L z : ℝ) :
    totalEnergy L z vacuum = 0 := by
  simp [totalEnergy, vacuum]

/-- A one-particle occupation of a complete generated mode. -/
def oneParticle (mode : PhysicalMode) : BosonicOccupation :=
  Finsupp.single mode 1

@[simp] theorem particleNumber_oneParticle (mode : PhysicalMode) :
    particleNumber (oneParticle mode) = 1 := by
  classical
  simp [particleNumber, oneParticle]

@[simp] theorem totalEnergy_oneParticle (L z : ℝ) (mode : PhysicalMode) :
    totalEnergy L z (oneParticle mode) = physicalEigenvalue L z mode := by
  classical
  simp [totalEnergy, oneParticle]

theorem oneParticle_ne_vacuum (mode : PhysicalMode) :
    oneParticle mode ≠ vacuum := by
  classical
  simp [oneParticle, vacuum]

theorem totalEnergy_nonneg {L z : ℝ} (hL : 0 < L) (hz : 0 < z)
    (occupation : BosonicOccupation) : 0 ≤ totalEnergy L z occupation := by
  unfold totalEnergy
  exact Finsupp.sum_nonneg' fun mode =>
    mul_nonneg (Nat.cast_nonneg _)
      (physicalEigenvalue_pos hL hz mode).le

/-- Every non-vacuum occupation has at least one occupied generated mode and
therefore lies above the one-response bottom. -/
theorem gap_le_totalEnergy_of_ne_vacuum {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) {occupation : BosonicOccupation}
    (hoccupation : occupation ≠ vacuum) :
    generatedYangMillsGapSq L z ≤ totalEnergy L z occupation := by
  classical
  have hoccupation0 : occupation ≠ 0 := by simpa [vacuum] using hoccupation
  obtain ⟨mode, hmode⟩ := Finsupp.support_nonempty_iff.mpr hoccupation0
  have hmultiplicity : occupation mode ≠ 0 := Finsupp.mem_support_iff.mp hmode
  have hone : (1 : ℝ) ≤ (occupation mode : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hmultiplicity)
  have hsingle :
      (occupation mode : ℝ) * physicalEigenvalue L z mode ≤
        totalEnergy L z occupation := by
    unfold totalEnergy
    simpa using
      (Finsupp.single_le_sum occupation
        (fun selected multiplicity =>
          mul_nonneg (Nat.cast_nonneg multiplicity)
            (physicalEigenvalue_pos hL hz selected).le)
        mode)
  calc
    generatedYangMillsGapSq L z =
        (1 : ℝ) * generatedYangMillsGapSq L z := by ring
    _ ≤ (occupation mode : ℝ) * generatedYangMillsGapSq L z :=
      mul_le_mul_of_nonneg_right hone (generatedYangMillsGapSq_pos hL hz).le
    _ ≤ (occupation mode : ℝ) * physicalEigenvalue L z mode :=
      mul_le_mul_of_nonneg_left (gap_le_physicalEigenvalue L z mode)
        (Nat.cast_nonneg _)
    _ ≤ totalEnergy L z occupation := hsingle

theorem totalEnergy_eq_zero_iff_vacuum {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (occupation : BosonicOccupation) :
    totalEnergy L z occupation = 0 ↔ occupation = vacuum := by
  constructor
  · intro henergy
    by_contra hoccupation
    have hgap := gap_le_totalEnergy_of_ne_vacuum hL hz hoccupation
    linarith [generatedYangMillsGapSq_pos hL hz]
  · rintro rfl
    exact totalEnergy_vacuum L z

/-- The exact minimizing one-particle occupation. -/
def groundOccupation (L z : ℝ) : BosonicOccupation :=
  oneParticle (minimizingMode L z)

theorem groundOccupation_ne_vacuum (L z : ℝ) :
    groundOccupation L z ≠ vacuum :=
  oneParticle_ne_vacuum (minimizingMode L z)

@[simp] theorem totalEnergy_groundOccupation (L z : ℝ) :
    totalEnergy L z (groundOccupation L z) =
      generatedYangMillsGapSq L z := by
  simp [groundOccupation, physicalEigenvalue_minimizingMode]

/-- Exact Fock-space mass-gap statement on finite occupations. -/
structure Conclusions : Prop where
  vacuum_zero : ∀ L z, totalEnergy L z vacuum = 0
  vacuum_unique : ∀ {L z}, 0 < L → 0 < z → ∀ occupation,
    totalEnergy L z occupation = 0 ↔ occupation = vacuum
  nonvacuum_gap : ∀ {L z}, 0 < L → 0 < z →
    ∀ {occupation}, occupation ≠ vacuum →
      generatedYangMillsGapSq L z ≤ totalEnergy L z occupation
  gap_attained : ∀ L z,
    groundOccupation L z ≠ vacuum ∧
    totalEnergy L z (groundOccupation L z) = generatedYangMillsGapSq L z

theorem conclusions : Conclusions where
  vacuum_zero := totalEnergy_vacuum
  vacuum_unique := totalEnergy_eq_zero_iff_vacuum
  nonvacuum_gap := gap_le_totalEnergy_of_ne_vacuum
  gap_attained := fun L z =>
    ⟨groundOccupation_ne_vacuum L z, totalEnergy_groundOccupation L z⟩

end GeneratedFoundations.Physical.SourceGeneratedYangMillsFock
