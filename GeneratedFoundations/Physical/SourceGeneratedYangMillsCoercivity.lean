module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsEquation

/-!
# Cutoff-independent coercivity of the generated Yang--Mills action

The radial block and every coclosed shell are bounded below by the same
source-generated spectral bottom.  Summing those pointwise bounds proves a
coercive estimate whose constant is independent of the finite spectral
cutoff.  Thus the generated action has no flat direction after gauge reduction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsCoercivity

open SourceGeneratedYangMillsGap SourceGeneratedYangMillsAction
open SourceGeneratedYangMillsEquation

/-- Every finite generated spectral action controls the full reduced norm by
the same spectral bottom, independently of the shell cutoff. -/
theorem spectralAction_coercive {N : ℕ} (L z : ℝ)
    (x : SpectralConfiguration N) :
    generatedYangMillsGapSq L z * SpectralConfiguration.normSq x ≤
      2 * spectralAction L z x := by
  have hrad :
      generatedYangMillsGapSq L z * x.radial ^ 2 ≤
        normalizedRadialMassSq z * x.radial ^ 2 :=
    mul_le_mul_of_nonneg_right
      (generatedYangMillsGapSq_le_radial L z) (sq_nonneg x.radial)
  have hmode : ∀ i : Fin N,
      generatedYangMillsGapSq L z * x.coclosed i ^ 2 ≤
        coclosedMassIndex L z (i.1 + 1) * x.coclosed i ^ 2 := by
    intro i
    exact mul_le_mul_of_nonneg_right
      (generatedYangMillsGapSq_le_coclosed (Nat.succ_le_succ (Nat.zero_le i.1)))
      (sq_nonneg (x.coclosed i))
  have hsum :
      ∑ i, generatedYangMillsGapSq L z * x.coclosed i ^ 2 ≤
        ∑ i, coclosedMassIndex L z (i.1 + 1) * x.coclosed i ^ 2 :=
    Finset.sum_le_sum fun i _ => hmode i
  unfold SpectralConfiguration.normSq spectralAction
  rw [mul_add, Finset.mul_sum]
  nlinarith

/-- On the generated condensed branch, the action vanishes exactly at the
zero reduced configuration. -/
theorem spectralAction_eq_zero_iff {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (x : SpectralConfiguration N) :
    spectralAction L z x = 0 ↔ x = SpectralConfiguration.zero N := by
  constructor
  · intro hzero
    have hcoercive := spectralAction_coercive L z x
    rw [hzero, mul_zero] at hcoercive
    have hgap := generatedYangMillsGapSq_pos hL hz
    have hnorm := SpectralConfiguration.normSq_nonneg x
    have : SpectralConfiguration.normSq x = 0 := by nlinarith
    exact (SpectralConfiguration.normSq_eq_zero_iff x).mp this
  · rintro rfl
    simp [spectralAction, SpectralConfiguration.zero]

/-- The same cutoff-independent lower bound for the Euler quadratic form. -/
theorem firstVariation_coercive {N : ℕ} (L z : ℝ)
    (x : SpectralConfiguration N) :
    generatedYangMillsGapSq L z * SpectralConfiguration.normSq x ≤
      firstVariation L z x x := by
  rw [firstVariation_self_eq_two_action]
  exact spectralAction_coercive L z x

/-- Bundled coercivity interface. -/
structure Properties : Prop where
  uniform_coercivity : ∀ {N} L z (x : SpectralConfiguration N),
    generatedYangMillsGapSq L z * SpectralConfiguration.normSq x ≤
      2 * spectralAction L z x
  zero_characterization : ∀ {N L z}, 0 < L → 0 < z →
    ∀ x : SpectralConfiguration N,
      spectralAction L z x = 0 ↔ x = SpectralConfiguration.zero N
  euler_coercivity : ∀ {N} L z (x : SpectralConfiguration N),
    generatedYangMillsGapSq L z * SpectralConfiguration.normSq x ≤
      firstVariation L z x x

theorem properties : Properties where
  uniform_coercivity := spectralAction_coercive
  zero_characterization := spectralAction_eq_zero_iff
  euler_coercivity := firstVariation_coercive

end GeneratedFoundations.Physical.SourceGeneratedYangMillsCoercivity
