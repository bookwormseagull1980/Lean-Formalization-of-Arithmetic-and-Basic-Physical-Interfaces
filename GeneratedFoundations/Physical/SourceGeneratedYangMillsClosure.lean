module

public import GeneratedFoundations.Physical.SourceGeneratedYangMillsFlow

/-!
# Source-generated Yang--Mills closure

This module gathers the nonlinear local gauge action and the complete reduced
spectral dynamics selected by one minimal-change source.  The theorem is
uniform over every finite spectral cutoff: the cutoff labels a finite witness
of the same generated operator and does not enter its coercivity or decay
constant.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceGeneratedYangMillsClosure

open SourceConformalResponse SourceInternalYangMillsResponse
open SourceFourDimensionalYangMills
open SourceGeneratedYangMillsGap SourceGeneratedYangMillsAction
open SourceGeneratedYangMillsEquation SourceGeneratedYangMillsCoercivity
open SourceGeneratedYangMillsFlow

/-- The nonlinear local curvature and every reduced radial/coclosed mode are
parts of one generated Euclidean action.  The connection enters through its
full derivative-plus-commutator curvature, not through a linear replacement. -/
def completeGeneratedAction {N : ℕ} (L z : ℝ)
    (A : ColourConnectionJet) (x : SpectralConfiguration N) : ℝ :=
  (1 / 2 : ℝ) * euclideanCurvatureDensity A + spectralAction L z x

theorem completeGeneratedAction_nonneg {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (A : ColourConnectionJet)
    (x : SpectralConfiguration N) :
    0 ≤ completeGeneratedAction L z A x := by
  unfold completeGeneratedAction
  exact add_nonneg
    (mul_nonneg (by norm_num) (euclideanCurvatureDensity_nonneg A))
    (spectralAction_nonneg hL hz x)

/-- One cutoff-independent coercive estimate controls both the full nonlinear
curvature and all generated fluctuation shells. -/
theorem completeGeneratedAction_coercive {N : ℕ} (L z : ℝ)
    (A : ColourConnectionJet) (x : SpectralConfiguration N) :
    (1 / 2 : ℝ) * euclideanCurvatureDensity A +
        (1 / 2 : ℝ) * generatedYangMillsGapSq L z *
          SpectralConfiguration.normSq x ≤
      completeGeneratedAction L z A x := by
  have hspec := spectralAction_coercive L z x
  unfold completeGeneratedAction
  nlinarith

/-- The common action vanishes exactly at a flat generated connection with no
radial or coclosed fluctuation. -/
theorem completeGeneratedAction_eq_zero_iff {N : ℕ} {L z : ℝ}
    (hL : 0 < L) (hz : 0 < z) (A : ColourConnectionJet)
    (x : SpectralConfiguration N) :
    completeGeneratedAction L z A x = 0 ↔
      (∀ μ ν, curvature A μ ν = 0) ∧
        x = SpectralConfiguration.zero N := by
  constructor
  · intro hzero
    have hcurv : 0 ≤ euclideanCurvatureDensity A :=
      euclideanCurvatureDensity_nonneg A
    have hspec : 0 ≤ spectralAction L z x :=
      spectralAction_nonneg hL hz x
    have hcurvzero : euclideanCurvatureDensity A = 0 := by
      unfold completeGeneratedAction at hzero
      nlinarith
    have hspeczero : spectralAction L z x = 0 := by
      unfold completeGeneratedAction at hzero
      nlinarith
    exact ⟨(euclideanCurvatureDensity_eq_zero_iff A).mp hcurvzero,
      (spectralAction_eq_zero_iff hL hz x).mp hspeczero⟩
  · rintro ⟨hflat, rfl⟩
    have hcurvzero : euclideanCurvatureDensity A = 0 :=
      (euclideanCurvatureDensity_eq_zero_iff A).mpr hflat
    simp [completeGeneratedAction, hcurvzero, spectralAction,
      SpectralConfiguration.zero]

/-- With the nonlinear connection held fixed, the generated fluctuation flow
contracts the total action toward its curvature floor at the same uniform
spectral rate. -/
theorem completeGeneratedAction_flow_le {N : ℕ} {L z time : ℝ}
    (hL : 0 < L) (hz : 0 < z) (htime : 0 ≤ time)
    (A : ColourConnectionJet) (x : SpectralConfiguration N) :
    completeGeneratedAction L z A (spectralFlow L z time x) ≤
      (1 / 2 : ℝ) * euclideanCurvatureDensity A +
        Real.exp (-2 * time * generatedYangMillsGapSq L z) *
          spectralAction L z x := by
  unfold completeGeneratedAction
  exact add_le_add (le_refl _)
    (spectralAction_flow_le hL hz htime x)

/-- On the flat generated sector, the complete action itself decays
exponentially with a constant independent of the spectral cutoff. -/
theorem completeGeneratedAction_flat_flow_le {N : ℕ} {L z time : ℝ}
    (hL : 0 < L) (hz : 0 < z) (htime : 0 ≤ time)
    (A : ColourConnectionJet) (hflat : ∀ μ ν, curvature A μ ν = 0)
    (x : SpectralConfiguration N) :
    completeGeneratedAction L z A (spectralFlow L z time x) ≤
      Real.exp (-2 * time * generatedYangMillsGapSq L z) *
        completeGeneratedAction L z A x := by
  have hcurvzero : euclideanCurvatureDensity A = 0 :=
    (euclideanCurvatureDensity_eq_zero_iff A).mpr hflat
  simpa [completeGeneratedAction, hcurvzero] using
    spectralAction_flow_le hL hz htime x

/-- Complete generated-scope Yang--Mills theorem: one uniquely selected
condensed branch, the full nonlinear local gauge density, and a uniformly
coercive and exponentially stable reduced spectral dynamics. -/
structure Conclusions : Prop where
  unique_condensed_branch : ∀ L (hL : criticalRadius < L),
    0 < condensedAmplitude L hL ∧
    completeResponse (condensedAmplitude L hL) = generatedTarget L ∧
    0 < generatedYangMillsGapSq L (condensedAmplitude L hL)
  nonlinear_local_gauge_invariance : ∀ z radial q A,
    localActionDensity z radial (transformMatrixConnectionJet q A) =
      localActionDensity z radial A
  reduced_euler_unique : ∀ {N L z}, 0 < L → 0 < z →
    ∀ x : SpectralConfiguration N,
      equation L z x = SpectralConfiguration.zero N ↔
        x = SpectralConfiguration.zero N
  cutoff_independent_coercivity : ∀ {N} L z
      (x : SpectralConfiguration N),
    generatedYangMillsGapSq L z * SpectralConfiguration.normSq x ≤
      2 * spectralAction L z x
  exact_generated_semigroup : ∀ {N} L z s t
      (x : SpectralConfiguration N),
    spectralFlow L z s (spectralFlow L z t x) =
      spectralFlow L z (s + t) x
  uniform_exponential_stability : ∀ {N L z time},
    0 < L → 0 < z → 0 ≤ time → ∀ x : SpectralConfiguration N,
      spectralAction L z (spectralFlow L z time x) ≤
        Real.exp (-2 * time * generatedYangMillsGapSq L z) *
          spectralAction L z x
  complete_action_nonnegative : ∀ {N L z}, 0 < L → 0 < z →
    ∀ A (x : SpectralConfiguration N), 0 ≤ completeGeneratedAction L z A x
  complete_action_coercive : ∀ {N} L z A (x : SpectralConfiguration N),
    (1 / 2 : ℝ) * euclideanCurvatureDensity A +
        (1 / 2 : ℝ) * generatedYangMillsGapSq L z *
          SpectralConfiguration.normSq x ≤
      completeGeneratedAction L z A x
  complete_action_zero : ∀ {N L z}, 0 < L → 0 < z →
    ∀ A (x : SpectralConfiguration N),
      completeGeneratedAction L z A x = 0 ↔
        (∀ μ ν, curvature A μ ν = 0) ∧
          x = SpectralConfiguration.zero N
  flat_complete_action_decay : ∀ {N L z time},
    0 < L → 0 < z → 0 ≤ time →
    ∀ A, (∀ μ ν, curvature A μ ν = 0) →
      ∀ x : SpectralConfiguration N,
        completeGeneratedAction L z A (spectralFlow L z time x) ≤
          Real.exp (-2 * time * generatedYangMillsGapSq L z) *
            completeGeneratedAction L z A x

theorem conclusions : Conclusions where
  unique_condensed_branch := fun L hL => condensedAmplitude_spec L hL
  nonlinear_local_gauge_invariance := localActionDensity_gauge_invariant
  reduced_euler_unique := equation_eq_zero_iff
  cutoff_independent_coercivity := spectralAction_coercive
  exact_generated_semigroup := flow_add_time
  uniform_exponential_stability := spectralAction_flow_le
  complete_action_nonnegative := completeGeneratedAction_nonneg
  complete_action_coercive := completeGeneratedAction_coercive
  complete_action_zero := completeGeneratedAction_eq_zero_iff
  flat_complete_action_decay := completeGeneratedAction_flat_flow_le

end GeneratedFoundations.Physical.SourceGeneratedYangMillsClosure
