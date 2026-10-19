module

public import GeneratedFoundations.Analysis.MaximumPrimeFactorStage
public import GeneratedFoundations.Analysis.CenterRelativePotential

/-!
# Full relative-potential ledger of a maximum-prime-factor stage

This module joins the actual maximum-prime-factor birth set to the full
binary relative potential.  The old source and the genuine birth source are
combined before the observation is evaluated.  Hence the single
Jensen--Shannon loss below already contains the paired interior, the natural
cutoff boundary, and all their cross terms.

The result is an exact finite-stage identity.  Its scale integral becomes an
all-scale theorem only after a uniform cumulative lower bound for the same
Jensen--Shannon losses has been proved.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.MaximumPrimeFactorRelativeStage

open GeneratedFoundations.Arithmetic.JointOccupationScale
open GeneratedFoundations.Analysis.CenterEndpointPotential
open GeneratedFoundations.Analysis.CenterRelativePotential
open GeneratedFoundations.Analysis.MaximumPrimeFactorStage
open GeneratedFoundations.Analysis.CanonicalMobiusReadout

/-- The actual prime birth obeys one exact full-relative-potential ledger.
No endpoint term is omitted: the endpoint is part of the complete old pair. -/
theorem generated_stage_relative_ledger (w : ℕ → ℝ) {p N : ℕ}
    (hp : p.Prime) :
    relativePotential (sectorPairOn w (stageAfter p N)) -
        relativePotential (sectorPairOn w (stageBefore p N)) =
      relativePotential (returnPair w p N) -
        joinJSDissipation
          (sectorPairOn w (stageBefore p N)) (birthPair w p N) := by
  have hafter :
      sectorPairOn w (stageAfter p N) =
        CentrePair.add (sectorPairOn w (stageBefore p N))
          (birthPair w p N) := by
    rw [stageAfter, sectorPairOn_union w
      (disjoint_stageBefore_stageBirth hp)]
    rw [sectorPairOn_stageBirth_eq_birthPair w hp]
  have hchain := relativePotential_join_chain
    (sectorPairOn w (stageBefore p N)) (birthPair w p N)
  have hswap :
      relativePotential (birthPair w p N) =
        relativePotential (returnPair w p N) := by
    simp [birthPair]
  rw [hswap] at hchain
  rw [hafter]
  linarith

/-- The same identity with the generated Gaussian scale return made explicit. -/
theorem gaussian_generated_stage_relative_ledger (L : PositiveScale)
    {p N : ℕ} (hp : p.Prime) :
    relativePotential
          (sectorPairOn (gaussianWindowMass L.1) (stageAfter p N)) -
        relativePotential
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N)) =
      relativePotential
          (pairedPair (gaussianWindowMass (L.1 / (p : ℝ))) p N) -
        joinJSDissipation
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N))
          (birthPair (gaussianWindowMass L.1) p N) := by
  have h := generated_stage_relative_ledger (gaussianWindowMass L.1) (N := N) hp
  rw [gaussian_returnPair_eq_scale_transport L hp] at h
  exact h

/-- On a nonnegative source the full dissipation term in the actual stage is
nonnegative, including the empty-boundary cases. -/
theorem generated_stage_relative_dissipation_nonnegative
    (w : ℕ → ℝ) {p N : ℕ} (hw : ∀ n, 0 ≤ w n) :
    0 ≤ joinJSDissipation
      (sectorPairOn w (stageBefore p N)) (birthPair w p N) := by
  have hold := sectorPairOn_nonnegative w (stageBefore p N)
    (fun n _hn => hw n)
  have hreturn := sectorPairOn_nonnegative (fun n => w (p * n))
    (stagePairedBase p N) (fun n _hn => hw (p * n))
  have hbirth :
      0 ≤ (birthPair w p N).positive ∧ 0 ≤ (birthPair w p N).negative := by
    constructor
    · simpa [birthPair, CentrePair.swap, returnPair] using hreturn.2
    · simpa [birthPair, CentrePair.swap, returnPair] using hreturn.1
  exact joinJSDissipation_nonneg
    (sectorPairOn w (stageBefore p N)) (birthPair w p N)
    hold.1 hold.2 hbirth.1 hbirth.2

/-- Bundled exact output of the full relative-potential stage. -/
structure Conclusions : Prop where
  actual_stage : ∀ (w : ℕ → ℝ) {p N}, p.Prime →
    relativePotential (sectorPairOn w (stageAfter p N)) -
        relativePotential (sectorPairOn w (stageBefore p N)) =
      relativePotential (returnPair w p N) -
        joinJSDissipation
          (sectorPairOn w (stageBefore p N)) (birthPair w p N)
  gaussian_scale_stage : ∀ (L : PositiveScale) {p N}, p.Prime →
    relativePotential
          (sectorPairOn (gaussianWindowMass L.1) (stageAfter p N)) -
        relativePotential
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N)) =
      relativePotential
          (pairedPair (gaussianWindowMass (L.1 / (p : ℝ))) p N) -
        joinJSDissipation
          (sectorPairOn (gaussianWindowMass L.1) (stageBefore p N))
          (birthPair (gaussianWindowMass L.1) p N)
  dissipation_nonnegative : ∀ (w : ℕ → ℝ) {p N},
    (∀ n, 0 ≤ w n) →
      0 ≤ joinJSDissipation
        (sectorPairOn w (stageBefore p N)) (birthPair w p N)

theorem conclusions : Conclusions where
  actual_stage := generated_stage_relative_ledger
  gaussian_scale_stage := gaussian_generated_stage_relative_ledger
  dissipation_nonnegative := generated_stage_relative_dissipation_nonnegative

end GeneratedFoundations.Analysis.MaximumPrimeFactorRelativeStage
