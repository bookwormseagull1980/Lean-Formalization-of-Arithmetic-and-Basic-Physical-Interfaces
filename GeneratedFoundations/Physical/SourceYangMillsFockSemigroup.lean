module

public import GeneratedFoundations.Physical.SourceHaarYangMillsFock
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic

/-!
# The generated Yang--Mills Fock heat semigroup

This module closes the local Fock layer of the generated Yang--Mills
response.  The one-particle Hessian is diagonalized in
`SourceHaarYangMillsFock`; here the diagonal heat weights

`exp(-t * totalEnergy n)`

are proved to form a one-parameter semigroup on the generated occupations.
The vacuum is fixed, every nonvacuum occupation is damped by at least the
generated gap, and the weights are strictly positive.  This is the heat
semigroup of the generated Fock core, not an interacting path-integral
measure.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceYangMillsFockSemigroup

open SourceHaarYangMillsFock SourceGeneratedYangMillsGap

/-- Diagonal heat weight of a generated occupation. -/
def heatWeight (L z t : ℝ) (n : Occupation) : ℝ :=
  Real.exp (-t * totalEnergy L z n)

theorem heatWeight_zero (L z : ℝ) (n : Occupation) :
    heatWeight L z 0 n = 1 := by
  simp [heatWeight]

theorem heatWeight_add (L z s t : ℝ) (n : Occupation) :
    heatWeight L z (s + t) n = heatWeight L z s n * heatWeight L z t n := by
  rw [heatWeight, heatWeight, heatWeight, ← Real.exp_add]
  congr 1
  ring

theorem heatWeight_pos (L z t : ℝ) (n : Occupation) :
    0 < heatWeight L z t n :=
  Real.exp_pos _

theorem heatWeight_vacuum (L z t : ℝ) :
    heatWeight L z t vacuum = 1 := by
  simp [heatWeight]

/-- A nonvacuum occupation is damped at least by the generated gap. -/
theorem heatWeight_nonvacuum_le {L z t : ℝ} (hL : 0 < L) (hz : 0 < z)
    (ht : 0 ≤ t) {n : Occupation} (hn : n ≠ vacuum) :
    heatWeight L z t n ≤ Real.exp (-t * generatedYangMillsGapSq L z) := by
  have hgap : generatedYangMillsGapSq L z ≤ totalEnergy L z n :=
    nonvacuum_gap hL hz hn
  have hmono : -t * totalEnergy L z n ≤ -t * generatedYangMillsGapSq L z :=
    mul_le_mul_of_nonpos_left hgap (neg_nonpos.mpr ht)
  exact Real.exp_le_exp.mpr hmono

/-- The local Fock-layer closure. -/
structure Conclusions : Prop where
  semigroup : ∀ (L z s t : ℝ) (n : Occupation),
    heatWeight L z (s + t) n = heatWeight L z s n * heatWeight L z t n
  vacuum_fixed : ∀ (L z t : ℝ), heatWeight L z t vacuum = 1
  positive : ∀ (L z t : ℝ) (n : Occupation), 0 < heatWeight L z t n
  gap_damping : ∀ {L z t : ℝ}, 0 < L → 0 < z → 0 ≤ t →
    ∀ {n : Occupation}, n ≠ vacuum →
      heatWeight L z t n ≤ Real.exp (-t * generatedYangMillsGapSq L z)

theorem generated : Conclusions where
  semigroup := heatWeight_add
  vacuum_fixed := heatWeight_vacuum
  positive := heatWeight_pos
  gap_damping := fun hL hz ht _n hn => heatWeight_nonvacuum_le hL hz ht hn

end GeneratedFoundations.Physical.SourceYangMillsFockSemigroup
