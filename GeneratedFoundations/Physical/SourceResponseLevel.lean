module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith
public meta import Lean.Elab.Tactic.Omega

/-!
# Integer selection of the finite response level

The finite Gaussian window is indexed by a positive natural level.  The
three-position condition gives two real inequalities on the endpoint root
`c R`:

  `sqrt(11/2) <= c R` and `c R < sqrt(15/2)`.

If `c` is strictly increasing, `c 4 < sqrt(11/2)` and
`sqrt(15/2) <= c 6`, then the only natural level satisfying the
three-position condition is `5`.  The analytic certificate
`c 4 < sqrt(11/2)`, `sqrt(15/2) <= c 6` is supplied by the companion
Gaussian TT response module; this file proves the integer-selection half,
with no numerical fitting and no observational input.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceResponseLevel

/-- The discrete level count of a finite Gaussian response window. -/
abbrev ResponseLevel := ℕ

/-- The three-position condition at a given endpoint root value. -/
def ThreePosition (c : ℝ) : Prop :=
  Real.sqrt (11 / 2 : ℝ) ≤ c ∧ c < Real.sqrt (15 / 2 : ℝ)

/-- The three-point certificate for the endpoint root as a function of the
discrete level.  The analytic inputs are the lower crossing
`c 4 < sqrt(11/2)` and the shell-support upper bound `R <= 16/pi`; the upper
edge is not a crossing of `c` because `c 6 < sqrt(15/2)` in the production
realization. -/
structure ThreePointCertificate (c : ResponseLevel → ℝ) : Prop where
  strictMono : StrictMono c
  four_lt : c 4 < Real.sqrt (11 / 2 : ℝ)
  upper_bound : ∀ {R : ResponseLevel}, ThreePosition (c R) →
    (R : ℝ) ≤ 16 / Real.pi

/-- The three-position condition at level `5`, from the two local bounds. -/
theorem threePosition_five {c : ResponseLevel → ℝ}
    (h5lo : Real.sqrt (11 / 2 : ℝ) ≤ c 5)
    (h5hi : c 5 < Real.sqrt (15 / 2 : ℝ)) :
    ThreePosition (c 5) :=
  ⟨h5lo, h5hi⟩

/-- The only natural level satisfying the three-position condition is `5`. -/
theorem threePosition_eq_five {c : ResponseLevel → ℝ}
    (cert : ThreePointCertificate c) {R : ResponseLevel}
    (hR : ThreePosition (c R)) : R = 5 := by
  have hnot4 : ¬ R ≤ 4 := by
    intro hRle
    have hcRle : c R ≤ c 4 := cert.strictMono.monotone hRle
    have hlt : c R < Real.sqrt (11 / 2 : ℝ) :=
      lt_of_le_of_lt hcRle cert.four_lt
    exact (not_le_of_gt hlt) hR.1
  have hUpper : (R : ℝ) ≤ 16 / Real.pi := cert.upper_bound hR
  have hpi : (8 / 3 : ℝ) < Real.pi := by
    linarith [Real.pi_gt_three]
  have h6 : (16 : ℝ) / Real.pi < 6 := by
    rw [div_lt_iff₀ Real.pi_pos]
    nlinarith
  have hRlt6Real : (R : ℝ) < 6 := lt_of_le_of_lt hUpper h6
  have h4lt : 4 < R := Nat.lt_of_not_le hnot4
  have hRlt6 : R < 6 := by
    exact_mod_cast hRlt6Real
  have h5le : 5 ≤ R := by
    simpa using Nat.succ_le_of_lt h4lt
  have hRlt6' : R < 5 + 1 := by
    simpa using hRlt6
  have hRle5 : R ≤ 5 := Nat.lt_succ_iff.mp hRlt6'
  exact Nat.le_antisymm hRle5 h5le

end GeneratedFoundations.Physical.SourceResponseLevel
