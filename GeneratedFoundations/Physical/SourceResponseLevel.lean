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

  `sqrt(11/2) < c R` and `c R <= sqrt(15/2)`.

The lower edge is excluded and the upper edge is retained because the
spectral projection uses a strict upper cutoff.

The shell support is a distinct condition: the last retained index is `49/4`
and the first excluded index is `16`. It gives `49/(4*pi) < R <= 16/pi`.
The three-position condition alone does not imply this support restriction.
With the lower crossing `c 4 < sqrt(11/2)`, monotonicity and the support
restriction select the unique natural level `5`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceResponseLevel

/-- The discrete level count of a finite Gaussian response window. -/
abbrev ResponseLevel := ℕ

/-- The three-position condition at a given endpoint root value. -/
def ThreePosition (c : ℝ) : Prop :=
  Real.sqrt (11 / 2 : ℝ) < c ∧ c ≤ Real.sqrt (15 / 2 : ℝ)

/-- The retained shell set is unchanged precisely on this bandwidth range. -/
def SameShellSupport (R : ResponseLevel) : Prop :=
  49 / (4 * Real.pi) < (R : ℝ) ∧ (R : ℝ) ≤ 16 / Real.pi

/-- Analytic lower-crossing data; the support condition is imposed separately
at the observation to which the selection theorem is applied. -/
structure ThreePointCertificate (c : ResponseLevel → ℝ) : Prop where
  strictMono : StrictMono c
  four_lt : c 4 < Real.sqrt (11 / 2 : ℝ)

theorem sameShellSupport_five : SameShellSupport 5 := by
  constructor
  · rw [div_lt_iff₀ (mul_pos (by norm_num) Real.pi_pos)]
    norm_num
    nlinarith [Real.pi_gt_three]
  · rw [le_div_iff₀ Real.pi_pos]
    norm_num
    nlinarith [Real.pi_lt_d2]

/-- The three-position condition at level `5`, from the two local bounds. -/
theorem threePosition_five {c : ResponseLevel → ℝ}
    (h5lo : Real.sqrt (11 / 2 : ℝ) < c 5)
    (h5hi : c 5 ≤ Real.sqrt (15 / 2 : ℝ)) :
    ThreePosition (c 5) :=
  ⟨h5lo, h5hi⟩

/-- The unique natural level satisfying both the three-position condition
and the retained shell support is `5`. -/
theorem threePosition_eq_five {c : ResponseLevel → ℝ}
    (cert : ThreePointCertificate c) {R : ResponseLevel}
    (hR : ThreePosition (c R)) (hsupport : SameShellSupport R) : R = 5 := by
  have hnot4 : ¬ R ≤ 4 := by
    intro hRle
    have hcRle : c R ≤ c 4 := cert.strictMono.monotone hRle
    have hlt : c R < Real.sqrt (11 / 2 : ℝ) :=
      lt_of_le_of_lt hcRle cert.four_lt
    exact lt_asymm hlt hR.1
  have hUpper : (R : ℝ) ≤ 16 / Real.pi := hsupport.2
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
