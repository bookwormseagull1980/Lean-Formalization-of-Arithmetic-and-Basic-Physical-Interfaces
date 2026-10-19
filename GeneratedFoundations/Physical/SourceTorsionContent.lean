module

public import GeneratedFoundations.Physical.SourceMatterCharge
public import GeneratedFoundations.Physical.SourceChargeLattice
public import Mathlib.Tactic

/-!
# Torsion content: the exact `1/50` modulus

This module supplies the Lean counterpart of the V5 content identity

`tau = (N_L - N_R) / (N_f * sum Y^2) = 1/50`.

The hypercharge weights are not assigned here: they are the eigenvalues of
`SourceMatterCharge.hyperchargeOperator`, which is built from the generated
relative and right-spin generators.  The multiplicities are the actual
`FullIndex` multiplicities: three colours for the coloured sector, one for
the scalar sector, and the two left-spin / one upper / one lower components
of the source chiral carrier.

`hyperchargeSqSum` is the content capacity `sum c * Y^2` over the six source
sectors.  `leftCount` and `rightChargedCount` are the left and charged-right
component counts.  `nWeyl` is the dimension of the actual charged quotient
`FullMatter / neutralLine`, proved equal to `15` by
`SourceMatterCharge.chargedQuotient_finrank`.

The resulting `tau` is a rational theorem, not a parameter or a numerical
fit.  The neutral right component has `Y = 0`, so it contributes to the
carrier dimension but not to `sum Y^2`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceTorsionContent

open SourceChargeLattice SourceMatterCharge SourceChiralCarrier

/-- Number of colour components in a colour sector. -/
def colourMultiplicity : ColourSector → ℕ
  | .coloured => 3
  | .scalar => 1

/-- Number of chiral components in a spin sector. -/
def spinMultiplicity : SpinSector → ℕ
  | .left => 2
  | .upper => 1
  | .lower => 1

/-- Multiplicity of one `(colour, spin)` sector in the sixteen-component carrier. -/
def sectorMultiplicity (p : Sector) : ℕ :=
  colourMultiplicity p.1 * spinMultiplicity p.2

/-- Hypercharge capacity `sum c * Y^2` on the six source sectors.  The
coefficients are the sector multiplicities: `6,3,3` for the coloured
doublet/up/down and `2,1,1` for the scalar doublet/neutral/charged singlet. -/
def hyperchargeSqSum : ℚ :=
  6 * (hypercharge (.coloured, .left)) ^ 2 +
  3 * (hypercharge (.coloured, .upper)) ^ 2 +
  3 * (hypercharge (.coloured, .lower)) ^ 2 +
  2 * (hypercharge (.scalar, .left)) ^ 2 +
  1 * (hypercharge (.scalar, .upper)) ^ 2 +
  1 * (hypercharge (.scalar, .lower)) ^ 2

/-- The exact hypercharge capacity is `10/3`. -/
theorem hyperchargeSqSum_eq : hyperchargeSqSum = 10 / 3 := by
  norm_num [hyperchargeSqSum, hypercharge, generatedCharge, chargeWeight,
    relativeWeight, twiceRightWeight, baseRelativeWeight]

/-- Left-handed component count: coloured doublet plus scalar doublet. -/
def leftCount : ℕ :=
  sectorMultiplicity (.coloured, .left) + sectorMultiplicity (.scalar, .left)

/-- Charged right-handed component count: three coloured singlets plus the
charged scalar singlet.  The neutral right component is excluded. -/
def rightChargedCount : ℕ :=
  sectorMultiplicity (.coloured, .upper) +
    sectorMultiplicity (.coloured, .lower) +
    sectorMultiplicity (.scalar, .lower)

/-- The left count is `8`. -/
theorem leftCount_eq : leftCount = 8 := by
  decide

/-- The charged-right count is `7`. -/
theorem rightChargedCount_eq : rightChargedCount = 7 := by
  decide

/-- The charged-quotient index is `N_L - N_R = 1`. -/
theorem leftRightIndex_eq_one :
    (leftCount : ℚ) - (rightChargedCount : ℚ) = 1 := by
  rw [leftCount_eq, rightChargedCount_eq]
  norm_num

/-- Number of gauge-active Weyl components: the dimension of the actual
charged quotient. -/
def nWeyl : ℕ := Module.finrank ℂ (FullMatter ⧸ neutralLine)

/-- The charged quotient has exactly `15` components. -/
theorem nWeyl_eq : nWeyl = 15 :=
  chargedQuotient_finrank

/-- The content-derived torsion modulus. -/
def torsionTau : ℚ :=
  ((leftCount : ℚ) - (rightChargedCount : ℚ)) /
    ((nWeyl : ℚ) * hyperchargeSqSum)

/-- The exact content theorem: `tau = 1/50`. -/
theorem torsionTau_eq : torsionTau = 1 / 50 := by
  rw [torsionTau, nWeyl_eq, hyperchargeSqSum_eq, leftCount_eq, rightChargedCount_eq]
  norm_num

/-- The zero-argument torsion-content conclusion. -/
structure Conclusions : Prop where
  hypercharge_capacity : hyperchargeSqSum = 10 / 3
  left_count : leftCount = 8
  right_charged_count : rightChargedCount = 7
  charged_weyl_count : nWeyl = 15
  left_right_index : (leftCount : ℚ) - (rightChargedCount : ℚ) = 1
  tau_eq : torsionTau = 1 / 50

theorem generated : Conclusions where
  hypercharge_capacity := hyperchargeSqSum_eq
  left_count := leftCount_eq
  right_charged_count := rightChargedCount_eq
  charged_weyl_count := nWeyl_eq
  left_right_index := leftRightIndex_eq_one
  tau_eq := torsionTau_eq

end GeneratedFoundations.Physical.SourceTorsionContent
