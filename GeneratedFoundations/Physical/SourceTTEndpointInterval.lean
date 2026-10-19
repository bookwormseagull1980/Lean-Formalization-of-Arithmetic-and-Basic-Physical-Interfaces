module

public import GeneratedFoundations.Physical.SourceTensorResponseEndpoint
public import GeneratedFoundations.Physical.SourceTTGaussianCoefficient
public import Mathlib.Tactic

/-!
# Interval certificate for the TT endpoint root

This module formalizes the **root/interval layer** of the TT endpoint.  It
takes an interval `[A_lo, A_hi]` for the positive TT spectral coefficient
`A` (supplied by the V5 finite-response calculation) and proves that the
unique positive root of

`A / c - 4/27 = 0`

lies in `[27*A_lo/4, 27*A_hi/4]`.  The coefficient interval itself must be
supplied by the RP³ TT spectral sum and Gaussian frequency integral; this
module does not manufacture it from an external number.  The V5 certificate
`tt_branch_reduction` proves externally that the full active V5 spectrum
reduces exactly to this eight-branch coefficient on the endpoint bracket.

The algebraic maximum `4/27` and the uniqueness of the positive root are
already proved in `SourceTensorResponseEndpoint`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceTTEndpointInterval

open SourceTensorResponseEndpoint

/-- An interval enclosing the positive TT spectral coefficient `A`. -/
structure CoefficientBounds where
  A_lo : ℝ
  A_hi : ℝ
  A_lo_pos : 0 < A_lo
  A_mem : A_lo ≤ SourceTTGaussianCoefficient.coefficient ∧
    SourceTTGaussianCoefficient.coefficient ≤ A_hi

/-- The enclosed coefficient is fixed by the retained Gaussian spectral sum. -/
def CoefficientBounds.A (_b : CoefficientBounds) : ℝ :=
  SourceTTGaussianCoefficient.coefficient

/-- The coefficient is positive. -/
theorem A_pos (b : CoefficientBounds) : 0 < b.A :=
  lt_of_lt_of_le b.A_lo_pos b.A_mem.1

/-- The lower root bound. -/
def rootLower (b : CoefficientBounds) : ℝ := 27 * b.A_lo / 4

/-- The upper root bound. -/
def rootUpper (b : CoefficientBounds) : ℝ := 27 * b.A_hi / 4

/-- The unique positive root lies in the coefficient-induced interval. -/
theorem root_mem_interval (b : CoefficientBounds) {c : ℝ}
    (hc_pos : 0 < c) (hc : endpointResidual b.A c = 0) :
    rootLower b ≤ c ∧ c ≤ rootUpper b := by
  have hroot : c = endpointRoot b.A :=
    (endpointResidual_eq_zero_iff (A_pos b) hc_pos).mp hc
  subst hroot
  constructor
  · dsimp [rootLower, endpointRoot, CoefficientBounds.A]
    nlinarith [b.A_mem.1]
  · dsimp [rootUpper, endpointRoot, CoefficientBounds.A]
    nlinarith [b.A_mem.2]

/-- The interval/root layer of the TT endpoint closure. -/
structure Conclusions (b : CoefficientBounds) : Prop where
  coefficient_positive : 0 < b.A
  root_lower : rootLower b ≤ endpointRoot b.A
  root_upper : endpointRoot b.A ≤ rootUpper b

theorem generated (b : CoefficientBounds) : Conclusions b where
  coefficient_positive := A_pos b
  root_lower := by
    dsimp [rootLower, endpointRoot, CoefficientBounds.A]
    nlinarith [b.A_mem.1]
  root_upper := by
    dsimp [rootUpper, endpointRoot, CoefficientBounds.A]
    nlinarith [b.A_mem.2]

end GeneratedFoundations.Physical.SourceTTEndpointInterval
