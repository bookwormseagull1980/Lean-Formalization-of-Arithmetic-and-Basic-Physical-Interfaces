module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Order.Monotone.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Finite Gaussian response domain (mathematical scaffold)

This file fixes the mathematical object that the earlier physical branch was
missing: a **finite** response domain with an explicit Gaussian weight.

`ResponseDomain` is indexed by a positive natural `level`.  The level is the
discrete number of Gaussian ladder levels retained by the window; it is not a
continuous radius.  The response domain itself is the corresponding finite
window `q^2 < level * cutoff^2`.

The TT spectral sum and the endpoint-root certificate are deliberately not
defined here: they require the Gaussian-weighted frequency integral over the
generated spectrum and belong to the companion `SourceTTResponse` module.
This file only fixes the finite window and the weight, so that the later
selection theorem has a precise object to speak about.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceGaussianResponseDomain

/-- A finite Gaussian response domain: a positive discrete level count and a
positive frequency cutoff. -/
structure ResponseDomain where
  level : ℕ
  level_pos : 0 < level
  cutoff : ℝ
  cutoff_pos : 0 < cutoff

/-- The Gaussian weight of the finite response window. -/
def gaussianWeight (cutoff q : ℝ) : ℝ :=
  Real.exp (-(q ^ 2) / cutoff ^ 2)

/-- The finite response window `q^2 < level * cutoff^2`. -/
def window (D : ResponseDomain) : Set ℝ :=
  {q : ℝ | q ^ 2 < (D.level : ℝ) * D.cutoff ^ 2}

theorem zero_mem_window (D : ResponseDomain) : (0 : ℝ) ∈ window D := by
  have hlevel : (0 : ℝ) < (D.level : ℝ) := by
    exact_mod_cast D.level_pos
  have hcut : (0 : ℝ) < D.cutoff ^ 2 := sq_pos_of_pos D.cutoff_pos
  simp only [window, Set.mem_ofPred_eq, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  exact mul_pos hlevel hcut

end GeneratedFoundations.Physical.SourceGaussianResponseDomain
