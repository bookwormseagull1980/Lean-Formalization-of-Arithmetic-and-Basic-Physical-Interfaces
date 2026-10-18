module

public import GeneratedFoundations.Analysis.SignedGaussianEnergy
public import Mathlib.Analysis.Fourier.ZMod

/-!
# Finite residue rows of the generated signed source

The finite complete signed source is pushed to `ZMod q` without changing its
root coefficients.  The standard additive character then gives its canonical
finite Fourier rows.  Fourier inversion is inherited from the finite cyclic
group and the zero row is exactly the original signed amplitude.
-/

@[expose] public section

noncomputable section

open scoped BigOperators FourierTransform

namespace GeneratedFoundations.Analysis.FiniteResidueFourier

open SignedGaussianEnergy

variable (q : ℕ) [NeZero q]

/-- Push the finite signed root source to its generated residue class. -/
def residueSource (alpha L : ℝ) (N : ℕ) (a : ZMod q) : ℂ :=
  ∑ n ∈ rootRange N,
    if (n : ZMod q) = a then (rootSignedMass alpha L n : ℂ) else 0

/-- The canonical additive-character rows of the residue source. -/
def residueFourier (alpha L : ℝ) (N : ℕ) : ZMod q → ℂ :=
  ZMod.dft (residueSource q alpha L N)

theorem residueFourier_apply (alpha L : ℝ) (N : ℕ) (k : ZMod q) :
    residueFourier q alpha L N k =
      ∑ a : ZMod q, ZMod.stdAddChar (-(a * k)) * residueSource q alpha L N a := by
  simp [residueFourier, ZMod.dft_apply, smul_eq_mul]

/-- Residue pushforward preserves the complete finite signed amplitude. -/
theorem sum_residueSource (alpha L : ℝ) (N : ℕ) :
    ∑ a : ZMod q, residueSource q alpha L N a =
      (rootSignedAmplitude alpha L N : ℂ) := by
  classical
  rw [rootSignedAmplitude]
  push_cast
  simp only [residueSource]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp

/-- The zero Fourier row is the original complete signed amplitude. -/
theorem residueFourier_zero (alpha L : ℝ) (N : ℕ) :
    residueFourier q alpha L N 0 =
      (rootSignedAmplitude alpha L N : ℂ) := by
  rw [residueFourier, ZMod.dft_apply_zero, sum_residueSource]

/-- Applying the finite Fourier transform twice returns the reflected residue
source with the exact factor `q`; no information has been discarded. -/
theorem residueFourier_inversion (alpha L : ℝ) (N : ℕ) :
    ZMod.dft (residueFourier q alpha L N) =
      fun a => (q : ℂ) • residueSource q alpha L N (-a) := by
  exact ZMod.dft_dft (residueSource q alpha L N)

/-- Finite residue pushforward and Fourier inversion are one lossless
interface of the complete signed source. -/
structure Conclusions : Prop where
  zero_row : ∀ (alpha L : ℝ) (N : ℕ),
    residueFourier q alpha L N 0 = (rootSignedAmplitude alpha L N : ℂ)
  inversion : ∀ (alpha L : ℝ) (N : ℕ),
    ZMod.dft (residueFourier q alpha L N) =
      fun a => (q : ℂ) • residueSource q alpha L N (-a)

theorem finiteResidueFourierConclusions : Conclusions q where
  zero_row := residueFourier_zero q
  inversion := residueFourier_inversion q

end GeneratedFoundations.Analysis.FiniteResidueFourier
