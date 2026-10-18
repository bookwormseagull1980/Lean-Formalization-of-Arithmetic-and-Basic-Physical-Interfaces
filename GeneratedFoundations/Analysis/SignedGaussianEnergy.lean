module

public import GeneratedFoundations.Analysis.GeneratedMobiusObservation

/-!
# Finite complete signed Gaussian energy

This module forms the finite signed amplitude from the persistent complete
history source.  Summation over histories is performed before the energy is
expanded.  The resulting identity retains every ordered off-diagonal term;
no absolute-value split or independence replacement is made.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.SignedGaussianEnergy

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedMobiusObservation

/-- Root coefficient of the complete signed Gaussian source. -/
def rootSignedMass (alpha L : ℝ) (n : ℕ) : ℝ :=
  (generatedMoebius n : ℝ) * gaussianRootMass alpha L n

/-- Finite root range with the zero value excluded. -/
def rootRange (N : ℕ) : Finset ℕ := Finset.Icc 1 N

/-- Sum over roots after retaining and summing every complete history fiber. -/
def completeSignedAmplitude (alpha L : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, ∑ h : History n, signedGaussianIntensity alpha L h

/-- The same amplitude after exact pushforward to generated roots. -/
def rootSignedAmplitude (alpha L : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, rootSignedMass alpha L n

theorem completeSignedAmplitude_eq_root (alpha L : ℝ) (N : ℕ) :
    completeSignedAmplitude alpha L N = rootSignedAmplitude alpha L N := by
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : 0 < n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  exact signedGaussian_pushforward alpha L n hnpos

/-- Ordered off-diagonal contribution.  Both `(m,n)` and `(n,m)` are retained,
so this is the full cross term without a sign-destroying estimate. -/
def orderedCrossEnergy (alpha L : ℝ) (N : ℕ) : ℝ :=
  ∑ m ∈ rootRange N,
    ∑ n ∈ (rootRange N).erase m,
      rootSignedMass alpha L m * rootSignedMass alpha L n

def diagonalEnergy (alpha L : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ rootRange N, rootSignedMass alpha L n ^ 2

/-- Energy of the complete finite signed amplitude. -/
def completeSignedEnergy (alpha L : ℝ) (N : ℕ) : ℝ :=
  completeSignedAmplitude alpha L N ^ 2

private theorem sum_square_eq_diagonal_add_orderedCross
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) :
    (∑ x ∈ s, f x) ^ 2 =
      (∑ x ∈ s, f x ^ 2) +
        ∑ x ∈ s, ∑ y ∈ s.erase x, f x * f y := by
  rw [pow_two, Finset.sum_mul_sum]
  calc
    (∑ x ∈ s, ∑ y ∈ s, f x * f y) =
        ∑ x ∈ s, (f x * f x + ∑ y ∈ s.erase x, f x * f y) := by
      apply Finset.sum_congr rfl
      intro x hx
      have h := Finset.sum_erase_add s (fun y => f x * f y) hx
      simpa only [add_comm] using h.symm
    _ = (∑ x ∈ s, f x * f x) +
        ∑ x ∈ s, ∑ y ∈ s.erase x, f x * f y :=
      Finset.sum_add_distrib
    _ = (∑ x ∈ s, f x ^ 2) +
        ∑ x ∈ s, ∑ y ∈ s.erase x, f x * f y := by
      congr 1
      apply Finset.sum_congr rfl
      intro x _
      ring

/-- Exact finite energy decomposition with every signed cross term present. -/
theorem completeSignedEnergy_decomposition (alpha L : ℝ) (N : ℕ) :
    completeSignedEnergy alpha L N =
      diagonalEnergy alpha L N + orderedCrossEnergy alpha L N := by
  rw [completeSignedEnergy, completeSignedAmplitude_eq_root,
    rootSignedAmplitude, diagonalEnergy, orderedCrossEnergy]
  exact sum_square_eq_diagonal_add_orderedCross (rootRange N)
    (rootSignedMass alpha L)

/-- The diagonal is supported exactly on squarefree generated roots; the
remaining arithmetic difficulty is therefore carried by the signed cross
term rather than hidden in the diagonal. -/
theorem diagonalEnergy_eq_squarefree (alpha L : ℝ) (N : ℕ) :
    diagonalEnergy alpha L N =
      ∑ n ∈ rootRange N,
        (squarefreeProjector n : ℝ) * gaussianRootMass alpha L n ^ 2 := by
  rw [diagonalEnergy]
  apply Finset.sum_congr rfl
  intro n _
  rw [rootSignedMass, mul_pow]
  have hsquare : ((generatedMoebius n : ℝ) ^ 2) =
      (squarefreeProjector n : ℝ) := by
    norm_cast
    exact generatedMoebius_sq n
  rw [hsquare]

/-- The finite source, its exact root pushforward and its unsplit energy
decomposition form the algebraic input to later uniform scale estimates. -/
structure Conclusions : Prop where
  pushforward : ∀ (alpha L : ℝ) (N : ℕ),
    completeSignedAmplitude alpha L N = rootSignedAmplitude alpha L N
  full_cross_term : ∀ (alpha L : ℝ) (N : ℕ),
    completeSignedEnergy alpha L N =
      diagonalEnergy alpha L N + orderedCrossEnergy alpha L N
  squarefree_diagonal : ∀ (alpha L : ℝ) (N : ℕ),
    diagonalEnergy alpha L N =
      ∑ n ∈ rootRange N,
        (squarefreeProjector n : ℝ) * gaussianRootMass alpha L n ^ 2

theorem signedGaussianEnergyConclusions : Conclusions where
  pushforward := completeSignedAmplitude_eq_root
  full_cross_term := completeSignedEnergy_decomposition
  squarefree_diagonal := diagonalEnergy_eq_squarefree

end GeneratedFoundations.Analysis.SignedGaussianEnergy
