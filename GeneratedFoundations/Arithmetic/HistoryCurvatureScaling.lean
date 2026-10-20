module

public import GeneratedFoundations.Arithmetic.HistoryCurvatureVariation

/-!
# Exact amplitude scaling of the complete arithmetic curvature

The derivative and commutator parts scale with different degrees. The
complete action contains their cubic interference as well as the quadratic
and quartic terms. These formulas use every actual coordinate direction and
every matrix coefficient of the history--phase/source carrier.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCurvatureScaling

open HistoryGaugeJets
open Geometry.HilbertTraceVariation

def scale (N : ℕ) (t : ℝ) (A : ConnectionJet N) : ConnectionJet N where
  value μ := (t : ℂ) • A.value μ
  derivative μ ν := (t : ℂ) • A.derivative μ ν

def linearCurvature (N : ℕ) (A : ConnectionJet N) (μ ν : CoordinateIndex N) :
    Operator N := A.derivative μ ν - A.derivative ν μ

def bracketCurvature (N : ℕ) (A : ConnectionJet N) (μ ν : CoordinateIndex N) :
    Operator N := A.value μ * A.value ν - A.value ν * A.value μ

theorem curvature_decomposition (N : ℕ) (A : ConnectionJet N) (μ ν : CoordinateIndex N) :
    curvature A μ ν = linearCurvature N A μ ν + bracketCurvature N A μ ν := by
  simp only [curvature, Geometry.ConnectionJetAlgebra.curvature,
    linearCurvature, bracketCurvature]

theorem linearCurvature_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N)
    (μ ν : CoordinateIndex N) :
    linearCurvature N (scale N t A) μ ν = (t : ℂ) • linearCurvature N A μ ν := by
  simp [linearCurvature, scale, smul_sub]

theorem bracketCurvature_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N)
    (μ ν : CoordinateIndex N) :
    bracketCurvature N (scale N t A) μ ν =
      ((t ^ 2 : ℝ) : ℂ) • bracketCurvature N A μ ν := by
  simp only [bracketCurvature, scale, smul_mul_assoc, mul_smul_comm,
    smul_smul, ← smul_sub, pow_two, Complex.ofReal_mul]

theorem quadratic_smul (N : ℕ) (t : ℝ) (X : Operator N) :
    quadratic N ((t : ℂ) • X) = t ^ 2 * quadratic N X := by
  change pair ((t : ℂ) • X) ((t : ℂ) • X) = t ^ 2 * pair X X
  rw [pair_smul_left, pair_smul_right]
  ring

theorem quadratic_add (N : ℕ) (X Y : Operator N) :
    quadratic N (X + Y) = quadratic N X + 2 * pair X Y + quadratic N Y := by
  change pair (X + Y) (X + Y) = pair X X + 2 * pair X Y + pair Y Y
  rw [pair_add_left, pair_add_right, pair_add_right, pair_symm Y X]
  ring

def connectionDensity (N : ℕ) (A : ConnectionJet N) : ℝ :=
  ∑ μ, quadratic N (A.value μ)

def linearDensity (N : ℕ) (A : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, quadratic N (linearCurvature N A μ ν)

def bracketDensity (N : ℕ) (A : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, quadratic N (bracketCurvature N A μ ν)

def interference (N : ℕ) (A : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, pair (linearCurvature N A μ ν) (bracketCurvature N A μ ν)

theorem density_decomposition (N : ℕ) (A : ConnectionJet N) :
    curvatureDensity N A = linearDensity N A + 2 * interference N A + bracketDensity N A := by
  simp only [curvatureDensity, curvature_decomposition, quadratic_add,
    linearDensity, interference, bracketDensity, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem connectionDensity_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N) :
    connectionDensity N (scale N t A) = t ^ 2 * connectionDensity N A := by
  simp only [connectionDensity, scale, quadratic_smul, Finset.mul_sum]

theorem linearDensity_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N) :
    linearDensity N (scale N t A) = t ^ 2 * linearDensity N A := by
  simp only [linearDensity, linearCurvature_scale, quadratic_smul, Finset.mul_sum]

theorem bracketDensity_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N) :
    bracketDensity N (scale N t A) = t ^ 4 * bracketDensity N A := by
  simp only [bracketDensity, bracketCurvature_scale, quadratic_smul,
    ← Finset.mul_sum]
  congr 1
  ring

theorem interference_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N) :
    interference N (scale N t A) = t ^ 3 * interference N A := by
  simp only [interference, linearCurvature_scale, bracketCurvature_scale,
    pair_smul_left, pair_smul_right, ← mul_assoc, ← Finset.mul_sum]
  congr 1

theorem full_density_scale (N : ℕ) (t : ℝ) (A : ConnectionJet N) :
    curvatureDensity N (scale N t A) = t ^ 2 * linearDensity N A +
      2 * t ^ 3 * interference N A + t ^ 4 * bracketDensity N A := by
  rw [density_decomposition, linearDensity_scale, interference_scale, bracketDensity_scale]
  ring

structure Conclusions : Prop where
  full_decomposition : ∀ N A, curvatureDensity N A =
    linearDensity N A + 2 * interference N A + bracketDensity N A
  complete_scaling : ∀ N t A, curvatureDensity N (scale N t A) =
    t ^ 2 * linearDensity N A + 2 * t ^ 3 * interference N A + t ^ 4 * bracketDensity N A

theorem generated : Conclusions where
  full_decomposition := density_decomposition
  complete_scaling := full_density_scale

end GeneratedFoundations.Arithmetic.HistoryCurvatureScaling
