module

public import GeneratedFoundations.Arithmetic.HistoryGaugeJets
public import GeneratedFoundations.Geometry.HilbertTraceVariation
public import Mathlib.Tactic.Module

/-!
# Full variation of the arithmetic curvature density

Both connection slots vary on the actual arithmetic carrier. The curvature
along a line has a linearized term and a quadratic commutator term. Squaring
its complete trace norm therefore gives a quartic action, not merely the
square of its linearization. The background--commutator term remains in the
second variation.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryCurvatureVariation

open HistoryGaugeJets
open Geometry.HilbertTraceVariation

def line (N : ℕ) (A V : ConnectionJet N) (t : ℂ) : ConnectionJet N where
  value μ := A.value μ + t • V.value μ
  derivative μ ν := A.derivative μ ν + t • V.derivative μ ν

def linearized (N : ℕ) (A V : ConnectionJet N) (μ ν : CoordinateIndex N) : Operator N :=
  V.derivative μ ν - V.derivative ν μ +
    (V.value μ * A.value ν + A.value μ * V.value ν -
      V.value ν * A.value μ - A.value ν * V.value μ)

def quadraticTerm (N : ℕ) (V : ConnectionJet N) (μ ν : CoordinateIndex N) : Operator N :=
  V.value μ * V.value ν - V.value ν * V.value μ

theorem curvature_line (N : ℕ) (A V : ConnectionJet N) (t : ℂ)
    (μ ν : CoordinateIndex N) :
    curvature (line N A V t) μ ν = curvature A μ ν +
      t • linearized N A V μ ν + t ^ 2 • quadraticTerm N V μ ν := by
  simp only [curvature, Geometry.ConnectionJetAlgebra.curvature, line,
    linearized, quadraticTerm, add_mul, mul_add, mul_smul_comm,
    smul_mul_assoc]
  module

/-- The half trace norm uses the complete curvature, with both ordered slots. -/
def action (N : ℕ) (A : ConnectionJet N) : ℝ := curvatureDensity N A / 2

def firstVariation (N : ℕ) (A V : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, pair (curvature A μ ν) (linearized N A V μ ν)

def secondVariation (N : ℕ) (A V : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, (quadratic N (linearized N A V μ ν) +
    2 * pair (curvature A μ ν) (quadraticTerm N V μ ν))

def lineDerivative (N : ℕ) (A V : ConnectionJet N) (t : ℝ) : ℝ :=
  ∑ μ, ∑ ν,
    (pair (curvature A μ ν) (linearized N A V μ ν) +
      t * (quadratic N (linearized N A V μ ν) +
        2 * pair (curvature A μ ν) (quadraticTerm N V μ ν)) +
      3 * t ^ 2 * pair (linearized N A V μ ν) (quadraticTerm N V μ ν) +
      2 * t ^ 3 * quadratic N (quadraticTerm N V μ ν))

theorem action_line_hasDerivAt (N : ℕ) (A V : ConnectionJet N) (t : ℝ) :
    HasDerivAt (fun s : ℝ => action N (line N A V (s : ℂ)))
      (lineDerivative N A V t) t := by
  have h (μ ν : CoordinateIndex N) :=
    (energy_quadratic_path_hasDerivAt (curvature A μ ν)
      (linearized N A V μ ν) (quadraticTerm N V μ ν) t).div_const 2
  have hs := HasDerivAt.sum (u := Finset.univ) (fun μ _ =>
    HasDerivAt.sum (u := Finset.univ) (fun ν _ => h μ ν))
  convert hs using 1
  · funext s
    simp only [action, curvatureDensity, quadratic, Finset.sum_div, curvature_line,
      Complex.ofReal_pow, Finset.sum_apply]
  · simp only [lineDerivative, quadratic]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    ring

@[simp] theorem lineDerivative_zero (N : ℕ) (A V : ConnectionJet N) :
    lineDerivative N A V 0 = firstVariation N A V := by
  simp [lineDerivative, firstVariation]

theorem action_first_deriv (N : ℕ) (A V : ConnectionJet N) :
    deriv (fun s : ℝ => action N (line N A V (s : ℂ))) 0 = firstVariation N A V := by
  rw [(action_line_hasDerivAt N A V 0).deriv, lineDerivative_zero]

theorem lineDerivative_hasDerivAt_zero (N : ℕ) (A V : ConnectionJet N) :
    HasDerivAt (lineDerivative N A V) (secondVariation N A V) 0 := by
  have h (μ ν : CoordinateIndex N) := quartic_hasDerivAt
    (pair (curvature A μ ν) (linearized N A V μ ν))
    (quadratic N (linearized N A V μ ν) +
      2 * pair (curvature A μ ν) (quadraticTerm N V μ ν))
    (3 * pair (linearized N A V μ ν) (quadraticTerm N V μ ν))
    (2 * quadratic N (quadraticTerm N V μ ν)) 0 0
  have hs := HasDerivAt.sum (u := Finset.univ) (fun μ _ =>
    HasDerivAt.sum (u := Finset.univ) (fun ν _ => h μ ν))
  convert hs using 1
  · funext s
    simp only [lineDerivative, mul_zero, add_zero, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro μ _
    apply Finset.sum_congr rfl
    intro ν _
    ring
  · simp [secondVariation]

theorem action_second_deriv (N : ℕ) (A V : ConnectionJet N) :
    deriv (fun t : ℝ => deriv (fun s : ℝ => action N (line N A V (s : ℂ))) t) 0 =
      secondVariation N A V := by
  have he : (fun t : ℝ => deriv (fun s : ℝ => action N (line N A V (s : ℂ))) t) =
      lineDerivative N A V := funext fun t => (action_line_hasDerivAt N A V t).deriv
  rw [he]
  exact (lineDerivative_hasDerivAt_zero N A V).deriv

def mixedCurvature (N : ℕ) (V W : ConnectionJet N) (μ ν : CoordinateIndex N) :
    Operator N :=
  W.value μ * V.value ν + V.value μ * W.value ν -
    W.value ν * V.value μ - V.value ν * W.value μ

theorem mixedCurvature_symm (N : ℕ) (V W : ConnectionJet N) (μ ν : CoordinateIndex N) :
    mixedCurvature N V W μ ν = mixedCurvature N W V μ ν := by
  simp only [mixedCurvature]
  abel

theorem linearized_line (N : ℕ) (A V W : ConnectionJet N) (t : ℂ)
    (μ ν : CoordinateIndex N) :
    linearized N (line N A W t) V μ ν = linearized N A V μ ν +
      t • mixedCurvature N V W μ ν := by
  simp only [linearized, line, mixedCurvature, add_mul, mul_add,
    mul_smul_comm, smul_mul_assoc]
  module

def hessian (N : ℕ) (A V W : ConnectionJet N) : ℝ :=
  ∑ μ, ∑ ν, (pair (linearized N A W μ ν) (linearized N A V μ ν) +
    pair (curvature A μ ν) (mixedCurvature N V W μ ν))

theorem hessian_symm (N : ℕ) (A V W : ConnectionJet N) :
    hessian N A V W = hessian N A W V := by
  unfold hessian
  apply Finset.sum_congr rfl
  intro μ _
  apply Finset.sum_congr rfl
  intro ν _
  rw [pair_symm (linearized N A W μ ν), mixedCurvature_symm]

theorem hessian_diagonal (N : ℕ) (A V : ConnectionJet N) :
    hessian N A V V = secondVariation N A V := by
  have hm (μ ν : CoordinateIndex N) :
      mixedCurvature N V V μ ν = ((2 : ℝ) : ℂ) • quadraticTerm N V μ ν := by
    simp only [mixedCurvature, quadraticTerm]
    module
  simp only [hessian, secondVariation, hm, pair_smul_right, quadratic,
    ← energy_eq_pair]

/-- This is the mixed derivative of the same complete action's first variation. -/
theorem firstVariation_line_hasDerivAt_zero (N : ℕ) (A V W : ConnectionJet N) :
    HasDerivAt (fun t : ℝ => firstVariation N (line N A W (t : ℂ)) V)
      (hessian N A V W) 0 := by
  have h (μ ν : CoordinateIndex N) := pair_quadratic_linear_hasDerivAt_zero
    (curvature A μ ν) (linearized N A W μ ν) (quadraticTerm N W μ ν)
    (linearized N A V μ ν) (mixedCurvature N V W μ ν)
  have hs := HasDerivAt.sum (u := Finset.univ) (fun μ _ =>
    HasDerivAt.sum (u := Finset.univ) (fun ν _ => h μ ν))
  convert hs using 1
  · funext t
    simp only [firstVariation, curvature_line, linearized_line,
      Complex.ofReal_pow, Finset.sum_apply]
  · rfl

theorem action_mixed_deriv (N : ℕ) (A V W : ConnectionJet N) :
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      action N (line N (line N A W (t : ℂ)) V (s : ℂ))) 0) 0 =
      hessian N A V W := by
  have he : (fun t : ℝ => deriv (fun s : ℝ =>
      action N (line N (line N A W (t : ℂ)) V (s : ℂ))) 0) =
      (fun t : ℝ => firstVariation N (line N A W (t : ℂ)) V) := by
    funext t
    exact action_first_deriv N (line N A W (t : ℂ)) V
  rw [he]
  exact (firstVariation_line_hasDerivAt_zero N A V W).deriv

theorem hessian_flat_nonneg (N : ℕ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) : 0 ≤ hessian N A V V := by
  unfold hessian
  apply Finset.sum_nonneg
  intro μ _
  apply Finset.sum_nonneg
  intro ν _
  have he := Geometry.HilbertTraceQuadratic.energy_nonneg (linearized N A V μ ν)
  simpa [hA, pair, Geometry.HilbertTraceQuadratic.energy] using he

theorem hessian_flat_eq_zero_iff (N : ℕ) (A V : ConnectionJet N)
    (hA : ∀ μ ν, curvature A μ ν = 0) :
    hessian N A V V = 0 ↔ ∀ μ ν, linearized N A V μ ν = 0 := by
  have he : hessian N A V V = ∑ μ, ∑ ν, quadratic N (linearized N A V μ ν) := by
    simp [hessian, hA, pair, quadratic, Geometry.HilbertTraceQuadratic.energy]
  rw [he]
  constructor
  · intro h μ ν
    have hμ := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      Finset.sum_nonneg fun j _ => quadratic_nonneg N (linearized N A V i j))).mp h μ
        (Finset.mem_univ μ)
    have hμν := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      quadratic_nonneg N (linearized N A V μ j))).mp hμ ν (Finset.mem_univ ν)
    exact (quadratic_eq_zero_iff N _).mp hμν
  · intro h
    simp [h, quadratic, Geometry.HilbertTraceQuadratic.energy_zero]

def constantGauge (N : ℕ) (g : HistoryElementaryConnector.Frame) : GaugeTwoJet N where
  value := g
  first := fun _ => 0
  second := fun _ _ => 0
  mixed_second := fun _ _ => rfl

def changeFrame (N : ℕ) (g : HistoryElementaryConnector.Frame) (A : ConnectionJet N) :
    ConnectionJet N := transformConnectionJet N (constantGauge N g) A

theorem changeFrame_line (N : ℕ) (g : HistoryElementaryConnector.Frame)
    (A V : ConnectionJet N) (t : ℂ) :
    changeFrame N g (line N A V t) =
      line N (changeFrame N g A) (changeFrame N g V) t := by
  simp [changeFrame, constantGauge, transformConnectionJet, algebraicGaugeJet,
    Geometry.ConnectionJetAlgebra.transform, Geometry.ConnectionJetAlgebra.inverseDerivative,
    line, add_mul, mul_add]

theorem action_changeFrame (N : ℕ) (g : HistoryElementaryConnector.Frame)
    (A : ConnectionJet N) : action N (changeFrame N g A) = action N A := by
  rw [action, changeFrame, curvatureDensity_transform, action]

theorem firstVariation_changeFrame (N : ℕ) (g : HistoryElementaryConnector.Frame)
    (A V : ConnectionJet N) :
    firstVariation N (changeFrame N g A) (changeFrame N g V) = firstVariation N A V := by
  have he : (fun s : ℝ => action N
      (line N (changeFrame N g A) (changeFrame N g V) (s : ℂ))) =
      (fun s : ℝ => action N (line N A V (s : ℂ))) := by
    funext s
    rw [← changeFrame_line, action_changeFrame]
  rw [← action_first_deriv, he, action_first_deriv]

theorem hessian_changeFrame (N : ℕ) (g : HistoryElementaryConnector.Frame)
    (A V W : ConnectionJet N) :
    hessian N (changeFrame N g A) (changeFrame N g V) (changeFrame N g W) =
      hessian N A V W := by
  have he : (fun t : ℝ => firstVariation N
      (line N (changeFrame N g A) (changeFrame N g W) (t : ℂ)) (changeFrame N g V)) =
      (fun t : ℝ => firstVariation N (line N A W (t : ℂ)) V) := by
    funext t
    rw [← changeFrame_line, firstVariation_changeFrame]
  rw [← (firstVariation_line_hasDerivAt_zero N (changeFrame N g A)
    (changeFrame N g V) (changeFrame N g W)).deriv, he,
    (firstVariation_line_hasDerivAt_zero N A V W).deriv]

structure Conclusions : Prop where
  first_derivative : ∀ N A V,
    deriv (fun s : ℝ => action N (line N A V (s : ℂ))) 0 = firstVariation N A V
  second_derivative : ∀ N A V,
    deriv (fun t : ℝ => deriv (fun s : ℝ => action N (line N A V (s : ℂ))) t) 0 =
      secondVariation N A V
  mixed_derivative : ∀ N A V W,
    deriv (fun t : ℝ => deriv (fun s : ℝ =>
      action N (line N (line N A W (t : ℂ)) V (s : ℂ))) 0) 0 = hessian N A V W
  mixed_symmetric : ∀ N A V W, hessian N A V W = hessian N A W V
  flat_nonnegative : ∀ N A V, (∀ μ ν, curvature A μ ν = 0) →
    0 ≤ hessian N A V V
  action_invariant : ∀ N g A, action N (changeFrame N g A) = action N A
  hessian_invariant : ∀ N g A V W,
    hessian N (changeFrame N g A) (changeFrame N g V) (changeFrame N g W) =
      hessian N A V W

theorem generated : Conclusions where
  first_derivative := action_first_deriv
  second_derivative := action_second_deriv
  mixed_derivative := action_mixed_deriv
  mixed_symmetric := hessian_symm
  flat_nonnegative := hessian_flat_nonneg
  action_invariant := action_changeFrame
  hessian_invariant := hessian_changeFrame

end GeneratedFoundations.Arithmetic.HistoryCurvatureVariation
