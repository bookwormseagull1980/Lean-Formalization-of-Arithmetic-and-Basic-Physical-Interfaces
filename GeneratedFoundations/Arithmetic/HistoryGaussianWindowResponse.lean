module

public import GeneratedFoundations.Arithmetic.HistoryGaussianCovariance
public import GeneratedFoundations.Geometry.SourceTensorResponse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Gaussian observation of the actual joint response spectrum

A finite spectral observation retains a finite set of the complete joint
Hessian's eigenvectors. Each branch uses its calculated eigenvalue and the
unit-covariance Gaussian frequency weight. Neither physical multiplicities
nor a dimensional calibration enter this arithmetic coefficient.

The observation level and finite set specify a measurement of the same
source. They are not parameters of the generated source. The response root
below is the algebraic root for this particular spectral coefficient; it
is not an identification with the physical endpoint radius. An interval
certificate encloses this integral itself and is consumed by a proved
root bound.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryGaussianWindowResponse

open HistoryHaarJointHessian (Index eigenvalue)
open Geometry.SourceTensorResponse (endpointRoot endpointResidual)

def kernel (N : ℕ) (i : Index N) (u : ℝ) : ℝ :=
  (u ^ 2 / (u ^ 2 + eigenvalue N i)) ^ 2 * Real.exp (-u ^ 2)

theorem kernel_nonneg (N : ℕ) (i : Index N) (u : ℝ) : 0 ≤ kernel N i u :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem kernel_pos (N : ℕ) (i : Index N) {u : ℝ} (hu : 0 < u) :
    0 < kernel N i u :=
  mul_pos (sq_pos_of_pos (div_pos (sq_pos_of_pos hu)
    (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (HistoryHaarJointHessian.eigenvalue_pos N i)))) (Real.exp_pos _)

theorem kernel_continuous (N : ℕ) (i : Index N) : Continuous (kernel N i) := by
  have hd : ∀ u : ℝ, u ^ 2 + eigenvalue N i ≠ 0 := by
    intro u
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (HistoryHaarJointHessian.eigenvalue_pos N i))
  unfold kernel
  fun_prop (disch := exact hd _)

def branchIntegral (N : ℕ) (R : ℝ) (i : Index N) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt R, kernel N i u

theorem branchIntegral_pos (N : ℕ) {R : ℝ} (hR : 0 < R) (i : Index N) :
    0 < branchIntegral N R i := by
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((kernel_continuous N i).intervalIntegrable _ _) (fun u h => ?_)
    (Real.sqrt_pos.mpr hR)
  exact mul_pos (sq_pos_of_pos (div_pos (sq_pos_of_pos h.1)
    (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (HistoryHaarJointHessian.eigenvalue_pos N i)))) (Real.exp_pos _)

/-- Increasing the observed frequency window strictly changes every actual
branch integral. The Gaussian weight is positive outside every finite window. -/
theorem branchIntegral_strictMonoOn (N : ℕ) (i : Index N) :
    StrictMonoOn (fun R => branchIntegral N R i) (Set.Ici 0) := by
  intro R₁ hR₁ R₂ _ hR
  have hs : Real.sqrt R₁ < Real.sqrt R₂ := Real.sqrt_lt_sqrt hR₁ hR
  have hp : 0 < ∫ u in Real.sqrt R₁..Real.sqrt R₂, kernel N i u :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((kernel_continuous N i).intervalIntegrable _ _)
      (fun u hu => kernel_pos N i (lt_of_le_of_lt (Real.sqrt_nonneg R₁) hu.1)) hs
  have ha : (∫ u in (0 : ℝ)..Real.sqrt R₁, kernel N i u) +
      (∫ u in Real.sqrt R₁..Real.sqrt R₂, kernel N i u) =
      ∫ u in (0 : ℝ)..Real.sqrt R₂, kernel N i u :=
    intervalIntegral.integral_add_adjacent_intervals
    ((kernel_continuous N i).intervalIntegrable 0 (Real.sqrt R₁))
    ((kernel_continuous N i).intervalIntegrable (Real.sqrt R₁) (Real.sqrt R₂))
  dsimp [branchIntegral]
  linarith

def coefficient (N : ℕ) (R : ℝ) (S : Finset (Index N)) : ℝ :=
  (∑ i ∈ S, branchIntegral N R i) / HistoryGaussianCovariance.componentCount N

theorem coefficient_pos (N : ℕ) {R : ℝ} (hR : 0 < R)
    (S : Finset (Index N)) (hS : S.Nonempty) : 0 < coefficient N R S := by
  apply div_pos
  · exact Finset.sum_pos (fun i _ => branchIntegral_pos N hR i) hS
  · exact Nat.cast_pos.mpr (HistoryGaussianCovariance.componentCount_pos N)

theorem coefficient_strictMonoOn (N : ℕ) (S : Finset (Index N))
    (hS : S.Nonempty) :
    StrictMonoOn (fun R => coefficient N R S) (Set.Ici 0) := by
  intro R₁ hR₁ R₂ hR₂ hR
  exact div_lt_div_of_pos_right
    (Finset.sum_lt_sum_of_nonempty hS
      (fun i _ => branchIntegral_strictMonoOn N i hR₁ hR₂ hR))
    (Nat.cast_pos.mpr (HistoryGaussianCovariance.componentCount_pos N))

def response (N : ℕ) (R : ℝ) (S : Finset (Index N)) (c : ℝ) : ℝ :=
  coefficient N R S / c

def responseRoot (N : ℕ) (R : ℝ) (S : Finset (Index N)) : ℝ :=
  endpointRoot (coefficient N R S)

theorem responseRoot_strictMonoOn (N : ℕ) (S : Finset (Index N))
    (hS : S.Nonempty) :
    StrictMonoOn (fun R => responseRoot N R S) (Set.Ici 0) := by
  intro R₁ hR₁ R₂ hR₂ hR
  have h := coefficient_strictMonoOn N S hS hR₁ hR₂ hR
  dsimp [responseRoot, endpointRoot]
  linarith

theorem responseRoot_pos (N : ℕ) {R : ℝ} (hR : 0 < R)
    (S : Finset (Index N)) (hS : S.Nonempty) : 0 < responseRoot N R S :=
  Geometry.SourceTensorResponse.endpointRoot_pos (coefficient_pos N hR S hS)

theorem response_eq_iff (N : ℕ) {R : ℝ} (hR : 0 < R)
    (S : Finset (Index N)) (hS : S.Nonempty) {c : ℝ} (hc : 0 < c) :
    response N R S c = 4 / 27 ↔ c = responseRoot N R S := by
  simpa only [response, responseRoot, endpointResidual, sub_eq_zero] using
    (Geometry.SourceTensorResponse.endpointResidual_eq_zero_iff
      (coefficient_pos N hR S hS) hc)

theorem existsUnique_responseRoot (N : ℕ) {R : ℝ} (hR : 0 < R)
    (S : Finset (Index N)) (hS : S.Nonempty) :
    ∃! c : ℝ, 0 < c ∧ response N R S c = 4 / 27 := by
  refine ⟨responseRoot N R S, ⟨responseRoot_pos N hR S hS, ?_⟩, ?_⟩
  · exact (response_eq_iff N hR S hS (responseRoot_pos N hR S hS)).mpr rfl
  · intro c hc
    exact (response_eq_iff N hR S hS hc.1).mp hc.2

/-- The algebraic endpoint equation does not select its own observation
window: at every positive level there is a larger admissible level with a
different positive root of the same normalized response equation. -/
theorem response_equation_does_not_select_window (N : ℕ)
    (S : Finset (Index N)) (hS : S.Nonempty) {R : ℝ} (hR : 0 < R) :
    ∃ R' : ℝ, R < R' ∧
      responseRoot N R S < responseRoot N R' S ∧
      response N R S (responseRoot N R S) = 4 / 27 ∧
      response N R' S (responseRoot N R' S) = 4 / 27 := by
  refine ⟨R + 1, by linarith, ?_, ?_, ?_⟩
  · exact responseRoot_strictMonoOn N S hS hR.le
      (by change 0 ≤ R + 1; linarith) (by linarith)
  · exact (response_eq_iff N hR S hS (responseRoot_pos N hR S hS)).mpr rfl
  · have hp : 0 < R + 1 := by linarith
    exact (response_eq_iff N hp S hS (responseRoot_pos N hp S hS)).mpr rfl

/-- Bounds are propositions about the same finite Gaussian integral, not
an independent coefficient supplied to the response definition. -/
structure CoefficientBounds (N : ℕ) (R : ℝ) (S : Finset (Index N)) where
  lo : ℝ
  hi : ℝ
  lo_pos : 0 < lo
  encloses : lo ≤ coefficient N R S ∧ coefficient N R S ≤ hi

def rootLower {N : ℕ} {R : ℝ} {S : Finset (Index N)}
    (b : CoefficientBounds N R S) : ℝ := 27 * b.lo / 4

def rootUpper {N : ℕ} {R : ℝ} {S : Finset (Index N)}
    (b : CoefficientBounds N R S) : ℝ := 27 * b.hi / 4

theorem consume_interval {N : ℕ} {R : ℝ} {S : Finset (Index N)}
    (b : CoefficientBounds N R S) :
    rootLower b ≤ responseRoot N R S ∧ responseRoot N R S ≤ rootUpper b := by
  dsimp [rootLower, rootUpper, responseRoot, endpointRoot]
  constructor <;> nlinarith [b.encloses.1, b.encloses.2]

structure Conclusions : Prop where
  actual_positive_integral : ∀ N R, 0 < R → ∀ i, 0 < branchIntegral N R i
  actual_positive_coefficient : ∀ N R, 0 < R → ∀ S, S.Nonempty →
    0 < coefficient N R S
  unique_response_root : ∀ N R, 0 < R → ∀ S, S.Nonempty →
    ∃! c : ℝ, 0 < c ∧ response N R S c = 4 / 27
  window_strict_monotonicity : ∀ N S, S.Nonempty →
    StrictMonoOn (fun R => responseRoot N R S) (Set.Ici 0)
  certificate_consumption : ∀ N R S (b : CoefficientBounds N R S),
    rootLower b ≤ responseRoot N R S ∧ responseRoot N R S ≤ rootUpper b

theorem generated : Conclusions where
  actual_positive_integral := fun N _ hR => branchIntegral_pos N hR
  actual_positive_coefficient := fun N _ hR => coefficient_pos N hR
  unique_response_root := fun N _ hR => existsUnique_responseRoot N hR
  window_strict_monotonicity := responseRoot_strictMonoOn
  certificate_consumption := fun _ _ _ => consume_interval

end GeneratedFoundations.Arithmetic.HistoryGaussianWindowResponse
