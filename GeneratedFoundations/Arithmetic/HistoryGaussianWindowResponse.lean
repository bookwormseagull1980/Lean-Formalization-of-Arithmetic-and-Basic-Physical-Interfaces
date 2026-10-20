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

def coefficient (N : ℕ) (R : ℝ) (S : Finset (Index N)) : ℝ :=
  (∑ i ∈ S, branchIntegral N R i) / HistoryGaussianCovariance.componentCount N

theorem coefficient_pos (N : ℕ) {R : ℝ} (hR : 0 < R)
    (S : Finset (Index N)) (hS : S.Nonempty) : 0 < coefficient N R S := by
  apply div_pos
  · exact Finset.sum_pos (fun i _ => branchIntegral_pos N hR i) hS
  · exact Nat.cast_pos.mpr (HistoryGaussianCovariance.componentCount_pos N)

def response (N : ℕ) (R : ℝ) (S : Finset (Index N)) (c : ℝ) : ℝ :=
  coefficient N R S / c

def responseRoot (N : ℕ) (R : ℝ) (S : Finset (Index N)) : ℝ :=
  endpointRoot (coefficient N R S)

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
  certificate_consumption : ∀ N R S (b : CoefficientBounds N R S),
    rootLower b ≤ responseRoot N R S ∧ responseRoot N R S ≤ rootUpper b

theorem generated : Conclusions where
  actual_positive_integral := fun N _ hR => branchIntegral_pos N hR
  actual_positive_coefficient := fun N _ hR => coefficient_pos N hR
  unique_response_root := fun N _ hR => existsUnique_responseRoot N hR
  certificate_consumption := fun _ _ _ => consume_interval

end GeneratedFoundations.Arithmetic.HistoryGaussianWindowResponse
