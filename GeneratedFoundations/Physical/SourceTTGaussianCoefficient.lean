module

public import GeneratedFoundations.Physical.SourceTorsionContent
public import GeneratedFoundations.Physical.SourceTensorResponseEndpoint
public import GeneratedFoundations.Physical.SourceTTResponseNormalization
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Tactic

/-!
# Reduced eight-branch TT coefficient

This module defines the reduced eight-branch coefficient used by the
certificate-conditional endpoint model. The branches are integrated with their
Gaussian frequency weight; the torsion shift is the generated content value,
not a parameter supplied to the endpoint certificate. Multiplicities include
the three matter copies.

At the self-consistent scale the change of frequency variable `u = c * omega`
leaves a dimensionless coefficient `A₅`; this model uses the response `A₅ / c`.
The V5 certificate `tt_branch_reduction` proves externally that, on the
endpoint bracket, the full active V5 spectrum is exactly these eight branches
and that `A_V5(c)=A_5/c`; that bridge is not formalized in this module.
Numerical enclosures of the coefficient are additional, independently
checkable propositions about this coefficient model.

The kinetic insertion in the same positive precision Gaussian realizes
each rational mode kernel as twice its quadratic-score variance. The
coefficient below is therefore also an integral of these source responses.
The common-normalization theorem transports the existing endpoint rule
under simultaneous calibration of the coefficient and reference profile.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceTTGaussianCoefficient

open SourceTorsionContent SourceTensorResponseEndpoint

def torsion : ℝ := (torsionTau : ℝ)

theorem torsion_eq : torsion = 1 / 50 := by
  simp only [torsion, torsionTau_eq]
  norm_num

/-- `(Laplacian index, mass index, weighted multiplicity)` of the eight
retained branches. The final three entries include all three matter copies. -/
def branch : Fin 8 → ℝ × ℝ × ℝ :=
  ![(0, 3 / 4, 4), (8, 3 / 4, 36),
    (4, 3 / 2 + torsion ^ 2 / 6, 192),
    (4, 1 + torsion ^ 2 / 6, 72), (4, torsion ^ 2 / 6, 24),
    (9 / 4, 3 * torsion ^ 2 / 8, 168),
    (25 / 4, 3 * torsion ^ 2 / 8, 576),
    (49 / 4, 3 * torsion ^ 2 / 8, 1008)]

theorem branch_bounds (i : Fin 8) :
    0 ≤ (branch i).1 ∧ (branch i).1 < 5 * Real.pi ∧
      0 < (branch i).2.1 ∧ 0 < (branch i).2.2 := by
  have hpi := Real.pi_gt_three
  fin_cases i <;> norm_num [branch, torsion_eq] <;> linarith

def kernel (a b u : ℝ) : ℝ :=
  ((u ^ 2 + a) / (u ^ 2 + a + b)) ^ 2 *
    Real.exp (-(u ^ 2 + a) / Real.pi)

theorem kernel_nonneg (a b u : ℝ) : 0 ≤ kernel a b u :=
  mul_nonneg (sq_nonneg _) (Real.exp_pos _).le

theorem kernel_continuous {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    Continuous (kernel a b) := by
  have hd : ∀ u : ℝ, u ^ 2 + a + b ≠ 0 := by
    intro u
    exact ne_of_gt (by nlinarith [sq_nonneg u])
  unfold kernel
  fun_prop (disch := exact hd _)

/-- The selected kinetic comparison has the displayed kernel in its original
one-coordinate Gaussian law, including the real quadratic-insertion factor. -/
theorem kernel_eq_gaussian_response {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (u : ℝ) :
    kernel a b u =
      SourceTTResponseNormalization.gaussianModeResponse (u ^ 2 + a) b *
        Real.exp (-(u ^ 2 + a) / Real.pi) := by
  rw [SourceTTResponseNormalization.gaussianModeResponse_eq _ _
    (by nlinarith [sq_nonneg u])]
  simp only [kernel, ttKernel, div_pow]

def branchIntegral (i : Fin 8) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (5 * Real.pi - (branch i).1),
    kernel (branch i).1 (branch i).2.1 u

theorem branchIntegral_eq_gaussian_response (i : Fin 8) :
    branchIntegral i =
      ∫ u in (0 : ℝ)..Real.sqrt (5 * Real.pi - (branch i).1),
        SourceTTResponseNormalization.gaussianModeResponse
          (u ^ 2 + (branch i).1) (branch i).2.1 *
            Real.exp (-(u ^ 2 + (branch i).1) / Real.pi) := by
  unfold branchIntegral
  congr 1
  funext u
  exact kernel_eq_gaussian_response (branch_bounds i).1 (branch_bounds i).2.2.1 u

theorem branchIntegral_pos (i : Fin 8) : 0 < branchIntegral i := by
  obtain ⟨ha, hwindow, hb, _⟩ := branch_bounds i
  have hu : 0 < Real.sqrt (5 * Real.pi - (branch i).1) :=
    Real.sqrt_pos.2 (sub_pos.2 hwindow)
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    ((kernel_continuous ha hb).intervalIntegrable _ _)
    (fun u h => ?_) hu
  have hq : 0 < u ^ 2 + (branch i).1 := by
    nlinarith [sq_pos_of_pos h.1]
  exact mul_pos (sq_pos_of_pos (div_pos hq (by linarith))) (Real.exp_pos _)

/-- Coefficient of the *actual* V5 finite-window response, before multiplication
by the universal endpoint factor `27/4`. -/
def coefficient : ℝ :=
  (1 / (32 * Real.pi ^ 3)) *
    ∑ i : Fin 8, (branch i).2.2 * branchIntegral i

theorem coefficient_eq_gaussian_response :
    coefficient = (1 / (32 * Real.pi ^ 3)) *
      ∑ i : Fin 8, (branch i).2.2 *
        (∫ u in (0 : ℝ)..Real.sqrt (5 * Real.pi - (branch i).1),
          SourceTTResponseNormalization.gaussianModeResponse
            (u ^ 2 + (branch i).1) (branch i).2.1 *
              Real.exp (-(u ^ 2 + (branch i).1) / Real.pi)) := by
  simp only [coefficient, branchIntegral_eq_gaussian_response]

theorem coefficient_pos : 0 < coefficient := by
  unfold coefficient
  apply mul_pos (by positivity)
  exact Finset.sum_pos (fun i _ =>
    mul_pos (branch_bounds i).2.2.2 (branchIntegral_pos i)) Finset.univ_nonempty

def response (c : ℝ) : ℝ := coefficient / c

def radius : ℝ := endpointRoot coefficient

theorem radius_pos : 0 < radius := endpointRoot_pos coefficient_pos

theorem response_radius : response radius = 4 / 27 := by
  have h := endpointResidual_root coefficient_pos
  change coefficient / endpointRoot coefficient - 4 / 27 = 0 at h
  exact sub_eq_zero.mp h

/-- The integral, rather than a separately recorded response number, selects
the unique positive endpoint. -/
theorem response_eq_iff {c : ℝ} (hc : 0 < c) :
    response c = 4 / 27 ↔ c = radius := by
  simpa only [response, radius, endpointResidual, sub_eq_zero] using
    (endpointResidual_eq_zero_iff coefficient_pos hc)

theorem existsUnique_endpoint : ∃! c : ℝ, 0 < c ∧ response c = 4 / 27 := by
  refine ⟨radius, ⟨radius_pos, response_radius⟩, ?_⟩
  intro c hc
  exact (response_eq_iff hc.1).mp hc.2

/-- Rescaling the same source response and its reference profile preserves
the actual integral-defined endpoint. -/
theorem calibrated_response_eq_iff {κ c : ℝ} (hκ : 0 < κ) (hc : 0 < c) :
    κ * response c = κ * massWeightedResponse (1 / 3) ↔ c = radius := by
  simpa only [SourceTTResponseNormalization.calibratedResponse,
    SourceTTResponseNormalization.calibratedProfile, response, radius] using
    SourceTTResponseNormalization.common_normalization_matching_iff hκ coefficient_pos hc

structure Conclusions : Prop where
  normalization : SourceTTResponseNormalization.Conclusions
  content_torsion : torsion = 1 / 50
  coefficient_positive : 0 < coefficient
  endpoint_positive : 0 < radius
  endpoint_equation : response radius = 4 / 27
  endpoint_unique : ∀ c : ℝ, 0 < c → (response c = 4 / 27 ↔ c = radius)

theorem generated : Conclusions where
  normalization := SourceTTResponseNormalization.generated
  content_torsion := torsion_eq
  coefficient_positive := coefficient_pos
  endpoint_positive := radius_pos
  endpoint_equation := response_radius
  endpoint_unique := fun _ hc => response_eq_iff hc

end GeneratedFoundations.Physical.SourceTTGaussianCoefficient
