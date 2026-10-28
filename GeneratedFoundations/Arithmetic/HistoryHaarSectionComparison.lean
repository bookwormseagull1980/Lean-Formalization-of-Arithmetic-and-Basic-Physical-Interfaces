module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionWindow
public import GeneratedFoundations.Operations.ScalarPrecisionComparison

/-!
# Variational origin of the complete history spectral response

For each eigenvector of the actual joint Hessian, the precision is varied
along its own kinetic coefficient. The compensated log comparison is formed
on the entire finite spectral window, with the original Gaussian weight.
Its exact second variation is the complete response trace. In particular,
the resolvent-squared kernel is obtained by differentiation rather than
introduced as an independently chosen response equation.

The cutoff is held fixed in this comparison variation. Selecting a cutoff
also requires the actual source-content and spectral-shell conditions.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open Set Filter

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionComparison

open HistoryHaarSectionWindow
open HistoryHaarSectionJointHessian (Index eigenvalue)
open Operations.ScalarPrecisionComparison

def kineticPrecision (N : ℕ) (i : Index N) (u : ℝ) : ℝ := u ^ 2 + kinetic N i

def precision (N : ℕ) (i : Index N) (u : ℝ) : ℝ := u ^ 2 + eigenvalue N i

def kineticFraction (N : ℕ) (i : Index N) (u : ℝ) : ℝ :=
  kineticPrecision N i u / precision N i u

def weight (N : ℕ) (i : Index N) (u : ℝ) : ℝ :=
  Real.exp (-kineticPrecision N i u)

theorem precision_pos (N : ℕ) (i : Index N) (u : ℝ) : 0 < precision N i u := by
  have he := HistoryHaarSectionJointHessian.eigenvalue_lower N i
  unfold precision
  nlinarith [sq_nonneg u]

theorem kineticFraction_nonneg (N : ℕ) (i : Index N) (u : ℝ) :
    0 ≤ kineticFraction N i u :=
  div_nonneg (add_nonneg (sq_nonneg u) (kinetic_nonneg N i)) (precision_pos N i u).le

theorem kineticFraction_le_one (N : ℕ) (i : Index N) (u : ℝ) :
    kineticFraction N i u ≤ 1 := by
  rw [kineticFraction, div_le_one (precision_pos N i u)]
  unfold kineticPrecision precision
  rw [source_response_decomposition]
  linarith [restoring_nonneg N i]

theorem kineticFraction_continuous (N : ℕ) (i : Index N) :
    Continuous (kineticFraction N i) := by
  exact ((continuous_id.pow 2).add continuous_const).div
    ((continuous_id.pow 2).add continuous_const) (fun u => (precision_pos N i u).ne')

theorem weight_pos (N : ℕ) (i : Index N) (u : ℝ) : 0 < weight N i u := Real.exp_pos _

theorem weight_le_one (N : ℕ) (i : Index N) (u : ℝ) : weight N i u ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  unfold kineticPrecision
  linarith [sq_nonneg u, kinetic_nonneg N i]

theorem weight_continuous (N : ℕ) (i : Index N) : Continuous (weight N i) := by
  unfold weight kineticPrecision
  fun_prop

theorem actual_relative_precision (N : ℕ) (i : Index N) (u z : ℝ) :
    (precision N i u + z * kineticPrecision N i u) / precision N i u =
      1 + z * kineticFraction N i u :=
  relative_precision (precision_pos N i u).ne' _ _

theorem kernel_eq_comparison_curvature (N : ℕ) (i : Index N) (u : ℝ) :
    kernel N i u = weight N i u * curvature (kineticFraction N i u) 0 := by
  simp only [curvature_zero, kernel, weight, kineticFraction, kineticPrecision, precision]
  ring

def branchComparison (N : ℕ) (B : ℝ) (i : Index N) (z : ℝ) : ℝ :=
  comparisonIntegral (kineticFraction N i) (weight N i)
    0 (Real.sqrt (B - kinetic N i)) z

def branchForce (N : ℕ) (B : ℝ) (i : Index N) (z : ℝ) : ℝ :=
  forceIntegral (kineticFraction N i) (weight N i)
    0 (Real.sqrt (B - kinetic N i)) z

theorem branchComparison_hasDerivAt (N : ℕ) (B : ℝ) (i : Index N)
    {z : ℝ} (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (branchComparison N B i) (branchForce N B i z) z :=
  comparisonIntegral_hasDerivAt _ _ _ _ (kineticFraction_continuous N i)
    (weight_continuous N i) (kineticFraction_nonneg N i) (kineticFraction_le_one N i)
    (fun u => (weight_pos N i u).le) (weight_le_one N i) hz

theorem branchForce_hasDerivAt_zero (N : ℕ) (B : ℝ) (i : Index N) :
    HasDerivAt (branchForce N B i) (branchIntegral N B i) 0 := by
  have h := forceIntegral_hasDerivAt_zero (kineticFraction N i) (weight N i)
    0 (Real.sqrt (B - kinetic N i)) (kineticFraction_continuous N i)
    (weight_continuous N i) (kineticFraction_nonneg N i) (kineticFraction_le_one N i)
    (fun u => (weight_pos N i u).le) (weight_le_one N i)
  convert! h using 1
  unfold branchIntegral
  apply intervalIntegral.integral_congr
  intro u _
  simpa only [curvature_zero] using kernel_eq_comparison_curvature N i u

theorem branchComparison_secondDeriv_zero (N : ℕ) (B : ℝ) (i : Index N) :
    HasDerivAt (fun z => deriv (branchComparison N B i) z) (branchIntegral N B i) 0 := by
  apply (branchForce_hasDerivAt_zero N B i).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  exact (branchComparison_hasDerivAt N B i hz).deriv

def comparison (N : ℕ) (B z : ℝ) : ℝ :=
  ∑ i ∈ support N B, branchComparison N B i z

def completeForce (N : ℕ) (B z : ℝ) : ℝ :=
  ∑ i ∈ support N B, branchForce N B i z

@[simp] theorem comparison_zero (N : ℕ) (B : ℝ) : comparison N B 0 = 0 := by
  simp [comparison, branchComparison, comparisonIntegral]

@[simp] theorem completeForce_zero (N : ℕ) (B : ℝ) : completeForce N B 0 = 0 := by
  simp [completeForce, branchForce, forceIntegral]

theorem comparison_hasDerivAt (N : ℕ) (B : ℝ)
    {z : ℝ} (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (comparison N B) (completeForce N B z) z := by
  classical
  exact HasDerivAt.fun_sum (fun i _ => branchComparison_hasDerivAt N B i hz)

theorem completeForce_hasDerivAt_zero (N : ℕ) (B : ℝ) :
    HasDerivAt (completeForce N B) (responseTrace N B) 0 := by
  classical
  exact HasDerivAt.fun_sum (fun i _ => branchForce_hasDerivAt_zero N B i)

theorem comparison_secondDeriv_zero (N : ℕ) (B : ℝ) :
    HasDerivAt (fun z => deriv (comparison N B) z) (responseTrace N B) 0 := by
  apply (completeForce_hasDerivAt_zero N B).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  exact (comparison_hasDerivAt N B hz).deriv

theorem comparison_curvature_pos (N : ℕ) (B : ℝ) (h : (support N B).Nonempty) :
    0 < deriv (fun z => deriv (comparison N B) z) 0 := by
  rw [(comparison_secondDeriv_zero N B).deriv]
  exact responseTrace_pos N B h

structure Conclusions : Prop where
  actual_precision : ∀ N i u z,
    (precision N i u + z * kineticPrecision N i u) / precision N i u =
      1 + z * kineticFraction N i u
  complete_variation : ∀ N B,
    HasDerivAt (fun z => deriv (comparison N B) z) (responseTrace N B) 0
  positive_curvature : ∀ N B, (support N B).Nonempty →
    0 < deriv (fun z => deriv (comparison N B) z) 0

theorem generated : Conclusions where
  actual_precision := actual_relative_precision
  complete_variation := comparison_secondDeriv_zero
  positive_curvature := comparison_curvature_pos

end GeneratedFoundations.Arithmetic.HistoryHaarSectionComparison
