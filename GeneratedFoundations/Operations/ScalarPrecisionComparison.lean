module

public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Second variation of a common precision comparison

The precision is varied in its actual kinetic direction. If its unperturbed
value is `p` and that direction is `q`, the relative precision is
`1 + z * (q / p)`. The compensated log comparison is evaluated before taking
its two derivatives. The finite trace identity and differentiation under
the Gaussian-weighted integral retain every coordinate of the chosen window.
The window is fixed during this variation; a change of cutoff is a different
variation with its own boundary terms.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Operations.ScalarPrecisionComparison

def cost (r z : ℝ) : ℝ := z * r - Real.log (1 + z * r)

def force (r z : ℝ) : ℝ := r - r / (1 + z * r)

def curvature (r z : ℝ) : ℝ := r ^ 2 / (1 + z * r) ^ 2

theorem cost_hasDerivAt (r z : ℝ) (h : 1 + z * r ≠ 0) :
    HasDerivAt (cost r) (force r z) z := by
  convert! ((hasDerivAt_id z).mul_const r).sub
    ((((hasDerivAt_id z).mul_const r).const_add 1).log h) using 1
  simp only [force, id_eq, one_mul]

theorem force_hasDerivAt (r z : ℝ) (h : 1 + z * r ≠ 0) :
    HasDerivAt (force r) (curvature r z) z := by
  have hd := (hasDerivAt_const z r).sub
    ((hasDerivAt_const z r).div
      (((hasDerivAt_id z).mul_const r).const_add 1) h)
  convert hd using 1
  · rfl
  · dsimp [curvature]
    ring

@[simp] theorem cost_zero (r : ℝ) : cost r 0 = 0 := by simp [cost]

@[simp] theorem force_zero (r : ℝ) : force r 0 = 0 := by simp [force]

@[simp] theorem curvature_zero (r : ℝ) : curvature r 0 = r ^ 2 := by
  simp [curvature]

theorem cost_nonneg (r z : ℝ) (h : 0 < 1 + z * r) : 0 ≤ cost r z := by
  have hl := Real.log_le_sub_one_of_pos h
  unfold cost
  linarith

theorem relative_precision {p : ℝ} (hp : p ≠ 0) (q z : ℝ) :
    (p + z * q) / p = 1 + z * (q / p) := by field_simp

theorem finite_trace_logdet {ι : Type*} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ) (z : ℝ) (h : ∀ i, 1 + z * r i ≠ 0) :
    (∑ i, cost (r i) z) =
      Matrix.trace (Matrix.diagonal (fun i => z * r i)) -
        Real.log (Matrix.det (Matrix.diagonal (fun i => 1 + z * r i))) := by
  rw [Matrix.trace_diagonal, Matrix.det_diagonal, Real.log_prod (fun i _ => h i)]
  simp only [cost, Finset.sum_sub_distrib]

theorem local_precision_lower {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : (1 / 2 : ℝ) < 1 + z * r := by
  have hm : -(1 / 2 : ℝ) < z * r := by
    by_cases h : 0 ≤ z
    · have := mul_nonneg h hr; linarith
    · have : z ≤ z * r := by nlinarith
      linarith [hz.1]
  linarith

theorem local_force_bound {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : |force r z| ≤ 3 := by
  have hp := local_precision_lower hr hr1 hz
  have hd : 0 ≤ r / (1 + z * r) := div_nonneg hr (by linarith)
  have hu : r / (1 + z * r) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  rw [force, abs_le]
  constructor <;> linarith

theorem local_curvature_bound {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : |curvature r z| ≤ 4 := by
  have hp := local_precision_lower hr hr1 hz
  have hd : 0 < (1 + z * r) ^ 2 := sq_pos_of_pos (by linarith)
  rw [curvature, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply (div_le_iff₀ hd).mpr
  nlinarith [sq_nonneg r]

def comparisonIntegral (r w : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  ∫ u in a..b, w u * cost (r u) z

def forceIntegral (r w : ℝ → ℝ) (a b z : ℝ) : ℝ :=
  ∫ u in a..b, w u * force (r u) z

theorem comparisonIntegral_hasDerivAt (r w : ℝ → ℝ) (a b : ℝ)
    (hr : Continuous r) (hw : Continuous w)
    (hr0 : ∀ u, 0 ≤ r u) (hr1 : ∀ u, r u ≤ 1)
    (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1)
    {z : ℝ} (hz : z ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
    HasDerivAt (comparisonIntegral r w a b) (forceIntegral r w a b z) z := by
  have hp (x : ℝ) (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) (u : ℝ) :
      1 + x * r u ≠ 0 := ne_of_gt (lt_trans (by norm_num)
        (local_precision_lower (hr0 u) (hr1 u) hx))
  have hc (x : ℝ) (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
      Continuous (fun u => w u * cost (r u) x) := by
    unfold cost
    exact hw.mul ((continuous_const.mul hr).sub
      ((continuous_const.add (continuous_const.mul hr)).log (hp x hx)))
  have hf (x : ℝ) (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
      Continuous (fun u => w u * force (r u) x) := by
    unfold force
    exact hw.mul (hr.sub (hr.div (continuous_const.add (continuous_const.mul hr)) (hp x hx)))
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := fun _ => (3 : ℝ))
    (Ioo_mem_nhds hz.1 hz.2)
    (by filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx
        exact (hc x hx).aestronglyMeasurable)
    ((hc z hz).intervalIntegrable a b) (hf z hz).aestronglyMeasurable
    (ae_of_all _ fun u _ x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u)]
      exact le_trans (mul_le_mul_of_nonneg_left
        (local_force_bound (hr0 u) (hr1 u) hx) (hw0 u)) (by nlinarith [hw1 u]))
    intervalIntegrable_const
    (ae_of_all _ fun u _ x hx => (cost_hasDerivAt (r u) x (hp x hx u)).const_mul (w u))).2

theorem forceIntegral_hasDerivAt_zero (r w : ℝ → ℝ) (a b : ℝ)
    (hr : Continuous r) (hw : Continuous w)
    (hr0 : ∀ u, 0 ≤ r u) (hr1 : ∀ u, r u ≤ 1)
    (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1) :
    HasDerivAt (forceIntegral r w a b)
      (∫ u in a..b, w u * (r u) ^ 2) 0 := by
  have hz : (0 : ℝ) ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2) := by constructor <;> norm_num
  have hp (x : ℝ) (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) (u : ℝ) :
      1 + x * r u ≠ 0 := ne_of_gt (lt_trans (by norm_num)
        (local_precision_lower (hr0 u) (hr1 u) hx))
  have hc (x : ℝ) (hx : x ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) :
      Continuous (fun u => w u * force (r u) x) := by
    unfold force
    exact hw.mul (hr.sub (hr.div (continuous_const.add (continuous_const.mul hr)) (hp x hx)))
  have hcc : Continuous (fun u => w u * curvature (r u) 0) := by
    convert! hw.mul (hr.pow 2) using 1
    funext u
    simp only [curvature_zero, Pi.mul_apply, Pi.pow_apply]
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := fun _ => (4 : ℝ)) (Ioo_mem_nhds hz.1 hz.2)
    (by filter_upwards [Ioo_mem_nhds hz.1 hz.2] with x hx
        exact (hc x hx).aestronglyMeasurable)
    ((hc 0 hz).intervalIntegrable a b) hcc.aestronglyMeasurable
    (ae_of_all _ fun u _ x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u)]
      exact le_trans (mul_le_mul_of_nonneg_left
        (local_curvature_bound (hr0 u) (hr1 u) hx) (hw0 u)) (by nlinarith [hw1 u]))
    intervalIntegrable_const
    (ae_of_all _ fun u _ x hx => (force_hasDerivAt (r u) x (hp x hx u)).const_mul (w u))).2
  convert! hd using 1
  simp only [curvature_zero]

theorem comparisonIntegral_secondDeriv_zero (r w : ℝ → ℝ) (a b : ℝ)
    (hr : Continuous r) (hw : Continuous w)
    (hr0 : ∀ u, 0 ≤ r u) (hr1 : ∀ u, r u ≤ 1)
    (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1) :
    HasDerivAt (fun z => deriv (comparisonIntegral r w a b) z)
      (∫ u in a..b, w u * (r u) ^ 2) 0 := by
  apply (forceIntegral_hasDerivAt_zero r w a b hr hw hr0 hr1 hw0 hw1).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (by norm_num : -(1 / 2 : ℝ) < 0)
    (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
  exact (comparisonIntegral_hasDerivAt r w a b hr hw hr0 hr1 hw0 hw1 hz).deriv

end GeneratedFoundations.Operations.ScalarPrecisionComparison
