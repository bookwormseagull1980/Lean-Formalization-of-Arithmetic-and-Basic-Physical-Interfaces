module

public import GeneratedFoundations.Operations.ScalarPrecisionComparison

/-!
# Gaussian precision comparison on the whole positive perturbation ray

Positive kinetic perturbations keep the original precision positive. The
fixed-window comparison therefore has no upper restriction z < 1/2.
These derivatives use the same exact logarithmic cost and force; only the
artificial upper bound of the earlier local comparison is removed.
-/

@[expose] public section
noncomputable section
open scoped BigOperators Topology
open MeasureTheory Set Filter
set_option backward.isDefEq.respectTransparency false
namespace GeneratedFoundations.Operations.ScalarPrecisionComparison

theorem positive_precision_lower {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ Ioi (-(1 / 2 : ℝ))) : (1 / 2 : ℝ) < 1 + z * r := by
  change -(1 / 2 : ℝ) < z at hz
  have hm : -(1 / 2 : ℝ) < z * r := by
    by_cases h : 0 ≤ z
    · have := mul_nonneg h hr; linarith
    · have : z ≤ z * r := by nlinarith
      linarith [hz]
  linarith

theorem positive_force_bound {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ Ioi (-(1 / 2 : ℝ))) : |force r z| ≤ 3 := by
  have hp := positive_precision_lower hr hr1 hz
  have hd : 0 ≤ r / (1 + z * r) := div_nonneg hr (by linarith)
  have hu : r / (1 + z * r) ≤ 2 := (div_le_iff₀ (by linarith)).mpr (by linarith)
  rw [force, abs_le]
  constructor <;> linarith

theorem positive_curvature_bound {r z : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hz : z ∈ Ioi (-(1 / 2 : ℝ))) : |curvature r z| ≤ 4 := by
  have hp := positive_precision_lower hr hr1 hz
  have hd : 0 < (1 + z * r) ^ 2 := sq_pos_of_pos (by linarith)
  rw [curvature, abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
  apply (div_le_iff₀ hd).mpr
  nlinarith [sq_nonneg r]

theorem positive_comparisonIntegral_hasDerivAt (r w : ℝ → ℝ) (a b : ℝ)
    (hr : Continuous r) (hw : Continuous w)
    (hr0 : ∀ u, 0 ≤ r u) (hr1 : ∀ u, r u ≤ 1)
    (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1)
    {z : ℝ} (hz : z ∈ Ioi (-(1 / 2 : ℝ))) :
    HasDerivAt (comparisonIntegral r w a b) (forceIntegral r w a b z) z := by
  have hp (x : ℝ) (hx : x ∈ Ioi (-(1 / 2 : ℝ))) (u : ℝ) :
      1 + x * r u ≠ 0 := ne_of_gt (lt_trans (by norm_num)
        (positive_precision_lower (hr0 u) (hr1 u) hx))
  have hc (x : ℝ) (hx : x ∈ Ioi (-(1 / 2 : ℝ))) :
      Continuous (fun u => w u * cost (r u) x) := by
    unfold cost
    exact hw.mul ((continuous_const.mul hr).sub
      ((continuous_const.add (continuous_const.mul hr)).log (hp x hx)))
  have hf (x : ℝ) (hx : x ∈ Ioi (-(1 / 2 : ℝ))) :
      Continuous (fun u => w u * force (r u) x) := by
    unfold force
    exact hw.mul (hr.sub (hr.div (continuous_const.add (continuous_const.mul hr)) (hp x hx)))
  exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := fun _ => (3 : ℝ))
    (isOpen_Ioi.mem_nhds hz)
    (by filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
        exact (hc x hx).aestronglyMeasurable)
    ((hc z hz).intervalIntegrable a b) (hf z hz).aestronglyMeasurable
    (ae_of_all _ fun u _ x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u)]
      exact le_trans (mul_le_mul_of_nonneg_left
        (positive_force_bound (hr0 u) (hr1 u) hx) (hw0 u)) (by nlinarith [hw1 u]))
    intervalIntegrable_const
    (ae_of_all _ fun u _ x hx => (cost_hasDerivAt (r u) x (hp x hx u)).const_mul (w u))).2


theorem positive_forceIntegral_hasDerivAt (r w : ℝ → ℝ) (a b : ℝ)
    (hr : Continuous r) (hw : Continuous w)
    (hr0 : ∀ u, 0 ≤ r u) (hr1 : ∀ u, r u ≤ 1)
    (hw0 : ∀ u, 0 ≤ w u) (hw1 : ∀ u, w u ≤ 1)
    {z : ℝ} (hz : z ∈ Ioi (-(1 / 2 : ℝ))) :
    HasDerivAt (forceIntegral r w a b)
      (∫ u in a..b, w u * curvature (r u) z) z := by
  have hp (x : ℝ) (hx : x ∈ Ioi (-(1 / 2 : ℝ))) (u : ℝ) :
      1 + x * r u ≠ 0 := ne_of_gt (lt_trans (by norm_num)
        (positive_precision_lower (hr0 u) (hr1 u) hx))
  have hc (x : ℝ) (hx : x ∈ Ioi (-(1 / 2 : ℝ))) :
      Continuous (fun u => w u * force (r u) x) := by
    unfold force
    exact hw.mul (hr.sub (hr.div (continuous_const.add (continuous_const.mul hr)) (hp x hx)))
  have hcc : Continuous (fun u => w u * curvature (r u) z) := by
    unfold curvature
    exact hw.mul ((hr.pow 2).div
      ((continuous_const.add (continuous_const.mul hr)).pow 2)
      (fun u => pow_ne_zero 2 (hp z hz u)))
  have hd := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (bound := fun _ => (4 : ℝ)) (isOpen_Ioi.mem_nhds hz)
    (by filter_upwards [isOpen_Ioi.mem_nhds hz] with x hx
        exact (hc x hx).aestronglyMeasurable)
    ((hc z hz).intervalIntegrable a b) hcc.aestronglyMeasurable
    (ae_of_all _ fun u _ x hx => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw0 u)]
      exact le_trans (mul_le_mul_of_nonneg_left
        (positive_curvature_bound (hr0 u) (hr1 u) hx) (hw0 u)) (by nlinarith [hw1 u]))
    intervalIntegrable_const
    (ae_of_all _ fun u _ x hx => (force_hasDerivAt (r u) x (hp x hx u)).const_mul (w u))).2
  exact hd

end GeneratedFoundations.Operations.ScalarPrecisionComparison
