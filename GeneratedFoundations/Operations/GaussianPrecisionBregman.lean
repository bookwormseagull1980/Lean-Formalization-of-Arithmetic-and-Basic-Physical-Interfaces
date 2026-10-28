module

public import GeneratedFoundations.Operations.GaussianPrecisionKL

/-!
# Exact comparison between two Gaussian precision variations

The tangent remainder of the compensated log comparison is another full
precision comparison. It is twice the relative entropy of the two actual
Gaussian laws. No quadratic replacement of the logarithm is involved.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace GeneratedFoundations.Operations.ScalarPrecisionComparison

def betweenCost (r z v : ℝ) : ℝ := cost (r / (1 + z * r)) (v - z)

theorem between_relative_precision {r z v : ℝ} (hz : 1 + z * r ≠ 0) :
    1 + (v - z) * (r / (1 + z * r)) = (1 + v * r) / (1 + z * r) := by
  field_simp
  ring

theorem betweenCost_eq {r z v : ℝ} (hz : 0 < 1 + z * r)
    (hv : 0 < 1 + v * r) :
    betweenCost r z v = cost r v - cost r z - force r z * (v - z) := by
  unfold betweenCost cost
  rw [between_relative_precision hz.ne', Real.log_div hv.ne' hz.ne']
  unfold force
  ring

theorem betweenCost_nonneg {r z v : ℝ} (hz : 0 < 1 + z * r)
    (hv : 0 < 1 + v * r) : 0 ≤ betweenCost r z v := by
  exact cost_nonneg _ _ (by
    rw [between_relative_precision hz.ne']
    exact div_pos hv hz)

theorem cost_pos {r z : ℝ} (h : 0 < 1 + z * r) (hne : z * r ≠ 0) :
    0 < cost r z := by
  have hl := Real.log_lt_sub_one_of_pos h (by intro hh; apply hne; linarith)
  unfold cost
  linarith

theorem betweenCost_pos {r z v : ℝ} (hr : 0 < r) (hz : 0 < 1 + z * r)
    (hv : 0 < 1 + v * r) (hne : v ≠ z) : 0 < betweenCost r z v := by
  apply cost_pos
  · rw [between_relative_precision hz.ne']
    exact div_pos hv hz
  · exact mul_ne_zero (sub_ne_zero.mpr hne) (div_ne_zero hr.ne' hz.ne')

@[simp] theorem betweenCost_self (r z : ℝ) : betweenCost r z z = 0 := by
  simp [betweenCost]

@[simp] theorem betweenCost_zero_left (r v : ℝ) : betweenCost r 0 v = cost r v := by
  simp [betweenCost]

theorem cost_add_reverse {r z : ℝ} (hz : 0 < 1 + z * r) :
    cost r z + betweenCost r z 0 = z * force r z := by
  rw [betweenCost_eq hz (by norm_num), cost_zero]
  ring

end GeneratedFoundations.Operations.ScalarPrecisionComparison

namespace GeneratedFoundations.Operations.GaussianPrecisionKL

theorem between_varied_precisions {p k z v : ℝ} (hp : 0 < p)
    (hz : 0 < p + z * k) (hv : 0 < p + v * k) :
    (InformationTheory.klDiv (law (p + z * k)) (law (p + v * k))).toReal =
      ScalarPrecisionComparison.betweenCost (k / p) z v / 2 := by
  have hnext : p + z * k + (v - z) * k = p + v * k := by ring
  have he := varied_precision (p := p + z * k) (k := k) (z := v - z) hz
    (by rw [hnext]; exact hv)
  rw [hnext] at he
  rw [he]
  congr 2
  field_simp [hp.ne', hz.ne']

end GeneratedFoundations.Operations.GaussianPrecisionKL
