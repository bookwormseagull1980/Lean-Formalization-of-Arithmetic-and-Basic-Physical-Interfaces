module

public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic.Linarith

/-!
# Nonnegative additive functions on the positive half-line

The single theorem in this module records the rigidity shared by generated
variance and local information. Nonnegativity makes an additive half-line map
monotone. Its real additive extension is then Borel measurable, hence
continuous and real-linear.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace GeneratedFoundations.Analysis.NonnegativeAdditive

/-- A nonnegative additive real-valued function on `ℝ≥0` is multiplication by
its value at one. No continuity or measurability assumption is required. -/
theorem eq_mul_one (H : ℝ≥0 → ℝ) (hn : ∀ x, 0 ≤ H x)
    (ha : ∀ x y, H (x + y) = H x + H y) (x : ℝ≥0) :
    H x = (x : ℝ) * H 1 := by
  have hzero : H 0 = 0 := by
    have h := ha 0 0
    simp only [add_zero] at h
    linarith
  let extension : ℝ →+ ℝ :=
    { toFun := fun t => H t.toNNReal - H (-t).toNNReal
      map_zero' := by simp [hzero]
      map_add' := by
        intro a b
        have hparts :
            a.toNNReal + b.toNNReal + (-(a + b)).toNNReal =
              (a + b).toNNReal + (-a).toNNReal + (-b).toNNReal := by
          apply NNReal.eq
          simp only [NNReal.coe_add, Real.coe_toNNReal']
          linarith [max_zero_sub_max_neg_zero_eq_self a,
            max_zero_sub_max_neg_zero_eq_self b,
            max_zero_sub_max_neg_zero_eq_self (a + b)]
        have hh := congrArg H hparts
        simp only [ha] at hh
        linarith }
  have hmono : Monotone H := by
    intro a b hab
    have hsum : a + (b - a) = b := by
      simpa [add_comm] using tsub_add_cancel_of_le hab
    calc
      H a ≤ H a + H (b - a) := le_add_of_nonneg_right (hn _)
      _ = H b := by rw [← ha, hsum]
  have he_meas : Measurable extension := by
    exact (hmono.measurable.comp measurable_real_toNNReal).sub
      (hmono.measurable.comp (measurable_real_toNNReal.comp measurable_neg))
  have he : Continuous extension :=
    MeasureTheory.Measure.AddMonoidHom.continuous_of_measurable extension he_meas
  have hx : Real.toNNReal (-(x : ℝ)) = 0 :=
    Real.toNNReal_of_nonpos (neg_nonpos.mpr x.property)
  have h1 : Real.toNNReal (-1) = 0 := Real.toNNReal_of_nonpos (by norm_num)
  have hl := map_real_smul extension he (x : ℝ) (1 : ℝ)
  simpa [extension, smul_eq_mul, Real.toNNReal_coe, hx, h1, hzero] using hl

end GeneratedFoundations.Analysis.NonnegativeAdditive
