module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Continuous multiplicatively additive local information on `(0, 1]`.
The logarithmic form is derived before imposing the unit calibration.
-/

@[expose] public section

noncomputable section

open scoped NNReal

namespace GeneratedFoundations.Correlation.LocalInformation

abbrev CorrelationLevel := Set.Ioc (0 : ℝ) 1

def unitLevel : CorrelationLevel := ⟨1, by norm_num⟩

def levelMul (r s : CorrelationLevel) : CorrelationLevel :=
  ⟨(r : ℝ) * (s : ℝ), mul_pos r.property.1 s.property.1,
    calc
      (r : ℝ) * (s : ℝ) ≤ 1 * 1 :=
        mul_le_mul r.property.2 s.property.2 s.property.1.le (by norm_num)
      _ = 1 := by norm_num⟩

def expNeg (x : ℝ≥0) : CorrelationLevel :=
  ⟨Real.exp (-(x : ℝ)), Real.exp_pos _,
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr x.property)⟩

theorem continuous_expNeg : Continuous expNeg := by
  exact (Real.continuous_exp.comp continuous_subtype_val.neg).subtype_mk _

theorem expNeg_zero : expNeg 0 = unitLevel := by
  apply Subtype.ext
  simp [expNeg, unitLevel]

theorem expNeg_add (x y : ℝ≥0) :
    expNeg (x + y) = levelMul (expNeg x) (expNeg y) := by
  apply Subtype.ext
  simp [expNeg, levelMul, Real.exp_add, mul_comm]

/-- The real additive extension supplies the half-line linearity step. -/
theorem continuous_additive_nnreal (H : ℝ≥0 → ℝ) (hc : Continuous H)
    (ha : ∀ x y, H (x + y) = H x + H y) (x : ℝ≥0) :
    H x = (x : ℝ) * H 1 := by
  have hzero : H 0 = 0 := by
    have h := ha 0 0
    simp only [add_zero] at h
    linarith
  let extension : ℝ →+ ℝ :=
    { toFun := fun t => H t.toNNReal - H (-t).toNNReal
      map_zero' := by simp
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
  have he : Continuous extension :=
    (hc.comp continuous_real_toNNReal).sub
      (hc.comp (continuous_real_toNNReal.comp continuous_neg))
  have hx : Real.toNNReal (-(x : ℝ)) = 0 :=
    Real.toNNReal_of_nonpos (neg_nonpos.mpr x.property)
  have h1 : Real.toNNReal (-1) = 0 := Real.toNNReal_of_nonpos (by norm_num)
  have hl := map_real_smul extension he (x : ℝ) (1 : ℝ)
  simpa [extension, smul_eq_mul, Real.toNNReal_coe, hx, h1, hzero] using hl

structure AdditiveLocalInformation (F : CorrelationLevel → ℝ) : Prop where
  continuous : Continuous F
  nonnegative : ∀ r, 0 ≤ F r
  additive : ∀ r s, F (levelMul r s) = F r + F s

namespace AdditiveLocalInformation

variable {F : CorrelationLevel → ℝ} (hF : AdditiveLocalInformation F)

include hF

theorem value_at_unit : F unitLevel = 0 := by
  have hunit : levelMul unitLevel unitLevel = unitLevel := by
    apply Subtype.ext
    norm_num [levelMul, unitLevel]
  have h := hF.additive unitLevel unitLevel
  rw [hunit] at h
  linarith

theorem eq_neg_log_scale (r : CorrelationLevel) :
    F r = -(F (expNeg 1)) * Real.log (r : ℝ) := by
  let x : ℝ≥0 := ⟨-Real.log (r : ℝ),
    neg_nonneg.mpr (Real.log_nonpos r.property.1.le r.property.2)⟩
  have hx : expNeg x = r := by
    apply Subtype.ext
    change Real.exp (- -Real.log (r : ℝ)) = (r : ℝ)
    rw [neg_neg, Real.exp_log r.property.1]
  have hlinear := continuous_additive_nnreal (fun t => F (expNeg t))
    (hF.continuous.comp continuous_expNeg)
    (fun a b => by rw [expNeg_add, hF.additive]) x
  rw [hx] at hlinear
  calc
    F r = (-Real.log (r : ℝ)) * F (expNeg 1) := hlinear
    _ = -(F (expNeg 1)) * Real.log (r : ℝ) := by ring

theorem existsUnique_nonnegative_coefficient :
    ∃! c : ℝ, 0 ≤ c ∧ ∀ r : CorrelationLevel, F r = -c * Real.log (r : ℝ) := by
  refine ⟨F (expNeg 1), ⟨hF.nonnegative _, hF.eq_neg_log_scale⟩, ?_⟩
  intro c hc
  have h := hc.2 (expNeg 1)
  simp [expNeg, Real.log_exp] at h
  exact h.symm

theorem coefficient_pos_of_detectable (hd : ∃ r : CorrelationLevel, 0 < F r) :
    0 < F (expNeg 1) := by
  by_contra hnot
  have hz : F (expNeg 1) = 0 :=
    le_antisymm (le_of_not_gt hnot) (hF.nonnegative _)
  obtain ⟨r, hr⟩ := hd
  rw [hF.eq_neg_log_scale r, hz] at hr
  norm_num at hr

theorem eq_neg_log_of_calibration (hcal : F (expNeg 1) = 1)
    (r : CorrelationLevel) : F r = -Real.log (r : ℝ) := by
  rw [hF.eq_neg_log_scale, hcal]
  ring

end AdditiveLocalInformation

def negativeLog (r : CorrelationLevel) : ℝ := -Real.log (r : ℝ)

theorem negativeLog_axioms : AdditiveLocalInformation negativeLog where
  continuous := (continuous_subtype_val.log (fun r => r.property.1.ne')).neg
  nonnegative r := neg_nonneg.mpr (Real.log_nonpos r.property.1.le r.property.2)
  additive r s := by
    dsimp [negativeLog, levelMul]
    rw [Real.log_mul r.property.1.ne' s.property.1.ne']
    ring

theorem negativeLog_calibration : negativeLog (expNeg 1) = 1 := by
  simp [negativeLog, expNeg, Real.log_exp]

theorem calibrated_existsUnique :
    ∃! F : CorrelationLevel → ℝ,
      AdditiveLocalInformation F ∧ F (expNeg 1) = 1 := by
  refine ⟨negativeLog, ⟨negativeLog_axioms, negativeLog_calibration⟩, ?_⟩
  intro F hF
  funext r
  exact hF.1.eq_neg_log_of_calibration hF.2 r

end GeneratedFoundations.Correlation.LocalInformation
