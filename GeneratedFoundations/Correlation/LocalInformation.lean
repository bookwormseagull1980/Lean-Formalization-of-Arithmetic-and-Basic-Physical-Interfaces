module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Group.MinMax
public import GeneratedFoundations.Analysis.NonnegativeAdditive
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
Nonnegative multiplicatively additive local information on `(0, 1]`.
Nonnegativity makes the associated additive half-line map monotone, so
continuity and the logarithmic form are conclusions rather than assumptions.
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

structure AdditiveLocalInformation (F : CorrelationLevel → ℝ) : Prop where
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

theorem continuous : Continuous F := by
  have hlinear : ∀ x : ℝ≥0,
      F (expNeg x) = (x : ℝ) * F (expNeg 1) :=
    Analysis.NonnegativeAdditive.eq_mul_one (fun t => F (expNeg t))
      (fun t => hF.nonnegative _) (fun a b => by rw [expNeg_add, hF.additive])
  have hrepr : F = fun r : CorrelationLevel =>
      -(F (expNeg 1)) * Real.log (r : ℝ) := by
    funext r
    let x : ℝ≥0 := ⟨-Real.log (r : ℝ),
      neg_nonneg.mpr (Real.log_nonpos r.property.1.le r.property.2)⟩
    have hx : expNeg x = r := by
      apply Subtype.ext
      change Real.exp (- -Real.log (r : ℝ)) = (r : ℝ)
      rw [neg_neg, Real.exp_log r.property.1]
    have hl := hlinear x
    rw [hx] at hl
    calc
      F r = (-Real.log (r : ℝ)) * F (expNeg 1) := hl
      _ = -(F (expNeg 1)) * Real.log (r : ℝ) := by ring
  rw [hrepr]
  exact continuous_const.mul
    (continuous_subtype_val.log (fun r : CorrelationLevel => r.property.1.ne'))

theorem eq_neg_log_scale (r : CorrelationLevel) :
    F r = -(F (expNeg 1)) * Real.log (r : ℝ) := by
  let x : ℝ≥0 := ⟨-Real.log (r : ℝ),
    neg_nonneg.mpr (Real.log_nonpos r.property.1.le r.property.2)⟩
  have hx : expNeg x = r := by
    apply Subtype.ext
    change Real.exp (- -Real.log (r : ℝ)) = (r : ℝ)
    rw [neg_neg, Real.exp_log r.property.1]
  have hlinear := Analysis.NonnegativeAdditive.eq_mul_one (fun t => F (expNeg t))
    (fun t => hF.nonnegative _)
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
