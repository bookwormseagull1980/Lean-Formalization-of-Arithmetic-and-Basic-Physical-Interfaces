module

public import GeneratedFoundations.Arithmetic.CompleteHistoryDynamics

/-!
# Exact doubled-tilt balance on generated reaction edges

The complete history source already determines the unit-split merge rate by
detailed balance.  Tilting the same history by its internally generated
energy changes both species intensities and the edge rate.  Squaring the
tilted edge request against the un-tilted conductance recovers exactly the
intensity at doubled tilt.

This is the finite algebraic bottom-edge identity used by the shared-edge
recovery argument.  It preserves the actual generated species intensity and
does not replace it by an unweighted count.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.HistoryTiltedBalance

open GeneratedFoundations.Arithmetic.CompleteHistory
open GeneratedFoundations.Arithmetic.CompleteHistoryTransport
open GeneratedFoundations.Arithmetic.CompleteHistoryDynamics

def tiltFactor (t : ℝ) {k : ℕ} (h : History k) : ℝ :=
  Real.exp (-t * internalEnergy h)

def tiltedIntensity (alpha L t : ℝ) {k : ℕ} (h : History k) : ℝ :=
  flatGaussianIntensity alpha L h * tiltFactor t h

def tiltedMergeRate (alpha L t : ℝ) {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1) : ℝ :=
  tiltedIntensity alpha L t (.node c hl hr) /
    (tiltedIntensity alpha L t hl * tiltedIntensity alpha L t hr)

theorem flatWeight_pos {k : ℕ} (h : History k) : 0 < flatWeight h := by
  induction h with
  | one => norm_num [flatWeight]
  | node c hl hr ihl ihr =>
      exact div_pos (mul_pos ihl ihr) (channelCard_pos c)

theorem flatGaussianIntensity_pos (alpha L : ℝ) {k : ℕ} (h : History k) :
    0 < flatGaussianIntensity alpha L h :=
  mul_pos (gaussianRootMass_pos alpha L k) (flatWeight_pos h)

theorem tiltFactor_pos (t : ℝ) {k : ℕ} (h : History k) :
    0 < tiltFactor t h := Real.exp_pos _

theorem tiltedIntensity_pos (alpha L t : ℝ) {k : ℕ} (h : History k) :
    0 < tiltedIntensity alpha L t h :=
  mul_pos (flatGaussianIntensity_pos alpha L h) (tiltFactor_pos t h)

@[simp] theorem tiltFactor_zero {k : ℕ} (h : History k) :
    tiltFactor 0 h = 1 := by
  simp [tiltFactor]

theorem tiltFactor_two_mul (t : ℝ) {k : ℕ} (h : History k) :
    tiltFactor (2 * t) h = tiltFactor t h ^ 2 := by
  rw [tiltFactor, tiltFactor, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- At zero tilt the quotient of actual edge intensities is the already
generated detailed-balance merge rate. -/
theorem tiltedMergeRate_zero_eq_mergeRate (alpha L : ℝ) {k : ℕ}
    (c : Channel k) (hl : History c.left.1) (hr : History c.right.1) :
    tiltedMergeRate alpha L 0 c hl hr = mergeRate alpha L c := by
  have hl0 : flatGaussianIntensity alpha L hl ≠ 0 :=
    ne_of_gt (flatGaussianIntensity_pos alpha L hl)
  have hr0 : flatGaussianIntensity alpha L hr ≠ 0 :=
    ne_of_gt (flatGaussianIntensity_pos alpha L hr)
  rw [tiltedMergeRate, tiltedIntensity, tiltedIntensity, tiltedIntensity]
  simp only [tiltFactor_zero, mul_one]
  apply (div_eq_iff (mul_ne_zero hl0 hr0)).2
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (edge_detailed_balance alpha L c hl hr).symm

/-- Squared tilted edge demand divided by the base conductance leaves exactly
one generated product intensity at doubled tilt. -/
theorem doubled_tilt_edge_identity (alpha L t : ℝ) {k : ℕ}
    (c : Channel k) (hl : History c.left.1) (hr : History c.right.1) :
    tiltedMergeRate alpha L t c hl hr ^ 2 / mergeRate alpha L c *
        tiltedIntensity alpha L (2 * t) hl *
        tiltedIntensity alpha L (2 * t) hr =
      tiltedIntensity alpha L (2 * t) (.node c hl hr) := by
  have hleft : tiltedIntensity alpha L t hl ≠ 0 :=
    ne_of_gt (tiltedIntensity_pos alpha L t hl)
  have hright : tiltedIntensity alpha L t hr ≠ 0 :=
    ne_of_gt (tiltedIntensity_pos alpha L t hr)
  have htiltLeft : tiltFactor t hl ≠ 0 := ne_of_gt (tiltFactor_pos t hl)
  have htiltRight : tiltFactor t hr ≠ 0 := ne_of_gt (tiltFactor_pos t hr)
  have hbaseLeft : flatGaussianIntensity alpha L hl ≠ 0 :=
    ne_of_gt (flatGaussianIntensity_pos alpha L hl)
  have hbaseRight : flatGaussianIntensity alpha L hr ≠ 0 :=
    ne_of_gt (flatGaussianIntensity_pos alpha L hr)
  have hbaseParent : flatGaussianIntensity alpha L (.node c hl hr) ≠ 0 :=
    ne_of_gt (flatGaussianIntensity_pos alpha L (.node c hl hr))
  have hrate : mergeRate alpha L c ≠ 0 := ne_of_gt (mergeRate_pos alpha L c)
  simp only [tiltedMergeRate, tiltedIntensity, tiltFactor_two_mul]
  have hbalance := edge_detailed_balance alpha L c hl hr
  field_simp [hleft, hright, htiltLeft, htiltRight, hbaseLeft,
    hbaseRight, hbaseParent, hrate]
  rw [← hbalance]
  ring

structure Conclusions : Prop where
  zero_tilt_rate : ∀ (alpha L : ℝ) {k : ℕ} (c : Channel k)
      (hl : History c.left.1) (hr : History c.right.1),
    tiltedMergeRate alpha L 0 c hl hr = mergeRate alpha L c
  doubled_tilt_balance : ∀ (alpha L t : ℝ) {k : ℕ} (c : Channel k)
      (hl : History c.left.1) (hr : History c.right.1),
    tiltedMergeRate alpha L t c hl hr ^ 2 / mergeRate alpha L c *
        tiltedIntensity alpha L (2 * t) hl *
        tiltedIntensity alpha L (2 * t) hr =
      tiltedIntensity alpha L (2 * t) (.node c hl hr)

theorem historyTiltedBalanceConclusions : Conclusions where
  zero_tilt_rate := tiltedMergeRate_zero_eq_mergeRate
  doubled_tilt_balance := doubled_tilt_edge_identity

end GeneratedFoundations.Analysis.HistoryTiltedBalance
