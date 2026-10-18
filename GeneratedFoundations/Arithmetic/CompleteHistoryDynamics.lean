module

public import GeneratedFoundations.Arithmetic.CompleteHistoryTransport

/-!
# Detailed-balance dynamics of the complete positive source

The flat history law and the Gaussian root mass determine the forward merge
rate once the reverse split rate is calibrated to one.  This module records
that determination edge by edge.  It is a dynamics on the already generated
histories, not an additional rule for constructing the natural-number
semiring.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.CompleteHistoryDynamics

open GeneratedFoundations.Arithmetic.CompleteHistory

/-- Forward rate forced by the complete Gaussian source and unit reverse
split rate. -/
def mergeRate (alpha L : ℝ) {k : ℕ} (c : Channel k) : ℝ :=
  gaussianRootMass alpha L k /
    (gaussianRootMass alpha L c.left.1 *
      gaussianRootMass alpha L c.right.1 *
      (Fintype.card (Channel k) : ℝ))

theorem channelCard_pos {k : ℕ} (c : Channel k) :
    0 < (Fintype.card (Channel k) : ℝ) := by
  norm_cast
  exact Fintype.card_pos_iff.mpr ⟨c⟩

theorem mergeRate_pos (alpha L : ℝ) {k : ℕ} (c : Channel k) :
    0 < mergeRate alpha L c := by
  exact div_pos (gaussianRootMass_pos alpha L k)
    (mul_pos (mul_pos
      (gaussianRootMass_pos alpha L c.left.1)
      (gaussianRootMass_pos alpha L c.right.1))
      (channelCard_pos c))

/-- Detailed balance holds on each actual ordered merge/split edge. -/
theorem edge_detailed_balance (alpha L : ℝ) {k : ℕ} (c : Channel k)
    (hl : History c.left.1) (hr : History c.right.1) :
    flatGaussianIntensity alpha L hl *
        flatGaussianIntensity alpha L hr * mergeRate alpha L c =
      flatGaussianIntensity alpha L (.node c hl hr) := by
  have hleft : gaussianRootMass alpha L c.left.1 ≠ 0 :=
    ne_of_gt (gaussianRootMass_pos alpha L c.left.1)
  have hright : gaussianRootMass alpha L c.right.1 ≠ 0 :=
    ne_of_gt (gaussianRootMass_pos alpha L c.right.1)
  have hcard : (Fintype.card (Channel k) : ℝ) ≠ 0 :=
    ne_of_gt (channelCard_pos c)
  simp only [flatGaussianIntensity, flatWeight, mergeRate]
  field_simp [hleft, hright, hcard]

/-- No other scalar rate satisfies the same unit-split balance equation. -/
theorem mergeRate_unique (alpha L : ℝ) {k : ℕ} (c : Channel k)
    (q : ℝ)
    (hq : gaussianRootMass alpha L c.left.1 *
        gaussianRootMass alpha L c.right.1 * q =
      gaussianRootMass alpha L k / (Fintype.card (Channel k) : ℝ)) :
    q = mergeRate alpha L c := by
  have hleft : gaussianRootMass alpha L c.left.1 ≠ 0 :=
    ne_of_gt (gaussianRootMass_pos alpha L c.left.1)
  have hright : gaussianRootMass alpha L c.right.1 ≠ 0 :=
    ne_of_gt (gaussianRootMass_pos alpha L c.right.1)
  have hcard : (Fintype.card (Channel k) : ℝ) ≠ 0 :=
    ne_of_gt (channelCard_pos c)
  rw [mergeRate]
  field_simp [hleft, hright, hcard] at hq ⊢
  nlinarith

structure Conclusions : Prop where
  positive : ∀ (alpha L : ℝ) {k : ℕ} (c : Channel k),
    0 < mergeRate alpha L c
  detailed_balance : ∀ (alpha L : ℝ) {k : ℕ} (c : Channel k)
      (hl : History c.left.1) (hr : History c.right.1),
    flatGaussianIntensity alpha L hl *
        flatGaussianIntensity alpha L hr * mergeRate alpha L c =
      flatGaussianIntensity alpha L (.node c hl hr)
  unique_rate : ∀ (alpha L : ℝ) {k : ℕ} (c : Channel k) (q : ℝ),
    gaussianRootMass alpha L c.left.1 *
        gaussianRootMass alpha L c.right.1 * q =
      gaussianRootMass alpha L k / (Fintype.card (Channel k) : ℝ) →
    q = mergeRate alpha L c

theorem completeHistoryDynamicsConclusions : Conclusions where
  positive := mergeRate_pos
  detailed_balance := edge_detailed_balance
  unique_rate := mergeRate_unique

end GeneratedFoundations.Arithmetic.CompleteHistoryDynamics
