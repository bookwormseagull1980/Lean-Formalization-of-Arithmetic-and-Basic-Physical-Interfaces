module

public import GeneratedFoundations.Physical.SourceTorsionContent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.LinearAlgebra.Trace

/-!
# Centre balance on the complete generated matter carrier

The index set and grading below belong to the already constructed matter
carrier, including its neutral right-handed line. No multiplicity, preferred
state, driving field or response coefficient is supplied at the root.

The real variable `h` is the coordinate of the exponential centre probe.
At its origin the normalized trace is the closed, unbiased source state.
The fluctuation and restoring coefficients are computed from this trace.
The operator identity also covers every common left/right response, without
requiring that response to be a scalar matrix.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceClosedCenterResponse

open SourceChiralCarrier SourceMinimalRepresentation

/-- The eigenvalue of the actual source grading on a matter basis vector. -/
def centreSign (i : FullIndex) : ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1) i.2

def exchangeIndex (i : FullIndex) : FullIndex :=
  (i.1, (Equiv.sumComm SpinLabel SpinLabel) i.2)

@[simp] theorem exchangeIndex_involution (i : FullIndex) :
    exchangeIndex (exchangeIndex i) = i := by
  rcases i with ⟨c, s | s⟩ <;> rfl

/-- Exchange permutes the actual complete carrier. Its total weighted
capacity is unchanged; no state is removed or normalized away. -/
theorem exchange_capacity_conservation (w : FullIndex → ℝ) :
    ∑ i : FullIndex, w (exchangeIndex i) = ∑ i : FullIndex, w i := by
  classical
  exact Fintype.sum_bijective _ (Function.Involutive.bijective exchangeIndex_involution)
    _ _ (fun _ => rfl)

@[simp] theorem centreSign_left (c : ColourLabel) (s : SpinLabel) :
    centreSign (c, Sum.inl s) = 1 := rfl

@[simp] theorem centreSign_right (c : ColourLabel) (s : SpinLabel) :
    centreSign (c, Sum.inr s) = -1 := rfl

theorem centreSign_exchange (i : FullIndex) :
    centreSign (exchangeIndex i) = -centreSign i := by
  rcases i with ⟨c, s | s⟩ <;> simp [exchangeIndex, centreSign]

theorem centreSign_sq (i : FullIndex) : centreSign i ^ 2 = 1 := by
  rcases i with ⟨c, s | s⟩ <;> norm_num [centreSign]

/-- The signs are the eigenvalues of the constructed operator, not new labels. -/
theorem grading_fullBasis (i : FullIndex) :
    grading (fullBasis i) = (centreSign i : ℂ) • fullBasis i := by
  rcases i with ⟨c, s | s⟩ <;>
    simp [fullBasis_left, fullBasis_right, grading_left, grading_right]

theorem exchange_fullBasis (i : FullIndex) :
    exchange (fullBasis i) = fullBasis (exchangeIndex i) := by
  rcases i with ⟨c, s | s⟩ <;>
    simp [exchangeIndex, fullBasis_left, fullBasis_right,
      exchange_eq_connector_one, connector_left, connector_right, spinOnSource]

theorem fullIndex_card : Fintype.card FullIndex = 16 := by
  norm_num [FullIndex, ColourLabel, ChiralLabel, SpinLabel]

set_option maxHeartbeats 1200000 in
theorem diagonalBlocks_trace (A B : Module.End ℂ SourceCarrier) :
    LinearMap.trace ℂ FullMatter (diagonalBlocks A B) =
      LinearMap.trace ℂ SourceCarrier A + LinearMap.trace ℂ SourceCarrier B := by
  change LinearMap.trace ℂ FullMatter
    (fullMatterCoordinates.conj (LinearMap.prodMap A B)) = _
  rw [LinearMap.trace_conj', LinearMap.trace_prodMap']

set_option maxHeartbeats 1200000 in
/-- A common response has exactly zero centre trace, with all matrix entries
retained. Positivity or diagonality inside a chiral block is not needed. -/
theorem common_response_centre_trace (A : Module.End ℂ SourceCarrier) :
    LinearMap.trace ℂ FullMatter (grading * diagonalBlocks A A) = 0 := by
  rw [grading, diagonalBlocks_mul, one_mul, neg_one_mul, diagonalBlocks_trace,
    map_neg, add_neg_cancel]

/-- Finite exponential trace of the actual sixteen source basis states. -/
def partition (h : ℝ) : ℝ :=
  (∑ i : FullIndex, Real.exp (h * centreSign i)) / Fintype.card FullIndex

def firstMoment (h : ℝ) : ℝ :=
  (∑ i : FullIndex, centreSign i * Real.exp (h * centreSign i)) /
    Fintype.card FullIndex

def secondMoment (h : ℝ) : ℝ :=
  (∑ i : FullIndex, centreSign i ^ 2 * Real.exp (h * centreSign i)) /
    Fintype.card FullIndex

def bias (h : ℝ) : ℝ := firstMoment h / partition h

def susceptibility (h : ℝ) : ℝ :=
  secondMoment h / partition h - bias h ^ 2

def restoringHessian (h : ℝ) : ℝ := (susceptibility h)⁻¹

theorem partition_eq_cosh (h : ℝ) : partition h = Real.cosh h := by
  simp [partition, Fintype.sum_prod_type,
    Fintype.sum_sum_type, centreSign, ColourLabel, SpinLabel, ChiralLabel,
    Real.cosh_eq]
  ring

theorem firstMoment_eq_sinh (h : ℝ) : firstMoment h = Real.sinh h := by
  simp [firstMoment, Fintype.sum_prod_type,
    Fintype.sum_sum_type, centreSign, ColourLabel, SpinLabel, ChiralLabel,
    Real.sinh_eq]
  ring

theorem secondMoment_eq_partition (h : ℝ) : secondMoment h = partition h := by
  simp only [secondMoment, partition, centreSign_sq, one_mul]

theorem partition_pos (h : ℝ) : 0 < partition h := by
  rw [partition_eq_cosh]
  exact Real.cosh_pos h

theorem partition_even (h : ℝ) : partition (-h) = partition h := by
  simp [partition_eq_cosh]

theorem bias_eq_tanh (h : ℝ) : bias h = Real.tanh h := by
  rw [bias, firstMoment_eq_sinh, partition_eq_cosh, Real.tanh_eq_sinh_div_cosh]

theorem susceptibility_eq (h : ℝ) :
    susceptibility h = 1 - bias h ^ 2 := by
  rw [susceptibility, secondMoment_eq_partition, div_self (partition_pos h).ne']

theorem susceptibility_eq_inv_cosh_sq (h : ℝ) :
    susceptibility h = 1 / Real.cosh h ^ 2 := by
  rw [susceptibility_eq, bias_eq_tanh, Real.tanh_eq_sinh_div_cosh]
  calc
    _ = (Real.cosh h ^ 2 - Real.sinh h ^ 2) / Real.cosh h ^ 2 := by
      field_simp [(Real.cosh_pos h).ne']
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]

theorem susceptibility_pos (h : ℝ) : 0 < susceptibility h := by
  rw [susceptibility_eq_inv_cosh_sq]
  exact div_pos zero_lt_one (sq_pos_of_pos (Real.cosh_pos h))

theorem bias_eq_zero_iff (h : ℝ) : bias h = 0 ↔ h = 0 := by
  rw [bias_eq_tanh, Real.tanh_eq_sinh_div_cosh]
  simp [(Real.cosh_pos h).ne', Real.sinh_eq_zero]

/-- Fluctuation--response identity of the same finite source trace. -/
theorem logPartition_hasDerivAt (h : ℝ) :
    HasDerivAt (fun x => Real.log (partition x)) (bias h) h := by
  simp only [partition_eq_cosh, bias, firstMoment_eq_sinh]
  exact (Real.hasDerivAt_cosh h).log (Real.cosh_pos h).ne'

theorem bias_hasDerivAt (h : ℝ) : HasDerivAt bias (susceptibility h) h := by
  have hd := (Real.hasDerivAt_sinh h).div (Real.hasDerivAt_cosh h)
    (Real.cosh_pos h).ne'
  have heq : (Real.cosh h * Real.cosh h - Real.sinh h * Real.sinh h) /
      Real.cosh h ^ 2 = 1 - (Real.sinh h / Real.cosh h) ^ 2 := by
    field_simp [(Real.cosh_pos h).ne']
  rw [heq] at hd
  have hb : bias = Real.sinh / Real.cosh := by
    funext x
    simp [bias, firstMoment_eq_sinh, partition_eq_cosh]
  rw [susceptibility_eq, hb]
  exact hd

theorem closed_partition : partition 0 = 1 := by simp [partition_eq_cosh]
theorem closed_bias : bias 0 = 0 := by simp [bias_eq_tanh]
theorem closed_susceptibility : susceptibility 0 = 1 := by
  simp [susceptibility_eq, closed_bias]
theorem closed_restoringHessian : restoringHessian 0 = 1 := by
  simp [restoringHessian, closed_susceptibility]

/-- The charged quotient and the complete carrier have distinct centre traces. -/
theorem charged_quotient_bias :
    ((SourceTorsionContent.leftCount : ℝ) - SourceTorsionContent.rightChargedCount) /
      (SourceTorsionContent.leftCount + SourceTorsionContent.rightChargedCount) = 1 / 15 := by
  norm_num [SourceTorsionContent.leftCount, SourceTorsionContent.rightChargedCount,
    SourceTorsionContent.sectorMultiplicity, SourceTorsionContent.colourMultiplicity,
    SourceTorsionContent.spinMultiplicity]

theorem charged_quotient_fluctuation :
    1 - (((SourceTorsionContent.leftCount : ℝ) - SourceTorsionContent.rightChargedCount) /
      (SourceTorsionContent.leftCount + SourceTorsionContent.rightChargedCount)) ^ 2 =
      224 / 225 := by
  rw [charged_quotient_bias]
  norm_num

structure Conclusions : Prop where
  carrier_dimension : Fintype.card FullIndex = 16
  capacity_conservation : ∀ w : FullIndex → ℝ,
    ∑ i : FullIndex, w (exchangeIndex i) = ∑ i : FullIndex, w i
  grading_eigenvalues : ∀ i, grading (fullBasis i) = (centreSign i : ℂ) • fullBasis i
  exchange_on_basis : ∀ i, exchange (fullBasis i) = fullBasis (exchangeIndex i)
  common_response_balance : ∀ A : Module.End ℂ SourceCarrier,
    LinearMap.trace ℂ FullMatter (grading * diagonalBlocks A A) = 0
  finite_trace : ∀ h, partition h = Real.cosh h
  unique_unbiased_probe : ∀ h, bias h = 0 ↔ h = 0
  positive_fluctuation : ∀ h, 0 < susceptibility h
  logarithmic_response : ∀ h,
    HasDerivAt (fun x => Real.log (partition x)) (bias h) h
  fluctuation_response : ∀ h, HasDerivAt bias (susceptibility h) h
  zero_centre_bias : bias 0 = 0
  unit_fluctuation : susceptibility 0 = 1
  unit_restoring_hessian : restoringHessian 0 = 1

theorem generated : Conclusions where
  carrier_dimension := fullIndex_card
  capacity_conservation := exchange_capacity_conservation
  grading_eigenvalues := grading_fullBasis
  exchange_on_basis := exchange_fullBasis
  common_response_balance := common_response_centre_trace
  finite_trace := partition_eq_cosh
  unique_unbiased_probe := bias_eq_zero_iff
  positive_fluctuation := susceptibility_pos
  logarithmic_response := logPartition_hasDerivAt
  fluctuation_response := bias_hasDerivAt
  zero_centre_bias := closed_bias
  unit_fluctuation := closed_susceptibility
  unit_restoring_hessian := closed_restoringHessian

end GeneratedFoundations.Physical.SourceClosedCenterResponse
