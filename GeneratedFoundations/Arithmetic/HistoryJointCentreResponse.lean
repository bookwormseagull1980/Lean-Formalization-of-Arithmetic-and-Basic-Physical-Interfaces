module

public import GeneratedFoundations.Arithmetic.HistoryJointConnector
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Source-centre response on the complete arithmetic charge carrier

The four source coordinates are those already acting on every generated
history and phase. The basis, exchange and grading below act on that same
Hilbert space. Full block responses retain arbitrary history, phase and
spin matrix entries. Their centre trace is their actual difference.

This source grading is distinct from prime-occupation parity and from
reflection of expression histories. The exponential probe is a coordinate
of observation of the constructed finite source, not a root input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryJointCentreResponse

open HistoryJointCharge HistoryJointChargeLattice HistoryJointSourceTransport

abbrev Index (n : ℕ) := (_ : Spin) × HistoryModuleRepresentation.Index n
abbrev Chiral (n : ℕ) := PiLp 2 (fun _ : Fin 2 => Fibre n)

def fullBasis (n : ℕ) : OrthonormalBasis (Index n) ℂ (Space n) :=
  Pi.orthonormalBasis (fun _ : Spin =>
    EuclideanSpace.basisFun (HistoryModuleRepresentation.Index n) ℂ)

def coordinates (n : ℕ) : Space n ≃ₗ[ℂ] (Chiral n × Chiral n) :=
  (PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Spin => Fibre n)).toLinearEquiv.trans
    (WithLp.linearEquiv 2 ℂ (Chiral n × Chiral n))

def diagonalBlocks (n : ℕ) (A B : Module.End ℂ (Chiral n)) :
    Module.End ℂ (Space n) := (coordinates n).symm.conj (LinearMap.prodMap A B)

def grading (n : ℕ) : Module.End ℂ (Space n) := diagonalBlocks n 1 (-1)

theorem grading_eq_source (n : ℕ) : grading n = HistoryJointConnector.grading n := by
  apply LinearMap.ext
  intro x
  apply PiLp.ext
  intro s
  cases s <;> simp [grading, diagonalBlocks, coordinates,
    HistoryJointConnector.grading, sourceAction_apply,
    Operations.SourceCliffordConnector.grading, Matrix.one_apply]

def centreSign {n : ℕ} (i : Index n) : ℝ :=
  Sum.elim (fun _ => 1) (fun _ => -1) i.1

@[simp] theorem centreSign_left {n : ℕ} (s : Fin 2)
    (a : HistoryModuleRepresentation.Index n) : centreSign ⟨Sum.inl s, a⟩ = 1 := rfl

@[simp] theorem centreSign_right {n : ℕ} (s : Fin 2)
    (a : HistoryModuleRepresentation.Index n) : centreSign ⟨Sum.inr s, a⟩ = -1 := rfl

def exchangeIndex {n : ℕ} (i : Index n) : Index n :=
  ⟨HistoryJointSourceTransport.exchangeIndex i.1, i.2⟩

@[simp] theorem exchangeIndex_involution {n : ℕ} (i : Index n) :
    exchangeIndex (exchangeIndex i) = i := by
  rcases i with ⟨s, a⟩
  cases s <;> rfl

theorem exchange_capacity_conservation (n : ℕ) (w : Index n → ℝ) :
    ∑ i, w (exchangeIndex i) = ∑ i, w i :=
  Fintype.sum_bijective _ (Function.Involutive.bijective exchangeIndex_involution)
    _ _ (fun _ => rfl)

theorem centreSign_exchange {n : ℕ} (i : Index n) :
    centreSign (exchangeIndex i) = -centreSign i := by
  rcases i with ⟨s, a⟩
  cases s <;> simp [centreSign, exchangeIndex, HistoryJointSourceTransport.exchangeIndex]

theorem centreSign_sq {n : ℕ} (i : Index n) : centreSign i ^ 2 = 1 := by
  rcases i with ⟨s, a⟩
  cases s <;> norm_num [centreSign]

theorem fullIndex_card (n : ℕ) :
    Fintype.card (Index n) = 4 * HistoryChargeContent.historyCount n * (n + 1) := by
  simp [Index, Spin, Operations.SourceCliffordConnector.ChiralIndex,
    HistoryModuleRepresentation.Index, HistoryMatrixAlgebra.Index,
    HistoryChargeContent.historyCount]
  ring

theorem grading_fullBasis (n : ℕ) (i : Index n) :
    grading n (fullBasis n i) = (centreSign i : ℂ) • fullBasis n i := by
  rw [grading_eq_source]
  apply PiLp.ext
  intro s
  rcases i with ⟨t, a⟩
  cases t <;> cases s <;>
    simp [HistoryJointConnector.grading, sourceAction_apply,
      Operations.SourceCliffordConnector.grading, fullBasis,
      Pi.orthonormalBasis_apply, centreSign, Matrix.one_apply]

theorem diagonalBlocks_trace (n : ℕ) (A B : Module.End ℂ (Chiral n)) :
    LinearMap.trace ℂ (Space n) (diagonalBlocks n A B) =
      LinearMap.trace ℂ (Chiral n) A + LinearMap.trace ℂ (Chiral n) B := by
  rw [diagonalBlocks, LinearMap.trace_conj', LinearMap.trace_prodMap']

theorem exchange_fullBasis (n : ℕ) (i : Index n) :
    exchange n (fullBasis n i) = fullBasis n (exchangeIndex i) := by
  apply PiLp.ext
  intro s
  rcases i with ⟨t, a⟩
  cases t <;> cases s <;>
    simp [exchange_apply, fullBasis, Pi.orthonormalBasis_apply,
      exchangeIndex, HistoryJointSourceTransport.exchangeIndex]

theorem grading_diagonalBlocks (n : ℕ) (A B : Module.End ℂ (Chiral n)) :
    grading n * diagonalBlocks n A B = diagonalBlocks n A (-B) := by
  let e := (coordinates n).symm.conjAlgEquiv ℂ
  change e (LinearMap.prodMap 1 (-1)) * e (LinearMap.prodMap A B) =
    e (LinearMap.prodMap A (-B))
  rw [← map_mul]
  congr 1

theorem centre_trace_response_difference (n : ℕ) (A B : Module.End ℂ (Chiral n)) :
    LinearMap.trace ℂ (Space n) (grading n * diagonalBlocks n A B) =
      LinearMap.trace ℂ (Chiral n) (A - B) := by
  rw [grading_diagonalBlocks, diagonalBlocks_trace]
  simp [sub_eq_add_neg]

theorem common_response_centre_trace (n : ℕ) (A : Module.End ℂ (Chiral n)) :
    LinearMap.trace ℂ (Space n) (grading n * diagonalBlocks n A A) = 0 := by
  rw [centre_trace_response_difference, sub_self, map_zero]

def partition (n : ℕ) (h : ℝ) : ℝ :=
  (∑ i : Index n, Real.exp (h * centreSign i)) / Fintype.card (Index n)

def firstMoment (n : ℕ) (h : ℝ) : ℝ :=
  (∑ i : Index n, centreSign i * Real.exp (h * centreSign i)) / Fintype.card (Index n)

def secondMoment (n : ℕ) (h : ℝ) : ℝ :=
  (∑ i : Index n, centreSign i ^ 2 * Real.exp (h * centreSign i)) /
    Fintype.card (Index n)

def bias (n : ℕ) (h : ℝ) : ℝ := firstMoment n h / partition n h
def susceptibility (n : ℕ) (h : ℝ) : ℝ :=
  secondMoment n h / partition n h - bias n h ^ 2
def restoringHessian (n : ℕ) (h : ℝ) : ℝ := (susceptibility n h)⁻¹

theorem partition_eq_cosh (n : ℕ) (h : ℝ) : partition n h = Real.cosh h := by
  have hc : (Fintype.card (HistoryModuleRepresentation.Index n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [partition, Index, Fintype.sum_sigma, Fintype.sum_sum_type,
    centreSign, Real.cosh_eq, Spin, Operations.SourceCliffordConnector.ChiralIndex]
  field_simp
  ring

theorem firstMoment_eq_sinh (n : ℕ) (h : ℝ) : firstMoment n h = Real.sinh h := by
  have hc : (Fintype.card (HistoryModuleRepresentation.Index n) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [firstMoment, Index, Fintype.sum_sigma, Fintype.sum_sum_type,
    centreSign, Real.sinh_eq, Spin, Operations.SourceCliffordConnector.ChiralIndex]
  field_simp
  ring

theorem secondMoment_eq_partition (n : ℕ) (h : ℝ) :
    secondMoment n h = partition n h := by
  simp only [secondMoment, partition, centreSign_sq, one_mul]

theorem partition_pos (n : ℕ) (h : ℝ) : 0 < partition n h := by
  rw [partition_eq_cosh]
  exact Real.cosh_pos h

theorem partition_even (n : ℕ) (h : ℝ) : partition n (-h) = partition n h := by
  simp [partition_eq_cosh]

theorem bias_eq_tanh (n : ℕ) (h : ℝ) : bias n h = Real.tanh h := by
  rw [bias, firstMoment_eq_sinh, partition_eq_cosh, Real.tanh_eq_sinh_div_cosh]

theorem susceptibility_eq (n : ℕ) (h : ℝ) :
    susceptibility n h = 1 - bias n h ^ 2 := by
  rw [susceptibility, secondMoment_eq_partition, div_self (partition_pos n h).ne']

theorem susceptibility_eq_inv_cosh_sq (n : ℕ) (h : ℝ) :
    susceptibility n h = 1 / Real.cosh h ^ 2 := by
  rw [susceptibility_eq, bias_eq_tanh, Real.tanh_eq_sinh_div_cosh]
  calc
    _ = (Real.cosh h ^ 2 - Real.sinh h ^ 2) / Real.cosh h ^ 2 := by
      field_simp [(Real.cosh_pos h).ne']
    _ = _ := by rw [Real.cosh_sq_sub_sinh_sq]

theorem susceptibility_pos (n : ℕ) (h : ℝ) : 0 < susceptibility n h := by
  rw [susceptibility_eq_inv_cosh_sq]
  positivity

theorem bias_eq_zero_iff (n : ℕ) (h : ℝ) : bias n h = 0 ↔ h = 0 := by
  rw [bias_eq_tanh, Real.tanh_eq_sinh_div_cosh]
  simp [(Real.cosh_pos h).ne', Real.sinh_eq_zero]

theorem logPartition_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (fun x => Real.log (partition n x)) (bias n h) h := by
  simp only [partition_eq_cosh, bias, firstMoment_eq_sinh]
  exact (Real.hasDerivAt_cosh h).log (Real.cosh_pos h).ne'

theorem bias_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (bias n) (susceptibility n h) h := by
  have hd := (Real.hasDerivAt_sinh h).div (Real.hasDerivAt_cosh h) (Real.cosh_pos h).ne'
  have heq : (Real.cosh h * Real.cosh h - Real.sinh h * Real.sinh h) /
      Real.cosh h ^ 2 = 1 - (Real.sinh h / Real.cosh h) ^ 2 := by
    field_simp [(Real.cosh_pos h).ne']
  rw [heq] at hd
  have hb : bias n = Real.sinh / Real.cosh := by
    funext x
    simp [bias, firstMoment_eq_sinh, partition_eq_cosh]
  rw [susceptibility_eq, hb]
  exact hd

theorem closed_partition (n : ℕ) : partition n 0 = 1 := by simp [partition_eq_cosh]
theorem closed_bias (n : ℕ) : bias n 0 = 0 := by simp [bias_eq_tanh]
theorem closed_susceptibility (n : ℕ) : susceptibility n 0 = 1 := by
  simp [susceptibility_eq, closed_bias]
theorem closed_restoringHessian (n : ℕ) : restoringHessian n 0 = 1 := by
  simp [restoringHessian, closed_susceptibility]

/-- Removing the actual neutral kernel changes the centre trace. The history
multiplicity cancels in this normalized quotient observable, although it
remains in the unnormalized content capacities. -/
theorem charged_quotient_bias {n : ℕ} (hn : 2 ≤ n) :
    ((HistoryChargeContent.leftCount n : ℚ) - HistoryChargeContent.rightChargedCount n) /
      (HistoryChargeContent.leftCount n + HistoryChargeContent.rightChargedCount n) =
        1 / (4 * n + 3) := by
  have hh : (HistoryChargeContent.historyCount n : ℚ) ≠ 0 := by
    exact_mod_cast (HistoryChargeContent.historyCount_pos n).ne'
  rw [HistoryChargeContent.imbalance_eq hn, HistoryChargeContent.leftCount_eq,
    HistoryChargeContent.rightChargedCount_eq hn]
  push_cast
  field_simp
  ring

theorem charged_quotient_fluctuation {n : ℕ} (hn : 2 ≤ n) :
    1 - (((HistoryChargeContent.leftCount n : ℚ) -
      HistoryChargeContent.rightChargedCount n) /
      (HistoryChargeContent.leftCount n + HistoryChargeContent.rightChargedCount n)) ^ 2 =
        (4 * n + 2) * (4 * n + 4) / (4 * n + 3) ^ 2 := by
  have hp : (4 * n + 3 : ℚ) ≠ 0 := by positivity
  rw [charged_quotient_bias hn]
  field_simp
  ring

theorem charged_quotient_fluctuation_rank_three :
    1 - (((HistoryChargeContent.leftCount 3 : ℚ) -
      HistoryChargeContent.rightChargedCount 3) /
      (HistoryChargeContent.leftCount 3 + HistoryChargeContent.rightChargedCount 3)) ^ 2 =
        224 / 225 := by
  rw [charged_quotient_fluctuation (by norm_num : 2 ≤ 3)]
  norm_num

structure Conclusions : Prop where
  actual_dimension : ∀ n,
    Fintype.card (Index n) = 4 * HistoryChargeContent.historyCount n * (n + 1)
  actual_grading : ∀ n, grading n = HistoryJointConnector.grading n
  complete_basis_eigenvalues : ∀ n i,
    grading n (fullBasis n i) = (centreSign i : ℂ) • fullBasis n i
  exchange_on_basis : ∀ n i, exchange n (fullBasis n i) = fullBasis n (exchangeIndex i)
  conserved_capacity : ∀ n (w : Index n → ℝ), ∑ i, w (exchangeIndex i) = ∑ i, w i
  full_response_difference : ∀ n A B,
    LinearMap.trace ℂ (Space n) (grading n * diagonalBlocks n A B) =
      LinearMap.trace ℂ (Chiral n) (A - B)
  common_response_balance : ∀ n A,
    LinearMap.trace ℂ (Space n) (grading n * diagonalBlocks n A A) = 0
  finite_trace : ∀ n h, partition n h = Real.cosh h
  unique_unbiased_probe : ∀ n h, bias n h = 0 ↔ h = 0
  logarithmic_response : ∀ n h,
    HasDerivAt (fun x => Real.log (partition n x)) (bias n h) h
  exact_fluctuation : ∀ n h, HasDerivAt (bias n) (susceptibility n h) h
  unbiased_source : ∀ n, bias n 0 = 0
  positive_fluctuation : ∀ n h, 0 < susceptibility n h
  unit_fluctuation : ∀ n, susceptibility n 0 = 1
  unit_restoring_hessian : ∀ n, restoringHessian n 0 = 1
  quotient_centre_bias : ∀ n, 2 ≤ n →
    ((HistoryChargeContent.leftCount n : ℚ) - HistoryChargeContent.rightChargedCount n) /
      (HistoryChargeContent.leftCount n + HistoryChargeContent.rightChargedCount n) =
        1 / (4 * n + 3)

theorem generated : Conclusions where
  actual_dimension := fullIndex_card
  actual_grading := grading_eq_source
  complete_basis_eigenvalues := grading_fullBasis
  exchange_on_basis := exchange_fullBasis
  conserved_capacity := exchange_capacity_conservation
  full_response_difference := centre_trace_response_difference
  common_response_balance := common_response_centre_trace
  finite_trace := partition_eq_cosh
  unique_unbiased_probe := bias_eq_zero_iff
  logarithmic_response := logPartition_hasDerivAt
  exact_fluctuation := bias_hasDerivAt
  unbiased_source := closed_bias
  positive_fluctuation := susceptibility_pos
  unit_fluctuation := closed_susceptibility
  unit_restoring_hessian := closed_restoringHessian
  quotient_centre_bias := fun _ => charged_quotient_bias

end GeneratedFoundations.Arithmetic.HistoryJointCentreResponse
