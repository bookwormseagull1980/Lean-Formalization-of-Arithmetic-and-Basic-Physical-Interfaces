module

public import GeneratedFoundations.Analysis.HistoryGibbsResponse

/-!
# Exponential response of the actual history orientation

The reference is the generated history probability and the observable is its
actual integer orientation score. The real variable is a probe coordinate,
not an additional source input. Reflection makes the partition even and the
unperturbed mean zero. Differentiation at every probe value gives the actual
variance. In contrast to a balanced two-level carrier, a history fibre can
have fixed points and more than two score values; no universal cosh formula
or unit variance is imposed on it.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryCentralResponse

open Arithmetic.CompleteHistory Arithmetic.CompleteHistoryGeometry
open Arithmetic.HistoryObservation

abbrev Index (n : ℕ) := History (n + 1)

def score {n : ℕ} (x : Index n) : ℝ := (orientationScore x : ℝ)

@[simp] theorem score_reflect {n : ℕ} (x : Index n) : score (reflect x) = -score x := by
  simp [score]

def weight {n : ℕ} (h : ℝ) (x : Index n) : ℝ := flatWeight x * Real.exp (h * score x)

theorem weight_pos {n : ℕ} (h : ℝ) (x : Index n) : 0 < weight h x :=
  mul_pos (Arithmetic.HistoryObservation.weight_pos x) (Real.exp_pos _)

def partition (n : ℕ) (h : ℝ) : ℝ := ∑ x : Index n, weight h x

def moment (n : ℕ) (h : ℝ) (f : Index n → ℝ) : ℝ := ∑ x, weight h x * f x

def bias (n : ℕ) (h : ℝ) : ℝ := moment n h score / partition n h

def susceptibility (n : ℕ) (h : ℝ) : ℝ :=
  moment n h (fun x => score x ^ 2) / partition n h - bias n h ^ 2

theorem partition_pos (n : ℕ) (h : ℝ) : 0 < partition n h :=
  Finset.sum_pos (fun x _ => weight_pos h x) Finset.univ_nonempty

@[simp] theorem closed_partition (n : ℕ) : partition n 0 = 1 := by
  simp only [partition, weight, zero_mul, Real.exp_zero, mul_one]
  exact flatWeight_sum_one (n + 1) (by omega)

theorem closed_bias (n : ℕ) : bias n 0 = 0 := by
  simpa [bias, moment, weight, score, mean] using orientation_mean_zero (n + 1)

theorem closed_susceptibility (n : ℕ) :
    susceptibility n 0 = Arithmetic.HistoryObservation.energy (score (n := n)) := by
  simp [susceptibility, closed_bias, moment, weight,
    Arithmetic.HistoryObservation.energy, pairing, mean, pow_two]

/-- The scalar orientation response is the corresponding direction of the
complete same-source Hermitian Hessian, for every Gaussian observation. -/
theorem closed_hessian (n : ℕ) (alpha L : ℝ) :
    susceptibility n 0 =
      fderiv ℝ (fderiv ℝ (HistoryGibbsResponse.response n alpha L)) 0
        (HistoryGibbsResponse.diagonalObservation (score (n := n)))
        (HistoryGibbsResponse.diagonalObservation (score (n := n))) := by
  rw [closed_susceptibility]
  exact (HistoryGibbsResponse.orientation_hessian n alpha L).symm

theorem partition_even (n : ℕ) (h : ℝ) : partition n (-h) = partition n h := by
  apply Fintype.sum_equiv (reflection (n + 1))
  intro x
  simp [weight, reflection]

theorem moment_score_neg (n : ℕ) (h : ℝ) :
    moment n (-h) score = -moment n h score := by
  simp only [moment, ← Finset.sum_neg_distrib]
  apply Fintype.sum_equiv (reflection (n + 1))
  intro x
  simp [weight, reflection]

theorem bias_odd (n : ℕ) (h : ℝ) : bias n (-h) = -bias n h := by
  rw [bias, bias, partition_even, moment_score_neg, neg_div]

theorem partition_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (partition n) (moment n h score) h := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun (x : Index n) _ =>
    ((((hasDerivAt_id h).mul_const (score x)).exp).const_mul (flatWeight x)))
  convert hd using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro x _
    simp only [weight, id_eq]
    ring

theorem moment_hasDerivAt {n : ℕ} (h : ℝ) (f : Index n → ℝ) :
    HasDerivAt (fun u => moment n u f) (moment n h (fun x => score x * f x)) h := by
  have hd := HasDerivAt.fun_sum (u := Finset.univ) (fun x _ =>
    (((((hasDerivAt_id h).mul_const (score x)).exp).const_mul (flatWeight x)).mul_const (f x)))
  convert hd using 1
  · rfl
  · apply Finset.sum_congr rfl
    intro x _
    simp only [weight, id_eq]
    ring

theorem logPartition_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (fun u => Real.log (partition n u)) (bias n h) h :=
  (partition_hasDerivAt n h).log (ne_of_gt (partition_pos n h))

theorem bias_hasDerivAt (n : ℕ) (h : ℝ) :
    HasDerivAt (bias n) (susceptibility n h) h := by
  have hd := (moment_hasDerivAt h (score (n := n))).div
    (partition_hasDerivAt n h) (ne_of_gt (partition_pos n h))
  convert hd using 1
  · rfl
  · simp only [susceptibility, bias, ← pow_two]
    field_simp [(ne_of_gt (partition_pos n h))]

theorem variance_identity (n : ℕ) (h : ℝ) :
    susceptibility n h =
      (∑ x : Index n, weight h x * (score x - bias n h) ^ 2) / partition n h := by
  have he : (∑ x : Index n, weight h x * (score x - bias n h) ^ 2) =
      moment n h (fun x => score x ^ 2) - 2 * bias n h * moment n h score +
        bias n h ^ 2 * partition n h := by
    simp only [moment, partition, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [he]
  unfold susceptibility bias
  field_simp [(ne_of_gt (partition_pos n h))]
  ring

theorem susceptibility_nonneg (n : ℕ) (h : ℝ) : 0 ≤ susceptibility n h := by
  rw [variance_identity]
  apply div_nonneg _ (partition_pos n h).le
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (weight_pos h x).le (sq_nonneg _))

theorem susceptibility_zero_iff (n : ℕ) (h : ℝ) :
    susceptibility n h = 0 ↔ ∀ x : Index n, score x = bias n h := by
  rw [variance_identity, div_eq_zero_iff]
  simp only [(ne_of_gt (partition_pos n h)), or_false]
  constructor
  · intro hz x
    have hx := (Finset.sum_eq_zero_iff_of_nonneg
      (fun x _ => mul_nonneg (weight_pos h x).le (sq_nonneg _))).mp hz x (Finset.mem_univ x)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp
      ((mul_eq_zero.mp hx).resolve_left (ne_of_gt (weight_pos h x))))
  · intro hx
    apply Finset.sum_eq_zero
    intro x _
    simp [hx x]

structure Conclusions : Prop where
  normalized_source : ∀ n, partition n 0 = 1
  reflection : ∀ n h, partition n (-h) = partition n h
  closed_balance : ∀ n, bias n 0 = 0
  exact_log_response : ∀ n h,
    HasDerivAt (fun u => Real.log (partition n u)) (bias n h) h
  exact_fluctuation : ∀ n h, HasDerivAt (bias n) (susceptibility n h) h
  positive_fluctuation : ∀ n h, 0 ≤ susceptibility n h
  actual_closed_fluctuation : ∀ n,
    susceptibility n 0 = Arithmetic.HistoryObservation.energy (score (n := n))

theorem generated : Conclusions where
  normalized_source := closed_partition
  reflection := partition_even
  closed_balance := closed_bias
  exact_log_response := logPartition_hasDerivAt
  exact_fluctuation := bias_hasDerivAt
  positive_fluctuation := susceptibility_nonneg
  actual_closed_fluctuation := closed_susceptibility

end GeneratedFoundations.Analysis.HistoryCentralResponse
