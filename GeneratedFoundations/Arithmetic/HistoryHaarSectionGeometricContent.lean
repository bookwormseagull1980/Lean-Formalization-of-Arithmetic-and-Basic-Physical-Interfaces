module

public import GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricState

/-!
# Content balance derived from the original geometric Gaussian action

The two sector counts below are computed on the actual joint spectral
support. They are not supplied content parameters. Differentiation of the
original geometric partition couples these counts to the restoring mass
fractions of the very same modes. Both quadratures have already been
combined in that partition.

This module gives the content equation and its necessary screening bounds
at a fixed support. It does not replace frequency-window variation by this
spatial equation, or select a cutoff by minimizing the number of labels.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricContent

open HistoryHaarSectionCovariance (WindowIndex)
open HistoryHaarSectionWindow (kinetic restoring)
open HistoryHaarSectionGeometricState (force freeEnergy)

def scalarCount (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i : WindowIndex N B 0, if i.val.isRight = true then 1 else 0

def connectionCount (N : ℕ) (B : ℝ) : ℝ :=
  ∑ i : WindowIndex N B 0, if i.val.isRight = true then 0 else 1

def restoringShare (N : ℕ) (B c : ℝ) : ℝ :=
  ∑ i : WindowIndex N B 0, if i.val.isRight = true then
    c ^ 2 * restoring N i.val / (kinetic N i.val + c ^ 2 * restoring N i.val) else 0

theorem logarithmic_force_content (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    c * force N B c = scalarCount N B - connectionCount N B + 2 * restoringShare N B c := by
  rw [HistoryHaarSectionGeometricState.logarithmic_force N B hc]
  unfold scalarCount connectionCount restoringShare
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> ring

/-- This compatibility equation follows from the original partition's
geometric stationarity, rather than from a prescribed response level. -/
theorem stationary_content_iff (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    force N B c = 0 ↔
      connectionCount N B = scalarCount N B + 2 * restoringShare N B c := by
  have he := logarithmic_force_content N B hc
  constructor
  · intro h
    rw [h, mul_zero] at he
    linarith
  · intro h
    have hz : c * force N B c = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left hc.ne'

theorem variational_content_iff (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    deriv (freeEnergy N B) c = 0 ↔
      connectionCount N B = scalarCount N B + 2 * restoringShare N B c := by
  rw [(HistoryHaarSectionGeometricState.freeEnergy_hasDerivAt N B hc).deriv]
  exact stationary_content_iff N B hc

private theorem denominator_pos (N : ℕ) {c : ℝ} (hc : 0 < c)
    (i : HistoryHaarSectionJointHessian.Index N) :
    0 < kinetic N i + c ^ 2 * restoring N i := by
  cases i with
  | inl i =>
    simpa only [kinetic, restoring, Sum.elim_inl, mul_zero, add_zero] using
      HistoryHaarClosedHessian.eigenvalue_pos N i
  | inr i =>
    exact add_pos_of_nonneg_of_pos
      (Geometry.SourceCasimirClosure.energy_nonneg _)
      (mul_pos (sq_pos_of_pos hc) (HistoryDefiningResponse.coefficient_pos N))

theorem restoringShare_nonneg (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    0 ≤ restoringShare N B c := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact div_nonneg (mul_nonneg (sq_nonneg c)
      (HistoryHaarSectionWindow.restoring_nonneg N i.val)) (denominator_pos N hc i.val).le
  · exact le_rfl

theorem restoringShare_le_scalarCount (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c) :
    restoringShare N B c ≤ scalarCount N B := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · apply (div_le_one (denominator_pos N hc i.val)).2
    linarith [HistoryHaarSectionWindow.kinetic_nonneg N i.val]
  · exact le_rfl

theorem stationary_content_bounds (N : ℕ) (B : ℝ) {c : ℝ} (hc : 0 < c)
    (hstationary : force N B c = 0) :
    scalarCount N B ≤ connectionCount N B ∧
      connectionCount N B ≤ 3 * scalarCount N B := by
  have he := (stationary_content_iff N B hc).1 hstationary
  have h0 := restoringShare_nonneg N B hc
  have h1 := restoringShare_le_scalarCount N B hc
  constructor <;> linarith

structure Conclusions : Prop where
  actual_variational_content : ∀ N B c, 0 < c →
    (deriv (freeEnergy N B) c = 0 ↔
      connectionCount N B = scalarCount N B + 2 * restoringShare N B c)
  necessary_screening : ∀ N B c, 0 < c → force N B c = 0 →
    scalarCount N B ≤ connectionCount N B ∧ connectionCount N B ≤ 3 * scalarCount N B

theorem generated : Conclusions where
  actual_variational_content := fun N B _ hc => variational_content_iff N B hc
  necessary_screening := fun N B _ hc => stationary_content_bounds N B hc

end GeneratedFoundations.Arithmetic.HistoryHaarSectionGeometricContent
