module

public import GeneratedFoundations.Arithmetic.HistoryGaussianWindowResponse
public import GeneratedFoundations.Arithmetic.HistoryGaussianConnection
public import GeneratedFoundations.Geometry.SourceFieldSpectrum
public import GeneratedFoundations.Geometry.SourceSpinorParityResolvent
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Complete spectral supports for arithmetic response windows

The observation contains every eigenvector of the original joint Hessian
below its strict cutoff. The finite enumeration below is proved exhaustive:
it is not a freely selected nonempty set. Both curl signs, all source rows,
all matrix entries and the full homogeneous-state block remain present.

The second part counts the positive arithmetic root positions with their
original history--phase fibres. A plateau is characterized by its last
retained and first excluded root. Its position count is calculated rather
than set equal to the physical three-position count.

These support and position statements supply the two discrete ingredients
needed in addition to a response equation. They do not prescribe how many
positions an arithmetic endpoint must contain.

The Hessian spectral projection and the source-frequency window are distinct.
The latter cuts off the kinetic index, not the sum of kinetic and restoring
indices. The homogeneous state has zero kinetic index and is retained at
every positive bandwidth, including when its restoring coefficient exceeds
that bandwidth. The two indices are calculated from the original action.
The responses below remain defined observations; their root theorems do not
derive an arithmetic effective-action endpoint selection law.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace GeneratedFoundations.Arithmetic.HistorySpectralWindow

open Geometry.SourceOneFormCurlSpectrum
open Geometry.SourceOneFormCurlBranches
open Geometry.SourceOneFormSpectralCore
open Geometry.SourceOneFormCoclosedSpectrum
open Geometry.SourceOneFormHodgeLaplacian

local instance (N : ℕ) : DecidableEq (HistoryHaarJointHessian.Index N) := Classical.decEq _

/-- All actual curl coordinates in source rows of degree less than `D`.
The zero-curl coordinates are removed only by the proved coclosed subtype. -/
def curlCandidates (D : ℕ) : Finset CurlIndex := by
  classical
  exact (Finset.range D).biUnion fun m =>
    if hm : Even m then
      Finset.univ.image fun p : Fin (m + 1) × Fin (3 * (m + 1)) =>
        (⟨⟨⟨m, hm⟩, p.1⟩, p.2⟩ : CurlIndex)
    else ∅

@[simp] theorem mem_curlCandidates (D : ℕ) (a : CurlIndex) :
    a ∈ curlCandidates D ↔ a.1.1.val < D := by
  classical
  unfold curlCandidates
  constructor
  · intro h
    obtain ⟨m, hm, ha⟩ := Finset.mem_biUnion.mp h
    split_ifs at ha with he
    · obtain ⟨p, _, hp⟩ := Finset.mem_image.mp ha
      have hd := congrArg (fun b : CurlIndex => b.1.1.val) hp
      simpa only [← hd] using Finset.mem_range.mp hm
    · simp at ha
  · intro h
    apply Finset.mem_biUnion.mpr
    refine ⟨a.1.1.val, Finset.mem_range.mpr h, ?_⟩
    simp only [dite_eq_left a.1.1.property]
    exact Finset.mem_image.mpr ⟨(a.1.2, a.2), Finset.mem_univ _, rfl⟩

/-- The original row degree is bounded by the differentiated Hodge energy.
This is the finiteness input, derived from both actual curl branches. -/
theorem row_degree_sq_le (a : CoclosedIndex) :
    (a.val.1.1.val : ℝ) ^ 2 ≤ hodgeEigenvalue a := by
  rcases curlEigenvalue_branches a.val.1.1.val a.val.2 with hz | hp | hn
  · exact (a.property hz).elim
  · change (a.val.1.1.val : ℝ) ^ 2 ≤ curlEigenvalue _ _ ^ 2
    rw [hp]
    have hm : (0 : ℝ) ≤ a.val.1.1.val := Nat.cast_nonneg _
    nlinarith
  · change (a.val.1.1.val : ℝ) ^ 2 ≤ curlEigenvalue _ _ ^ 2
    rw [hn, neg_sq]

def fieldCandidates (D : ℕ) : Finset CoclosedIndex := by
  classical
  exact (curlCandidates D).subtype fun a => eigenvalue a ≠ 0

@[simp] theorem mem_fieldCandidates (D : ℕ) (a : CoclosedIndex) :
    a ∈ fieldCandidates D ↔ a.val.1.1.val < D := by
  classical
  simp [fieldCandidates]

def jointCandidates (N D : ℕ) : Finset (HistoryHaarJointHessian.Index N) := by
  classical
  exact ((Finset.univ : Finset (HistoryHaarClosedHessian.Label N)) ×ˢ
    fieldCandidates D).disjSum Finset.univ

def enumerationBound (B : ℝ) : ℕ := Nat.ceil B + 1

theorem cutoff_mem_candidates (N : ℕ) (B : ℝ)
    (i : HistoryHaarJointHessian.Index N)
    (hi : HistoryHaarJointHessian.eigenvalue N i < B) :
    i ∈ jointCandidates N (enumerationBound B) := by
  classical
  cases i with
  | inl a =>
    have hm := row_degree_sq_le a.2
    have hb : B < (enumerationBound B : ℝ) := by
      have hceil : B ≤ (Nat.ceil B : ℝ) := Nat.le_ceil B
      simp only [enumerationBound, Nat.cast_add, Nat.cast_one]
      linarith
    have he : hodgeEigenvalue a.2 < B := hi
    have hd : a.2.val.1.1.val < enumerationBound B := by
      by_contra hnot
      have hnat : enumerationBound B ≤ a.2.val.1.1.val := Nat.le_of_not_gt hnot
      have hcast : (enumerationBound B : ℝ) ≤ (a.2.val.1.1.val : ℝ) := by
        exact_mod_cast hnat
      have hone : (1 : ℝ) ≤ (a.2.val.1.1.val : ℝ) := by
        exact_mod_cast (show 1 ≤ a.2.val.1.1.val by
          have : 1 ≤ enumerationBound B := by unfold enumerationBound; omega
          omega)
      nlinarith
    simp [jointCandidates, hd]
  | inr a => simp [jointCandidates]

/-- The complete strict spectral projection, as a finite set of the
original orthonormal-basis labels. `B` is a squared spectral cutoff. -/
def support (N : ℕ) (B : ℝ) : Finset (HistoryHaarJointHessian.Index N) := by
  classical
  exact (jointCandidates N (enumerationBound B)).filter fun i =>
    HistoryHaarJointHessian.eigenvalue N i < B

@[simp] theorem mem_support (N : ℕ) (B : ℝ)
    (i : HistoryHaarJointHessian.Index N) :
    i ∈ support N B ↔ HistoryHaarJointHessian.eigenvalue N i < B := by
  classical
  simp only [support, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨cutoff_mem_candidates N B i h, h⟩⟩

theorem support_unique (N : ℕ) (B : ℝ)
    (S : Finset (HistoryHaarJointHessian.Index N))
    (hS : ∀ i, i ∈ S ↔ HistoryHaarJointHessian.eigenvalue N i < B) :
    S = support N B := by
  ext i
  exact (hS i).trans (mem_support N B i).symm

theorem support_mono (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    support N B ⊆ support N C := by
  intro i hi
  exact (mem_support N C i).mpr (lt_of_lt_of_le ((mem_support N B i).mp hi) hBC)

theorem support_nonempty_iff (N : ℕ) (B : ℝ) :
    (support N B).Nonempty ↔ HistoryHaarJointHessian.gapSq N < B := by
  constructor
  · rintro ⟨i, hi⟩
    exact lt_of_le_of_lt (HistoryHaarJointHessian.eigenvalue_ge_gap N i)
      ((mem_support N B i).mp hi)
  · intro h
    refine ⟨HistoryHaarJointHessian.minimizingIndex N, ?_⟩
    rw [mem_support, HistoryHaarJointHessian.eigenvalue_minimizingIndex]
    exact h

/-- A support changes exactly when an actual eigenvalue is crossed.
For a plateau `(last retained, first excluded]`, the left endpoint is
excluded and the right endpoint is retained. -/
theorem support_constant_iff_no_crossing (N : ℕ) {B C : ℝ} (hBC : B ≤ C) :
    support N B = support N C ↔
      ¬ ∃ i, B ≤ HistoryHaarJointHessian.eigenvalue N i ∧
        HistoryHaarJointHessian.eigenvalue N i < C := by
  constructor
  · intro h ⟨i, hlo, hhi⟩
    have hi : i ∈ support N B := h ▸ (mem_support N C i).mpr hhi
    exact not_lt_of_ge hlo ((mem_support N B i).mp hi)
  · intro h
    apply Finset.Subset.antisymm (support_mono N hBC)
    intro i hi
    apply (mem_support N B i).mpr
    by_contra hnot
    exact h ⟨i, le_of_not_gt hnot, (mem_support N C i).mp hi⟩

/-- A spectral set can now be selected by the same observed level as the
Gaussian frequency window; no separate finite-set parameter is supplied. -/
def selectedCoefficient (N : ℕ) (R : ℝ) : ℝ :=
  HistoryGaussianWindowResponse.coefficient N R (support N R)

def selectedRoot (N : ℕ) (R : ℝ) : ℝ :=
  HistoryGaussianWindowResponse.responseRoot N R (support N R)

theorem selected_root_equation (N : ℕ) {R : ℝ} (hR : 0 < R)
    (hS : (support N R).Nonempty) :
    HistoryGaussianWindowResponse.response N R (support N R) (selectedRoot N R) =
      4 / 27 :=
  (HistoryGaussianWindowResponse.response_eq_iff N hR _ hS
    (HistoryGaussianWindowResponse.responseRoot_pos N hR _ hS)).mpr rfl

theorem selectedCoefficient_pos (N : ℕ) {R : ℝ}
    (hR : HistoryHaarJointHessian.gapSq N < R) :
    0 < selectedCoefficient N R := by
  have hp : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8)
    ((HistoryHaarJointHessian.gapSq_lower N).trans hR.le)
  exact HistoryGaussianWindowResponse.coefficient_pos N hp _
    ((support_nonempty_iff N R).mpr hR)

/-- The complete observed set is no longer an independent argument of
the root theorem: positivity is decided by the attained actual spectral edge. -/
theorem selected_root_unique (N : ℕ) {R : ℝ}
    (hR : HistoryHaarJointHessian.gapSq N < R) :
    ∃! c : ℝ, 0 < c ∧
      HistoryGaussianWindowResponse.response N R (support N R) c = 4 / 27 := by
  have hp : 0 < R := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 15 / 8)
    ((HistoryHaarJointHessian.gapSq_lower N).trans hR.le)
  exact HistoryGaussianWindowResponse.existsUnique_responseRoot N hp _
    ((support_nonempty_iff N R).mpr hR)

/-- Kinetic index of the original action. The homogeneous section has no
spatial derivative; its defining Casimir belongs to the restoring term. -/
def sourceEnergy (N : ℕ) : HistoryHaarJointHessian.Index N → ℝ :=
  Sum.elim (HistoryHaarClosedHessian.eigenvalue N) (fun _ => 0)

/-- The remaining vacuum response of the same original action. There is
no additional field mass in this vacuum Hessian. -/
def restoringEnergy (N : ℕ) : HistoryHaarJointHessian.Index N → ℝ :=
  Sum.elim (fun _ => 0) (fun _ => HistoryDefiningResponse.coefficient N)

theorem source_response_decomposition (N : ℕ)
    (i : HistoryHaarJointHessian.Index N) :
    HistoryHaarJointHessian.eigenvalue N i = sourceEnergy N i + restoringEnergy N i := by
  cases i <;> simp [HistoryHaarJointHessian.eigenvalue, sourceEnergy, restoringEnergy]

theorem sourceEnergy_nonneg (N : ℕ) (i : HistoryHaarJointHessian.Index N) :
    0 ≤ sourceEnergy N i := by
  cases i with
  | inl a => exact (HistoryHaarJointHessian.eigenvalue_pos N (.inl a)).le
  | inr a => exact le_refl 0

theorem restoringEnergy_nonneg (N : ℕ) (i : HistoryHaarJointHessian.Index N) :
    0 ≤ restoringEnergy N i := by
  cases i with
  | inl a => exact le_refl 0
  | inr a => exact (HistoryDefiningResponse.coefficient_pos N).le

/-- Complete source-frequency support. Unlike `support`, this is not a
cutoff of the full Hessian: the restoring index is not a kinetic frequency. -/
def sourceSupport (N : ℕ) (B : ℝ) : Finset (HistoryHaarJointHessian.Index N) := by
  classical
  exact (jointCandidates N (enumerationBound B)).filter fun i => sourceEnergy N i < B

@[simp] theorem mem_sourceSupport (N : ℕ) (B : ℝ)
    (i : HistoryHaarJointHessian.Index N) :
    i ∈ sourceSupport N B ↔ sourceEnergy N i < B := by
  classical
  simp only [sourceSupport, Finset.mem_filter]
  refine ⟨And.right, fun h => ⟨?_, h⟩⟩
  cases i with
  | inl a => exact cutoff_mem_candidates N B (.inl a) h
  | inr a => simp [jointCandidates]

theorem sourceSupport_unique (N : ℕ) (B : ℝ)
    (S : Finset (HistoryHaarJointHessian.Index N))
    (hS : ∀ i, i ∈ S ↔ sourceEnergy N i < B) : S = sourceSupport N B := by
  ext i
  exact (hS i).trans (mem_sourceSupport N B i).symm

/-- All actual state coordinates are visible at positive source bandwidth.
This theorem has no upper bound on the defining response coefficient. -/
theorem state_mem_sourceSupport (N : ℕ) {B : ℝ} (hB : 0 < B)
    (i : HistoryCliffordAction.Index N) :
    Sum.inr i ∈ sourceSupport N B := by
  rw [mem_sourceSupport]
  exact hB

theorem sourceSupport_nonempty_iff (N : ℕ) (B : ℝ) :
    (sourceSupport N B).Nonempty ↔ 0 < B := by
  constructor
  · rintro ⟨i, hi⟩
    exact lt_of_le_of_lt (sourceEnergy_nonneg N i) ((mem_sourceSupport N B i).mp hi)
  · intro h
    exact ⟨.inr (HistoryCliffordAction.historyPoint N, Sum.inl 0),
      state_mem_sourceSupport N h _⟩

theorem hessian_support_subset_sourceSupport (N : ℕ) (B : ℝ) :
    support N B ⊆ sourceSupport N B := by
  intro i hi
  rw [mem_sourceSupport]
  have h := (mem_support N B i).mp hi
  rw [source_response_decomposition] at h
  linarith [restoringEnergy_nonneg N i]

/-- Kinetic momentum enters both the Gaussian and the numerator. The
complete original Hessian, including its restoring part, enters the
denominator. No branch or source coordinate is discarded. -/
def totalKernel (N : ℕ) (i : HistoryHaarJointHessian.Index N) (u : ℝ) : ℝ :=
  ((u ^ 2 + sourceEnergy N i) /
    (u ^ 2 + HistoryHaarJointHessian.eigenvalue N i)) ^ 2 *
      Real.exp (-(u ^ 2 + sourceEnergy N i))

theorem totalKernel_eq (N : ℕ) (i : HistoryHaarJointHessian.Index N) (u : ℝ) :
    totalKernel N i u =
      ((u ^ 2 + sourceEnergy N i) /
        (u ^ 2 + sourceEnergy N i + restoringEnergy N i)) ^ 2 *
          Real.exp (-(u ^ 2 + sourceEnergy N i)) := by
  rw [totalKernel, source_response_decomposition]
  congr 3; ring

theorem totalKernel_continuous (N : ℕ) (i : HistoryHaarJointHessian.Index N) :
    Continuous (totalKernel N i) := by
  have hd : ∀ u : ℝ, u ^ 2 + HistoryHaarJointHessian.eigenvalue N i ≠ 0 := by
    intro u
    exact ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (HistoryHaarJointHessian.eigenvalue_pos N i))
  unfold totalKernel
  fun_prop (disch := exact hd _)

theorem totalKernel_pos (N : ℕ) (i : HistoryHaarJointHessian.Index N)
    {u : ℝ} (hu : 0 < u) : 0 < totalKernel N i u :=
  mul_pos (sq_pos_of_pos (div_pos
    (add_pos_of_pos_of_nonneg (sq_pos_of_pos hu) (sourceEnergy_nonneg N i))
    (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (HistoryHaarJointHessian.eigenvalue_pos N i)))) (Real.exp_pos _)

/-- The massless field response is exactly the source Gaussian. -/
theorem totalKernel_field (N : ℕ) (i : HistoryHaarClosedHessian.BasisIndex N) (u : ℝ) :
    totalKernel N (.inl i) u =
      Real.exp (-(u ^ 2 + HistoryHaarClosedHessian.eigenvalue N i)) := by
  have hd : u ^ 2 + HistoryHaarClosedHessian.eigenvalue N i ≠ 0 :=
    ne_of_gt (add_pos_of_nonneg_of_pos (sq_nonneg u)
      (HistoryHaarJointHessian.eigenvalue_pos N (.inl i)))
  simp [totalKernel, sourceEnergy, HistoryHaarJointHessian.eigenvalue, hd]

theorem totalKernel_state (N : ℕ) (i : HistoryCliffordAction.Index N) (u : ℝ) :
    totalKernel N (.inr i) u = HistoryGaussianWindowResponse.kernel N (.inr i) u := by
  simp [totalKernel, sourceEnergy, HistoryGaussianWindowResponse.kernel]

/-- The source cutoff is `u^2 + sourceEnergy N i < R`; the restoring part
does not shorten the kinetic window. -/
def totalBranchIntegral (N : ℕ) (R : ℝ) (i : HistoryHaarJointHessian.Index N) : ℝ :=
  ∫ u in (0 : ℝ)..Real.sqrt (R - sourceEnergy N i),
    totalKernel N i u

theorem total_window_iff (N : ℕ) {R u : ℝ}
    (i : HistoryHaarJointHessian.Index N)
    (hi : sourceEnergy N i < R) (hu : 0 ≤ u) :
    u < Real.sqrt (R - sourceEnergy N i) ↔ u ^ 2 + sourceEnergy N i < R := by
  have hs := Real.sq_sqrt (sub_pos.mpr hi).le
  have hp := Real.sqrt_pos.mpr (sub_pos.mpr hi)
  constructor <;> intro h <;> nlinarith

theorem totalBranchIntegral_eq (N : ℕ) (R : ℝ)
    (i : HistoryHaarJointHessian.Index N) :
    totalBranchIntegral N R i = Real.exp (-sourceEnergy N i) *
      ∫ u in (0 : ℝ)..Real.sqrt (R - sourceEnergy N i),
        ((u ^ 2 + sourceEnergy N i) /
          (u ^ 2 + HistoryHaarJointHessian.eigenvalue N i)) ^ 2 * Real.exp (-u ^ 2) := by
  have he (u : ℝ) : totalKernel N i u = Real.exp (-sourceEnergy N i) *
      (((u ^ 2 + sourceEnergy N i) /
        (u ^ 2 + HistoryHaarJointHessian.eigenvalue N i)) ^ 2 * Real.exp (-u ^ 2)) := by
    simp only [totalKernel, neg_add, Real.exp_add]
    ring
  simp_rw [totalBranchIntegral, he, intervalIntegral.integral_const_mul]

/-- No spurious `exp(-mass)` weight or `R-mass` cutoff is inserted into
the homogeneous state's actual frequency response. -/
theorem totalBranchIntegral_state (N : ℕ) (R : ℝ)
    (i : HistoryCliffordAction.Index N) :
    totalBranchIntegral N R (.inr i) =
      HistoryGaussianWindowResponse.branchIntegral N R (.inr i) := by
  simp [totalBranchIntegral, sourceEnergy, totalKernel_state,
    HistoryGaussianWindowResponse.branchIntegral]

theorem totalBranchIntegral_pos (N : ℕ) {R : ℝ}
    (i : HistoryHaarJointHessian.Index N)
    (hi : sourceEnergy N i < R) :
    0 < totalBranchIntegral N R i := by
  exact intervalIntegral.intervalIntegral_pos_of_pos_on
    ((totalKernel_continuous N i).intervalIntegrable _ _)
    (fun u hu => totalKernel_pos N i hu.1) (Real.sqrt_pos.mpr (sub_pos.mpr hi))

theorem totalBranchIntegral_eq_zero (N : ℕ) {R : ℝ}
    (i : HistoryHaarJointHessian.Index N)
    (hi : R ≤ sourceEnergy N i) :
    totalBranchIntegral N R i = 0 := by
  simp [totalBranchIntegral, Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hi)]

def totalCoefficient (N : ℕ) (R : ℝ) : ℝ :=
  (∑ i ∈ sourceSupport N R, totalBranchIntegral N R i) /
    HistoryGaussianCovariance.componentCount N

theorem totalCoefficient_pos (N : ℕ) {R : ℝ}
    (hR : 0 < R) : 0 < totalCoefficient N R := by
  apply div_pos
  · exact Finset.sum_pos (fun i hi =>
      totalBranchIntegral_pos N i ((mem_sourceSupport N R i).mp hi))
      ((sourceSupport_nonempty_iff N R).mpr hR)
  · exact Nat.cast_pos.mpr (HistoryGaussianCovariance.componentCount_pos N)

def totalRoot (N : ℕ) (R : ℝ) : ℝ :=
  Geometry.SourceTensorResponse.endpointRoot (totalCoefficient N R)

def totalResponse (N : ℕ) (R c : ℝ) : ℝ := totalCoefficient N R / c

theorem totalRoot_pos (N : ℕ) {R : ℝ}
    (hR : 0 < R) : 0 < totalRoot N R :=
  Geometry.SourceTensorResponse.endpointRoot_pos (totalCoefficient_pos N hR)

theorem totalResponse_eq_iff (N : ℕ) {R : ℝ}
    (hR : 0 < R) {c : ℝ} (hc : 0 < c) :
    totalResponse N R c = 4 / 27 ↔ c = totalRoot N R := by
  simpa only [totalResponse, totalRoot,
    Geometry.SourceTensorResponse.endpointResidual, sub_eq_zero] using
    (Geometry.SourceTensorResponse.endpointResidual_eq_zero_iff
      (totalCoefficient_pos N hR) hc)

theorem total_root_unique (N : ℕ) {R : ℝ}
    (hR : 0 < R) :
    ∃! c : ℝ, 0 < c ∧ totalResponse N R c = 4 / 27 := by
  refine ⟨totalRoot N R, ⟨totalRoot_pos N hR, ?_⟩, ?_⟩
  · exact (totalResponse_eq_iff N hR (totalRoot_pos N hR)).mpr rfl
  · intro c hc
    exact (totalResponse_eq_iff N hR hc.1).mp hc.2

/-- Below `16` the positive field spectrum contains only the shell `4`,
as determined from both actual curl branches. This implication does not
assert the multiplicity or attainment of the next shell. -/
theorem hodge_lt_sixteen_iff (a : CoclosedIndex) :
    hodgeEigenvalue a < 16 ↔ hodgeEigenvalue a = 4 := by
  constructor
  · intro h
    obtain ⟨l, hlodd, hlpos, he⟩ :=
      every_nongauge_field_mode_has_odd_degree a.val a.property
    have hlr : (l : ℝ) < 3 := by
      change eigenvalue a.val ^ 2 < 16 at h
      rw [he] at h
      have hl0 : (0 : ℝ) ≤ l := Nat.cast_nonneg _
      nlinarith
    have hln : l < 3 := by exact_mod_cast hlr
    obtain ⟨k, hk⟩ := hlodd
    have hl : l = 1 := by omega
    change eigenvalue a.val ^ 2 = 4
    rw [he, hl]
    norm_num
  · intro h
    rw [h]
    norm_num

theorem field_first_shell (a : CoclosedIndex) {B : ℝ}
    (hlo : 4 < B) (hhi : B ≤ 16) :
    hodgeEigenvalue a < B ↔ hodgeEigenvalue a = 4 := by
  constructor
  · intro h
    exact (hodge_lt_sixteen_iff a).mp (lt_of_lt_of_le h hhi)
  · intro h
    simpa only [h] using hlo

/-- This is the actual joint first-shell formula, including the possibly
active homogeneous state. State inclusion is computed by its own eigenvalue. -/
theorem mem_support_first_shell (N : ℕ) {B : ℝ}
    (hlo : 4 < B) (hhi : B ≤ 16) (i : HistoryHaarJointHessian.Index N) :
    i ∈ support N B ↔
      Sum.elim (fun a => hodgeEigenvalue a.2 = 4)
        (fun _ => HistoryDefiningResponse.coefficient N < B) i := by
  rw [mem_support]
  cases i with
  | inl a => exact field_first_shell a.2 hlo hhi
  | inr a => rfl

/-- The source shell includes the entire homogeneous state, independently
of its restoring coefficient. Only the field shell is cut at `B`. -/
theorem mem_sourceSupport_first_shell (N : ℕ) {B : ℝ}
    (hlo : 4 < B) (hhi : B ≤ 16) (i : HistoryHaarJointHessian.Index N) :
    i ∈ sourceSupport N B ↔
      Sum.elim (fun a => hodgeEigenvalue a.2 = 4) (fun _ => True) i := by
  rw [mem_sourceSupport]
  cases i with
  | inl a => exact field_first_shell a.2 hlo hhi
  | inr a =>
    change 0 < B ↔ True
    exact iff_true_intro (lt_trans (by norm_num) hlo)

/-- Exact content of the homogeneous part of a source-frequency window. -/
theorem state_sourceSupport_eq (N : ℕ) {B : ℝ} (hB : 0 < B) :
    (sourceSupport N B).filter (fun i => i.isRight = true) =
      (Finset.univ : Finset (HistoryCliffordAction.Index N)).image Sum.inr := by
  classical
  ext i
  cases i <;> simp [mem_sourceSupport, sourceEnergy, hB]

theorem state_sourceSupport_card (N : ℕ) {B : ℝ} (hB : 0 < B) :
    ((sourceSupport N B).filter (fun i => i.isRight = true)).card =
      HistoryAdjointCasimir.dimension N := by
  classical
  rw [state_sourceSupport_eq N hB, Finset.card_image_of_injective _ Sum.inr_injective]
  rfl

/-- Positive arithmetic positions are roots `1,...,m`, not a supplied
number of physical matter generations. -/
def RootPlateau (m : ℕ) (B : ℝ) : Prop :=
  (m : ℝ) ^ 2 < B ∧ B ≤ ((m : ℝ) + 1) ^ 2

theorem root_plateau_iff (m : ℕ) {B : ℝ} (hB : 0 < B) :
    RootPlateau m B ↔ ∀ n : ℕ, 0 < n → ((n : ℝ) ^ 2 < B ↔ n ≤ m) := by
  constructor
  · rintro ⟨hlo, hhi⟩ n hn
    constructor
    · intro h
      by_contra hnot
      have hm : m + 1 ≤ n := by omega
      have hmr : (m : ℝ) + 1 ≤ n := by exact_mod_cast hm
      have hmp : 0 ≤ (m : ℝ) + 1 := by positivity
      nlinarith
    · intro h
      have hnm : (n : ℝ) ≤ m := by exact_mod_cast h
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
  · intro h
    constructor
    · by_cases hm : m = 0
      · subst m
        simpa using hB
      · exact (h m (Nat.pos_of_ne_zero hm)).mpr le_rfl
    · have hn := (h (m + 1) (by omega)).not.mpr (by omega)
      push_cast at hn
      exact le_of_not_gt hn

/-- The position projection retains the original histories, their finite
phases and their four source coordinates. -/
def rootSupport (N : ℕ) (B : ℝ) : Finset (HistoryCliffordAction.Index N) := by
  classical
  exact Finset.univ.filter fun i => HistoryGaussianConnection.rootEnergy N i < B

theorem mem_rootSupport_iff (N m : ℕ) {B : ℝ} (h : RootPlateau m B)
    (i : HistoryCliffordAction.Index N) :
    i ∈ rootSupport N B ↔ i.1.1.val + 1 ≤ m := by
  classical
  rw [rootSupport, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  exact (root_plateau_iff m (lt_of_le_of_lt (sq_nonneg _) h.1)).mp h
    (i.1.1.val + 1) (by omega)

/-- Position selection changes a root set, never the contents of a root
fibre. In particular it is not an average over histories or source signs. -/
theorem rootSupport_eq (N m : ℕ) {B : ℝ} (h : RootPlateau m B) :
    rootSupport N B = Finset.univ.filter (fun i => i.1.1.val + 1 ≤ m) := by
  classical
  ext i
  simp only [mem_rootSupport_iff N m h, Finset.mem_filter,
    Finset.mem_univ, true_and]

/-- The retained root positions in a finite source prefix are counted from
the actual square spectrum. The strict cutoff fixes both boundary directions. -/
theorem retained_roots (N m : ℕ) {B : ℝ} (h : RootPlateau m B) :
    (Finset.univ.filter fun n : Fin (N + 1) => ((n.val + 1 : ℕ) : ℝ) ^ 2 < B) =
      Finset.univ.filter (fun n : Fin (N + 1) => n.val + 1 ≤ m) := by
  classical
  ext n
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact (root_plateau_iff m (lt_of_le_of_lt (sq_nonneg _) h.1)).mp h
    (n.val + 1) (by omega)

/-- The shared positive spinor positions are a different spectrum from
the arithmetic roots. Keeping this map explicit prevents replacing a
calculated arithmetic count by the physical generation count. -/
def spinorPosition (j : ℕ) : ℝ :=
  Geometry.SourceFieldSpectrum.diracMagnitude 1 (2 * j)

theorem spinorPosition_eq (j : ℕ) : spinorPosition j = 2 * (j : ℝ) + 3 / 2 := by
  simp [spinorPosition, Geometry.SourceFieldSpectrum.diracMagnitude]

theorem spinorPosition_injective : Function.Injective spinorPosition := by
  intro j k h
  simp only [spinorPosition_eq] at h
  have he : (j : ℝ) = k := by linarith
  exact_mod_cast he

/-- Every displayed position is present in the original closed, centre-even
Dirac operator. This links the formula to an actual field eigenvector. -/
theorem spinorPosition_realized (j : ℕ) :
    ∃ a : Geometry.SourceSpinorParitySpectrum.Index false,
      Geometry.SourceSpinorClosedSpectrum.eigenvalue a.val = spinorPosition j := by
  have he : (-1 : ℂ) ^ (2 * j) = Geometry.SourceSpinorParitySpectrum.sign false := by
    simp [pow_mul, Geometry.SourceSpinorParitySpectrum.sign]
  obtain ⟨a, ha⟩ := (Geometry.SourceSpinorParityResolvent.positive_label false (2 * j)).mpr he
  exact ⟨a, by simpa [spinorPosition_eq] using ha⟩

/-- No other positive positions occur in that closed sector. Full basis
labels and their multiplicities are retained; only their eigenvalues are
coordinatized by `j`. Source parity is not prime-occupation parity. -/
theorem spinorPosition_exhausts (a : Geometry.SourceSpinorParitySpectrum.Index false)
    (ha : 0 < Geometry.SourceSpinorClosedSpectrum.eigenvalue a.val) :
    ∃ j : ℕ, Geometry.SourceSpinorClosedSpectrum.eigenvalue a.val = spinorPosition j := by
  obtain ⟨k, hp | hn⟩ := Geometry.SourceSpinorResolvent.eigenvalue_is_half_integer a.val
  · have hk : (-1 : ℂ) ^ k = 1 := by
      simpa [Geometry.SourceSpinorParitySpectrum.sign] using
        (Geometry.SourceSpinorParityResolvent.positive_label false k).mp ⟨a, hp⟩
    obtain ⟨j, hj⟩ := (neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℂ) ≠ 1)).mp hk
    refine ⟨j, ?_⟩
    rw [hp, hj, spinorPosition_eq]
    push_cast
    ring
  · have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    rw [hn] at ha
    linarith

theorem spinor_plateau_iff (m : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    (2 * (m : ℝ) - 1 / 2 < B ∧ B ≤ 2 * (m : ℝ) + 3 / 2) ↔
      ∀ j : ℕ, spinorPosition j < B ↔ j < m := by
  simp only [spinorPosition_eq]
  constructor
  · rintro ⟨hlo, hhi⟩ j
    constructor
    · intro hj
      by_contra hn
      have hnj : m ≤ j := Nat.le_of_not_gt hn
      have hr : (m : ℝ) ≤ j := by exact_mod_cast hnj
      linarith
    · intro hj
      have hnj : j + 1 ≤ m := hj
      have hr : (j : ℝ) + 1 ≤ m := by exact_mod_cast hnj
      linarith
  · intro h
    constructor
    · by_cases hm : m = 0
      · subst m
        norm_num
        linarith
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
        have hlt : m - 1 < m := by omega
        have hh := (h (m - 1)).mpr hlt
        rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one] at hh
        linarith
    · have hh := (h m).not.mpr (lt_irrefl m)
      exact le_of_not_gt hh

/-- This recovers the physical three-position test on the common spinor
tower without importing the physical branch or imposing that count on
the arithmetic root spectrum. The upper boundary is included. -/
theorem three_spinor_positions_iff (c : ℝ) :
    (∀ j : ℕ, spinorPosition j < c ^ 2 ↔ j < 3) ↔
      11 / 2 < c ^ 2 ∧ c ^ 2 ≤ 15 / 2 := by
  have h := spinor_plateau_iff 3 (sq_nonneg c)
  norm_num only [Nat.cast_ofNat] at h
  convert h.symm using 1

/-- Jointly checking a discrete observation means checking its complete
spectral support, its actual root-position plateau and its response equation.
The position count is an output to be constrained by an arithmetic content
theorem; it is not preset to three. -/
def CompatibleObservation (N R m : ℕ) : Prop :=
  0 < R ∧ (sourceSupport N (R : ℝ)).Nonempty ∧
    RootPlateau m (totalRoot N (R : ℝ) ^ 2)

theorem compatible_observation_spec (N R m : ℕ)
    (h : CompatibleObservation N R m) :
    totalResponse N (R : ℝ) (totalRoot N (R : ℝ)) = 4 / 27 ∧
      (∀ i, i ∈ sourceSupport N (R : ℝ) ↔ sourceEnergy N i < (R : ℝ)) ∧
      (∀ i, i ∈ rootSupport N (totalRoot N (R : ℝ) ^ 2) ↔
        i.1.1.val + 1 ≤ m) := by
  have hR : (0 : ℝ) < R := by exact_mod_cast h.1
  exact ⟨(totalResponse_eq_iff N hR (totalRoot_pos N hR)).mpr rfl,
    mem_sourceSupport N (R : ℝ), mem_rootSupport_iff N m h.2.2⟩

structure Conclusions : Prop where
  actual_support : ∀ N B i,
    i ∈ support N B ↔ HistoryHaarJointHessian.eigenvalue N i < B
  unique_support : ∀ N B S,
    (∀ i, i ∈ S ↔ HistoryHaarJointHessian.eigenvalue N i < B) → S = support N B
  attained_activation : ∀ N B,
    (support N B).Nonempty ↔ HistoryHaarJointHessian.gapSq N < B
  first_field_shell : ∀ N B, 4 < B → B ≤ 16 → ∀ i,
    i ∈ support N B ↔
      Sum.elim (fun a => hodgeEigenvalue a.2 = 4)
        (fun _ => HistoryDefiningResponse.coefficient N < B) i
  selected_response : ∀ N R, HistoryHaarJointHessian.gapSq N < R →
    ∃! c : ℝ, 0 < c ∧
      HistoryGaussianWindowResponse.response N R (support N R) c = 4 / 27
  total_frequency_domain : ∀ N R i,
    sourceEnergy N i < R → ∀ u, 0 ≤ u →
      (u < Real.sqrt (R - sourceEnergy N i) ↔ u ^ 2 + sourceEnergy N i < R)
  kinetic_restoring_decomposition : ∀ N i,
    HistoryHaarJointHessian.eigenvalue N i = sourceEnergy N i + restoringEnergy N i
  complete_source_support : ∀ N B i,
    i ∈ sourceSupport N B ↔ sourceEnergy N i < B
  complete_source_state : ∀ N B, 0 < B →
    ((sourceSupport N B).filter (fun i => i.isRight = true)).card =
      HistoryAdjointCasimir.dimension N
  total_response : ∀ N R, 0 < R →
    ∃! c : ℝ, 0 < c ∧ totalResponse N R c = 4 / 27
  complete_position_fibres : ∀ N m B, RootPlateau m B → ∀ i,
    i ∈ rootSupport N B ↔ i.1.1.val + 1 ≤ m
  shared_spinor_positions : ∀ (m : ℕ) (B : ℝ), 0 ≤ B →
    ((2 * (m : ℝ) - 1 / 2 < B ∧ B ≤ 2 * (m : ℝ) + 3 / 2) ↔
      ∀ j : ℕ, spinorPosition j < B ↔ j < m)
  actual_spinor_position_presence : ∀ j,
    ∃ a : Geometry.SourceSpinorParitySpectrum.Index false,
      Geometry.SourceSpinorClosedSpectrum.eigenvalue a.val = spinorPosition j
  actual_spinor_position_exhaustion : ∀ a : Geometry.SourceSpinorParitySpectrum.Index false,
    0 < Geometry.SourceSpinorClosedSpectrum.eigenvalue a.val →
      ∃ j : ℕ, Geometry.SourceSpinorClosedSpectrum.eigenvalue a.val = spinorPosition j

theorem generated : Conclusions where
  actual_support := mem_support
  unique_support := support_unique
  attained_activation := support_nonempty_iff
  first_field_shell := fun N _ hlo hhi => mem_support_first_shell N hlo hhi
  selected_response := fun N _ hR => selected_root_unique N hR
  total_frequency_domain := fun N _ i hi _ hu => total_window_iff N i hi hu
  kinetic_restoring_decomposition := source_response_decomposition
  complete_source_support := mem_sourceSupport
  complete_source_state := fun N _ hB => state_sourceSupport_card N hB
  total_response := fun N _ hR => total_root_unique N hR
  complete_position_fibres := fun N m _ h => mem_rootSupport_iff N m h
  shared_spinor_positions := fun m _ hB => spinor_plateau_iff m hB
  actual_spinor_position_presence := spinorPosition_realized
  actual_spinor_position_exhaustion := spinorPosition_exhausts

end GeneratedFoundations.Arithmetic.HistorySpectralWindow
