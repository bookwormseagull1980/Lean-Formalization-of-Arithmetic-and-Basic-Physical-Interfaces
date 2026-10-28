module

public import GeneratedFoundations.Analysis.HistoryPrefixBirthResponse

/-!
# Subset observations in the unchanged positive Gaussian prefix

A finite root set restricts observations, not the source state. All roots,
history fibres and phase fibres remain in `HistoryPrefixGibbsResponse`.
The subset mean is removed inside the same response metric, and restoring
the full partition yields the exact capacity-weighted conditional covariance.
The complement retains its original positive mass.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Analysis.HistoryPrefixSubsetResponse

open Arithmetic Arithmetic.CompleteHistory
open Operations Operations.PreparedTraceForm
open HistoryPrefixGibbsResponse
open HistoryPrefixBirthResponse (rootObservation rootMean weighted_rootMean)

def moment (alpha L : ℝ) (S : Finset ℕ) (f : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S, gaussianRootMass alpha L n * f n

def capacity (alpha L : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, gaussianRootMass alpha L n

def restricted (N : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) (i : Index N) : ℝ := by
  classical
  exact if i.1.val + 1 ∈ S then f (i.1.val + 1) else 0

theorem sum_positive_roots (N : ℕ) (f : ℕ → ℝ) :
    (∑ b : Fin (N + 1), f (b.val + 1)) =
      ∑ n ∈ SignedGaussianEnergy.rootRange (N + 1), f n := by
  classical
  refine Finset.sum_bij (fun b _ => b.val + 1) ?_ ?_ ?_ ?_
  · intro b _
    simp only [SignedGaussianEnergy.rootRange, Finset.mem_Icc]
    have hb := b.isLt
    omega
  · intro a _ b _ hab
    apply Fin.ext
    omega
  · intro n hn
    simp only [SignedGaussianEnergy.rootRange, Finset.mem_Icc] at hn
    refine ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, ?_⟩
    dsimp
    omega
  · intro b _
    rfl

theorem capacity_nonneg (alpha L : ℝ) (S : Finset ℕ) : 0 ≤ capacity alpha L S :=
  Finset.sum_nonneg fun n _ => (gaussianRootMass_pos alpha L n).le

theorem capacity_pos (alpha L : ℝ) {S : Finset ℕ} (hS : S.Nonempty) :
    0 < capacity alpha L S :=
  Finset.sum_pos (fun n _ => gaussianRootMass_pos alpha L n) hS

@[simp] theorem moment_one (alpha L : ℝ) (S : Finset ℕ) :
    moment alpha L S (fun _ => 1) = capacity alpha L S := by
  simp [moment, capacity]

theorem weighted_restricted (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1)) (f : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) * mean N alpha L (restricted N S f) =
      moment alpha L S f := by
  classical
  change GibbsTraceForm.Z (logIntensity N alpha L) *
    rootMean N alpha L (fun n => if n ∈ S then f n else 0) = _
  rw [weighted_rootMean,
    sum_positive_roots N (fun n => gaussianRootMass alpha L n * (if n ∈ S then f n else 0))]
  simp only [mul_ite, mul_zero]
  change (∑ n ∈ SignedGaussianEnergy.rootRange (N + 1),
    if n ∈ S then gaussianRootMass alpha L n * f n else 0) = _
  rw [← Finset.sum_filter]
  congr 1
  exact Finset.filter_mem_eq_inter.trans (Finset.inter_eq_right.mpr hS)

theorem mean_restricted (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1)) (f : ℕ → ℝ) :
    mean N alpha L (restricted N S f) =
      moment alpha L S f / GibbsTraceForm.Z (logIntensity N alpha L) := by
  apply (eq_div_iff (GibbsTraceForm.Z_ne_zero _)).mpr
  simpa only [mul_comm] using weighted_restricted N alpha L S hS f

theorem restricted_mul (N : ℕ) (S : Finset ℕ) (f g : ℕ → ℝ) :
    (fun i => restricted N S f i * restricted N S g i) =
      restricted N S (fun n => f n * g n) := by
  classical
  funext i
  by_cases h : i.1.val + 1 ∈ S <;> simp [restricted, h]

theorem restricted_hessian (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1)) (f g : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (diagonalObservation (restricted N S f)) (diagonalObservation (restricted N S g)) =
        moment alpha L S (fun n => f n * g n) / GibbsTraceForm.Z (logIntensity N alpha L) -
          (moment alpha L S f / GibbsTraceForm.Z (logIntensity N alpha L)) *
            (moment alpha L S g / GibbsTraceForm.Z (logIntensity N alpha L)) := by
  rw [hessian_covariance, restricted_mul, mean_restricted N alpha L S hS,
    mean_restricted N alpha L S hS, mean_restricted N alpha L S hS]

def centeredRoot (alpha L : ℝ) (S : Finset ℕ) (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  f n - moment alpha L S f / capacity alpha L S

def centeredObservation (N : ℕ) (alpha L : ℝ) (S : Finset ℕ) (f : ℕ → ℝ) :
    Hermitian (Index N) := diagonalObservation (restricted N S (centeredRoot alpha L S f))

theorem centered_moment (alpha L : ℝ) (S : Finset ℕ) (f : ℕ → ℝ)
    (hC : capacity alpha L S ≠ 0) :
    moment alpha L S (centeredRoot alpha L S f) = 0 := by
  simp only [moment, centeredRoot, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change moment alpha L S f - capacity alpha L S *
    (moment alpha L S f / capacity alpha L S) = 0
  rw [mul_div_cancel₀ _ hC, sub_self]

theorem centered_pair_moment (alpha L : ℝ) (S : Finset ℕ) (f g : ℕ → ℝ)
    (hC : capacity alpha L S ≠ 0) :
    moment alpha L S (fun n => centeredRoot alpha L S f n * centeredRoot alpha L S g n) =
      moment alpha L S (fun n => f n * g n) -
        moment alpha L S f * moment alpha L S g / capacity alpha L S := by
  have he : ∀ n, gaussianRootMass alpha L n *
      (centeredRoot alpha L S f n * centeredRoot alpha L S g n) =
      gaussianRootMass alpha L n * (f n * g n) -
      gaussianRootMass alpha L n * f n * (moment alpha L S g / capacity alpha L S) -
      gaussianRootMass alpha L n * g n * (moment alpha L S f / capacity alpha L S) +
      gaussianRootMass alpha L n *
        ((moment alpha L S f / capacity alpha L S) * (moment alpha L S g / capacity alpha L S)) :=
    fun n => by unfold centeredRoot; ring
  simp only [moment, he, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  change moment alpha L S (fun n => f n * g n) - _ - _ +
    capacity alpha L S * _ = _
  simp only [moment]
  field_simp [hC]
  ring

/-- A response on a subset is evaluated in the original full state.
Its actual capacity, rather than one, is recovered after normalization. -/
theorem restored_centered_hessian (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1))
    (hC : capacity alpha L S ≠ 0) (f g : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) *
      fderiv ℝ (fderiv ℝ (response N alpha L)) 0
        (centeredObservation N alpha L S f) (centeredObservation N alpha L S g) =
      moment alpha L S (fun n => f n * g n) -
        moment alpha L S f * moment alpha L S g / capacity alpha L S := by
  unfold centeredObservation
  rw [restricted_hessian N alpha L S hS, centered_moment alpha L S f hC,
    centered_moment alpha L S g hC, zero_div, zero_mul, sub_zero,
    mul_div_cancel₀ _ (GibbsTraceForm.Z_ne_zero _), centered_pair_moment alpha L S f g hC]

theorem centered_support_orthogonal (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1))
    (hC : capacity alpha L S ≠ 0) (f : ℕ → ℝ) :
    fderiv ℝ (fderiv ℝ (response N alpha L)) 0
      (centeredObservation N alpha L S f) (diagonalObservation (restricted N S (fun _ => 1))) = 0 := by
  unfold centeredObservation
  rw [restricted_hessian N alpha L S hS]
  simp only [mul_one, centered_moment alpha L S f hC, zero_div, zero_mul, sub_self]

/-- The complete restricted response retains the support/complement square.
Centering is an orthogonal reduction in the same full-source Hessian. -/
theorem retained_support_response (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1))
    (hC : capacity alpha L S ≠ 0) (f g : ℕ → ℝ) :
    GibbsTraceForm.Z (logIntensity N alpha L) *
      fderiv ℝ (fderiv ℝ (response N alpha L)) 0
        (diagonalObservation (restricted N S f)) (diagonalObservation (restricted N S g)) =
      GibbsTraceForm.Z (logIntensity N alpha L) *
        fderiv ℝ (fderiv ℝ (response N alpha L)) 0
          (centeredObservation N alpha L S f) (centeredObservation N alpha L S g) +
        (GibbsTraceForm.Z (logIntensity N alpha L) - capacity alpha L S) /
          (capacity alpha L S * GibbsTraceForm.Z (logIntensity N alpha L)) *
            moment alpha L S f * moment alpha L S g := by
  rw [restricted_hessian N alpha L S hS, restored_centered_hessian N alpha L S hS hC]
  field_simp [hC, GibbsTraceForm.Z_ne_zero (logIntensity N alpha L)]
  ring

theorem complete_capacity_partition (N : ℕ) (alpha L : ℝ) (S : Finset ℕ)
    (hS : S ⊆ SignedGaussianEnergy.rootRange (N + 1)) :
    capacity alpha L S +
        capacity alpha L (SignedGaussianEnergy.rootRange (N + 1) \ S) =
      GibbsTraceForm.Z (logIntensity N alpha L) := by
  rw [partition_eq_prefix, sum_positive_roots]
  unfold capacity
  rw [← Finset.sum_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset hS]

end GeneratedFoundations.Analysis.HistoryPrefixSubsetResponse
