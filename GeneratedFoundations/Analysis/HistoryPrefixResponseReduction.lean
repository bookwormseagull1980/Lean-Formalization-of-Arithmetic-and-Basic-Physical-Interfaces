module

public import GeneratedFoundations.Analysis.HistoryPrefixGibbsResponse

/-!
# Exact reduction in the actual Gaussian prefix Hessian

The response metric belongs to the complete root--history--phase prefix.
All matrix entries, including cross-root entries, occur before any direction
is removed. Orthogonal elimination retains its exact squared response term.
The scalar-kernel case is included and supplies no spurious inverse.

The eliminated direction is an observation of the existing source. It is
neither a new source nor an independently chosen physical realization.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.HistoryPrefixResponseReduction

open Operations Operations.PreparedTraceForm
open HistoryPrefixGibbsResponse

def form (N : ℕ) (alpha L : ℝ) : LinearMap.BilinForm ℝ (Hermitian (Index N)) :=
  GibbsTraceForm.hermitianForm (logIntensity N alpha L)

theorem form_hessian (N : ℕ) (alpha L : ℝ) (K J : Hermitian (Index N)) :
    form N alpha L K J = fderiv ℝ (fderiv ℝ (response N alpha L)) 0 K J :=
  (full_hessian N alpha L K J).symm

theorem form_symmetric (N : ℕ) (alpha L : ℝ) (K J : Hermitian (Index N)) :
    form N alpha L K J = form N alpha L J K :=
  GibbsTraceForm.gibbsForm_symm _ _ _

theorem form_nonneg (N : ℕ) (alpha L : ℝ) (K : Hermitian (Index N)) :
    0 ≤ form N alpha L K K := by
  rw [form_hessian]
  exact hessian_nonneg N alpha L K

theorem null_mixed (N : ℕ) (alpha L : ℝ) (J : Hermitian (Index N))
    (hJ : form N alpha L J J = 0) (K : Hermitian (Index N)) :
    form N alpha L J K = 0 := by
  change GibbsTraceForm.gibbsForm (logIntensity N alpha L)
    (J : Mat (Index N)) (J : Mat (Index N)) = 0 at hJ
  have hs := (GibbsTraceForm.gibbsForm_self_eq_zero_iff
    (logIntensity N alpha L) (hermitian_isHermitian (Index N) J)).mp hJ
  exact (GibbsTraceForm.gibbsForm_kernel_iff (logIntensity N alpha L) J).mpr hs K

def coefficient {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) : ℝ :=
  form N alpha L K J / form N alpha L J J

def residual {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) : Hermitian (Index N) :=
  K - coefficient alpha L K J • J

theorem reconstruction {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) :
    K = residual alpha L K J + coefficient alpha L K J • J := by
  simp [residual]

theorem residual_orthogonal {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) :
    form N alpha L J (residual alpha L K J) = 0 := by
  by_cases hJ : form N alpha L J J = 0
  · exact null_mixed N alpha L J hJ _
  · simp only [residual, map_sub, map_smul, smul_eq_mul]
    rw [form_symmetric N alpha L J K]
    unfold coefficient
    field_simp [hJ]
    ring

/-- Exact squared response of the removed direction, in the same metric. -/
theorem schur_identity {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) :
    form N alpha L K K =
      form N alpha L (residual alpha L K J) (residual alpha L K J) +
        form N alpha L K J ^ 2 / form N alpha L J J := by
  have he : form N alpha L (residual alpha L K J) (residual alpha L K J) =
      form N alpha L K K -
        2 * coefficient alpha L K J * form N alpha L K J +
        coefficient alpha L K J ^ 2 * form N alpha L J J := by
    simp only [residual, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [form_symmetric N alpha L J K]
    ring
  rw [he]
  by_cases hJ : form N alpha L J J = 0
  · simp [coefficient, hJ]
  · unfold coefficient
    field_simp [hJ]
    ring

theorem residual_energy_le {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) :
    form N alpha L (residual alpha L K J) (residual alpha L K J) ≤
      form N alpha L K K := by
  have he := schur_identity alpha L K J
  have hn := div_nonneg (sq_nonneg (form N alpha L K J)) (form_nonneg N alpha L J)
  linarith

/-- The removed direction is optimized in the actual complete response
metric, including its zero-curvature case. -/
theorem shifted_square {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) (q : ℝ) :
    form N alpha L (K - q • J) (K - q • J) =
      form N alpha L (residual alpha L K J) (residual alpha L K J) +
        form N alpha L J J * (coefficient alpha L K J - q) ^ 2 := by
  have he : K - q • J = residual alpha L K J + (coefficient alpha L K J - q) • J := by
    unfold residual
    module
  have hl := residual_orthogonal alpha L K J
  have hr : form N alpha L (residual alpha L K J) J = 0 := by
    rw [form_symmetric]
    exact hl
  rw [he]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hl, hr]
  ring

theorem residual_minimality {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)) (q : ℝ) :
    form N alpha L (residual alpha L K J) (residual alpha L K J) ≤
      form N alpha L (K - q • J) (K - q • J) := by
  rw [shifted_square]
  exact le_add_of_nonneg_right (mul_nonneg (form_nonneg N alpha L J) (sq_nonneg _))

theorem unique_coefficient {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N))
    (hJ : form N alpha L J J ≠ 0) :
    ∃! q : ℝ, form N alpha L J (K - q • J) = 0 := by
  refine ⟨coefficient alpha L K J, residual_orthogonal alpha L K J, ?_⟩
  intro q hq
  simp only [map_sub, map_smul, smul_eq_mul] at hq
  rw [form_symmetric N alpha L J K] at hq
  unfold coefficient
  apply (eq_div_iff hJ).mpr
  linarith

structure Conclusions : Prop where
  complete_reconstruction : ∀ {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)),
    K = residual alpha L K J + coefficient alpha L K J • J
  orthogonal_response : ∀ {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)),
    form N alpha L J (residual alpha L K J) = 0
  retained_response : ∀ {N : ℕ} (alpha L : ℝ) (K J : Hermitian (Index N)),
    form N alpha L K K =
      form N alpha L (residual alpha L K J) (residual alpha L K J) +
        form N alpha L K J ^ 2 / form N alpha L J J

theorem generated : Conclusions where
  complete_reconstruction := reconstruction
  orthogonal_response := residual_orthogonal
  retained_response := schur_identity

end GeneratedFoundations.Analysis.HistoryPrefixResponseReduction
