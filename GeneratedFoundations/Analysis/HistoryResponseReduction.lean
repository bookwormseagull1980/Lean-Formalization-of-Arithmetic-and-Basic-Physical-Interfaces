module

public import GeneratedFoundations.Analysis.HistoryGibbsResponse

/-!
# Exact Schur reduction of the complete history response

The form is the actual connected Hermitian Hessian of the positive Gaussian
history source. An observation direction may contain every off-diagonal
matrix entry. Its Schur coefficient and retained residual use this form,
not the unweighted coefficient inner product. The zero-direction case is
also covered: the proved scalar kernel makes its mixed response vanish.

The reduction is an observation operation on an already generated source.
Neither the direction nor its positivity is an input to the root theorem.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Analysis.HistoryResponseReduction

open Operations Operations.PreparedTraceForm
open HistoryGibbsResponse

def form (n : ℕ) (alpha L : ℝ) : LinearMap.BilinForm ℝ (Hermitian (Index n)) :=
  GibbsTraceForm.hermitianForm (logIntensity n alpha L)

theorem form_hessian (n : ℕ) (alpha L : ℝ) (K J : Hermitian (Index n)) :
    form n alpha L K J = fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J :=
  (full_hessian n alpha L K J).symm

theorem form_symmetric (n : ℕ) (alpha L : ℝ) (K J : Hermitian (Index n)) :
    form n alpha L K J = form n alpha L J K :=
  GibbsTraceForm.gibbsForm_symm _ _ _

theorem form_nonneg (n : ℕ) (alpha L : ℝ) (K : Hermitian (Index n)) :
    0 ≤ form n alpha L K K := by
  rw [form_hessian]
  exact hessian_nonneg n alpha L K

theorem null_mixed (n : ℕ) (alpha L : ℝ) (J : Hermitian (Index n))
    (hJ : form n alpha L J J = 0) (K : Hermitian (Index n)) :
    form n alpha L J K = 0 := by
  change GibbsTraceForm.gibbsForm (logIntensity n alpha L)
    (J : Mat (Index n)) (J : Mat (Index n)) = 0 at hJ
  have hs := (GibbsTraceForm.gibbsForm_self_eq_zero_iff
    (logIntensity n alpha L) (hermitian_isHermitian (Index n) J)).mp hJ
  exact (GibbsTraceForm.gibbsForm_kernel_iff (logIntensity n alpha L) J).mpr hs K

def coefficient {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)) : ℝ :=
  form n alpha L K J / form n alpha L J J

def residual {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)) : Hermitian (Index n) :=
  K - coefficient alpha L K J • J

theorem reconstruction {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)) :
    K = residual alpha L K J + coefficient alpha L K J • J := by
  simp [residual]

theorem residual_orthogonal {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)) :
    form n alpha L J (residual alpha L K J) = 0 := by
  by_cases hJ : form n alpha L J J = 0
  · exact null_mixed n alpha L J hJ _
  · simp only [residual, map_sub, map_smul, smul_eq_mul]
    rw [form_symmetric n alpha L J K]
    unfold coefficient
    field_simp [hJ]
    ring

theorem schur_identity {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)) :
    form n alpha L K K =
      form n alpha L (residual alpha L K J) (residual alpha L K J) +
        form n alpha L K J ^ 2 / form n alpha L J J := by
  have he : form n alpha L (residual alpha L K J) (residual alpha L K J) =
      form n alpha L K K -
        2 * coefficient alpha L K J * form n alpha L K J +
        coefficient alpha L K J ^ 2 * form n alpha L J J := by
    simp only [residual, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [form_symmetric n alpha L J K]
    ring
  rw [he]
  by_cases hJ : form n alpha L J J = 0
  · simp [coefficient, hJ]
  · unfold coefficient
    field_simp [hJ]
    ring

theorem residual_energy_le {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)) :
    form n alpha L (residual alpha L K J) (residual alpha L K J) ≤
      form n alpha L K K := by
  have he := schur_identity alpha L K J
  have hn := div_nonneg (sq_nonneg (form n alpha L K J)) (form_nonneg n alpha L J)
  linarith

theorem unique_coefficient {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n))
    (hJ : form n alpha L J J ≠ 0) :
    ∃! q : ℝ, form n alpha L J (K - q • J) = 0 := by
  refine ⟨coefficient alpha L K J, residual_orthogonal alpha L K J, ?_⟩
  intro q hq
  simp only [map_sub, map_smul, smul_eq_mul] at hq
  rw [form_symmetric n alpha L J K] at hq
  unfold coefficient
  apply (eq_div_iff hJ).mpr
  linarith

structure Conclusions : Prop where
  actual_hessian : ∀ n alpha L (K J : Hermitian (Index n)),
    form n alpha L K J = fderiv ℝ (fderiv ℝ (response n alpha L)) 0 K J
  complete_reconstruction : ∀ {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)),
    K = residual alpha L K J + coefficient alpha L K J • J
  orthogonal_response : ∀ {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)),
    form n alpha L J (residual alpha L K J) = 0
  retained_energy : ∀ {n : ℕ} (alpha L : ℝ) (K J : Hermitian (Index n)),
    form n alpha L K K =
      form n alpha L (residual alpha L K J) (residual alpha L K J) +
        form n alpha L K J ^ 2 / form n alpha L J J

theorem generated : Conclusions where
  actual_hessian := form_hessian
  complete_reconstruction := reconstruction
  orthogonal_response := residual_orthogonal
  retained_energy := schur_identity

end GeneratedFoundations.Analysis.HistoryResponseReduction
