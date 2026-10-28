module

public import GeneratedFoundations.Operations.GibbsResolutionLedger

/-!
# Orthogonal reduction in the complete Gibbs response

The eliminated observation is optimized in the same positive Gibbs form as
the retained observation. Scalar directions, whose curvature is zero, are
included. Changing the reference recomputes the coefficient and preserves
any contraction already proved for the complete logarithmic-mean kernel.
-/

@[expose] public section
noncomputable section

namespace GeneratedFoundations.Operations.GibbsSchurResponse

open PreparedTraceForm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def form (a : ι → ℝ) : LinearMap.BilinForm ℝ (Hermitian ι) :=
  GibbsTraceForm.hermitianForm a

omit [Nonempty ι] in
theorem form_symmetric (a : ι → ℝ) (K J : Hermitian ι) :
    form a K J = form a J K := GibbsTraceForm.gibbsForm_symm _ _ _

theorem form_nonneg (a : ι → ℝ) (K : Hermitian ι) : 0 ≤ form a K K :=
  GibbsTraceForm.gibbsForm_nonneg a (hermitian_isHermitian ι K)

theorem null_mixed (a : ι → ℝ) (J : Hermitian ι)
    (hJ : form a J J = 0) (K : Hermitian ι) : form a J K = 0 := by
  have hs := (GibbsTraceForm.gibbsForm_self_eq_zero_iff a
    (hermitian_isHermitian ι J)).mp hJ
  exact (GibbsTraceForm.gibbsForm_kernel_iff a J).mpr hs K

def coefficient (a : ι → ℝ) (K J : Hermitian ι) : ℝ := form a K J / form a J J

def residual (a : ι → ℝ) (K J : Hermitian ι) : Hermitian ι :=
  K - coefficient a K J • J

omit [Nonempty ι] in
theorem reconstruction (a : ι → ℝ) (K J : Hermitian ι) :
    K = residual a K J + coefficient a K J • J := by simp [residual]

theorem residual_orthogonal (a : ι → ℝ) (K J : Hermitian ι) :
    form a J (residual a K J) = 0 := by
  by_cases hJ : form a J J = 0
  · exact null_mixed a J hJ _
  · simp only [residual, map_sub, map_smul, smul_eq_mul]
    rw [form_symmetric a J K]
    unfold coefficient
    field_simp [hJ]
    ring

omit [Nonempty ι] in
theorem schur_identity (a : ι → ℝ) (K J : Hermitian ι) :
    form a K K = form a (residual a K J) (residual a K J) +
      form a K J ^ 2 / form a J J := by
  have he : form a (residual a K J) (residual a K J) =
      form a K K - 2 * coefficient a K J * form a K J +
        coefficient a K J ^ 2 * form a J J := by
    simp only [residual, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [form_symmetric a J K]
    ring
  rw [he]
  by_cases hJ : form a J J = 0
  · simp [coefficient, hJ]
  · unfold coefficient
    field_simp [hJ]
    ring

theorem shifted_square (a : ι → ℝ) (K J : Hermitian ι) (q : ℝ) :
    form a (K - q • J) (K - q • J) =
      form a (residual a K J) (residual a K J) +
        form a J J * (coefficient a K J - q) ^ 2 := by
  have he : K - q • J = residual a K J + (coefficient a K J - q) • J := by
    unfold residual
    module
  have hl := residual_orthogonal a K J
  have hr : form a (residual a K J) J = 0 := by
    rw [form_symmetric]
    exact hl
  rw [he]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, hl, hr]
  ring

theorem residual_minimality (a : ι → ℝ) (K J : Hermitian ι) (q : ℝ) :
    form a (residual a K J) (residual a K J) ≤ form a (K - q • J) (K - q • J) := by
  rw [shifted_square]
  exact le_add_of_nonneg_right (mul_nonneg (form_nonneg a J) (sq_nonneg _))

theorem unique_coefficient (a : ι → ℝ) (K J : Hermitian ι) (hJ : form a J J ≠ 0) :
    ∃! q : ℝ, form a J (K - q • J) = 0 := by
  refine ⟨coefficient a K J, residual_orthogonal a K J, ?_⟩
  intro q hq
  simp only [map_sub, map_smul, smul_eq_mul] at hq
  rw [form_symmetric a J K] at hq
  unfold coefficient
  apply (eq_div_iff hJ).mpr
  linarith

/-- The reduction is reoptimized at the new reference. The hypothesis is
the complete kernel comparison, not a bound on separately removed terms. -/
theorem reduced_contraction {a b : ι → ℝ} {q : ℝ}
    (h : ∀ i j, GibbsExponentialDifferentiation.expDividedDifference (b i) (b j) ≤
      q * GibbsExponentialDifferentiation.expDividedDifference (a i) (a j))
    (K J : Hermitian ι) :
    GibbsTraceForm.Z b * form b (residual b K J) (residual b K J) ≤
      q * (GibbsTraceForm.Z a * form a (residual a K J) (residual a K J)) := by
  have hm := residual_minimality b K J (coefficient a K J)
  have hc := GibbsResolutionLedger.restored_contraction h
    (hermitian_isHermitian ι (residual a K J))
  exact (mul_le_mul_of_nonneg_left hm (GibbsTraceForm.Z_pos b).le).trans hc

end GeneratedFoundations.Operations.GibbsSchurResponse
