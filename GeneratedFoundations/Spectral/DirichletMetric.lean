module

public import GeneratedFoundations.Spectral.IntervalSobolev

/-!
# The intrinsic distance of the interval Dirichlet form

The admissible functions are actual absolutely continuous Sobolev
representatives whose derivative has square at most one almost everywhere.
Their increments are bounded by Euclidean distance; the affine coordinate
attains that bound. Thus the supremum does not introduce an independent metric.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology Interval

namespace GeneratedFoundations.Spectral

def DirichletAdmissible (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ g : ℝ → ℝ, HasH1Derivative a b f g ∧
    ∀ᵐ x ∂intervalMeasure a b, (g x) ^ 2 ≤ 1

theorem dirichletAdmissible_increment_le {a b x y : ℝ} {f : ℝ → ℝ}
    (hf : DirichletAdmissible a b f) (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ |x - y| := by
  obtain ⟨g, hg, hbound⟩ := hf
  have hnorm : ∀ᵐ z ∂volume, z ∈ uIoc x y → ‖g z‖ ≤ 1 := by
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp hbound] with z hz hzi
    rw [Real.norm_eq_abs]
    exact (sq_le_one_iff_abs_le_one _).mp
      (hz ((uIcc_subset_Icc hx hy) (uIoc_subset_uIcc hzi)))
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const_ae hnorm
  rw [hg.integral_eq_sub hx hy, Real.norm_eq_abs, one_mul] at hint
  simpa only [abs_sub_comm] using hint

theorem dirichletAdmissible_coordinate (a b : ℝ) :
    DirichletAdmissible a b (fun x => x) := by
  refine ⟨fun _ => 1, ?_, ae_of_all _ (fun _ => by norm_num)⟩
  refine ⟨(contDiff_id : ContDiff ℝ 1 (fun x : ℝ => x)).contDiffOn.absolutelyContinuousOnInterval,
    memLp_const 1, ?_⟩
  exact ae_of_all _ fun x => hasDerivAt_id' x

noncomputable def dirichletDistance (a b x y : ℝ) : ℝ :=
  sSup {r : ℝ | ∃ f : ℝ → ℝ, DirichletAdmissible a b f ∧ r = |f x - f y|}

/-- The intrinsic distance agrees with the original interval metric. -/
theorem dirichletDistance_eq {a b x y : ℝ}
    (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    dirichletDistance a b x y = |x - y| := by
  have htrial : |x - y| ∈
      {r : ℝ | ∃ f : ℝ → ℝ, DirichletAdmissible a b f ∧ r = |f x - f y|} :=
    ⟨fun z => z, dirichletAdmissible_coordinate a b, rfl⟩
  apply csSup_eq_of_is_forall_le_of_forall_le_imp_ge ⟨_, htrial⟩
  · rintro r ⟨f, hf, rfl⟩
    exact dirichletAdmissible_increment_le hf hx hy
  · intro upper hupper
    exact hupper _ htrial

end GeneratedFoundations.Spectral
