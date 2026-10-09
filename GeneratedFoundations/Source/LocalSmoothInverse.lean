module

public import Mathlib.Geometry.Manifold.MFDeriv.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Smooth inverses in the original manifold charts

A homeomorphism between boundaryless manifolds has a smooth inverse when
its original-chart differential is invertible everywhere. The proof applies
the inverse regularity theorem to the existing coordinate homeomorphism;
neither manifold structure is transported through the given map.
-/

@[expose] public section

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace GeneratedFoundations.Source.LocalSmoothInverse

variable {E F M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace N] [ChartedSpace F N]

/-- Invertibility refers to the derivative in the two given atlases. -/
theorem contMDiff_symm_of_bijective_mfderiv (e : M ≃ₜ N)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ∞ e)
    (hd : ∀ x, Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x)) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, E) ∞ e.symm := by
  intro y
  let x := e.symm y
  let c := chartAt E x
  let k := chartAt F y
  let f := (c.symm.trans e.toOpenPartialHomeomorph).trans k
  have hex : e x = y := e.apply_symm_apply y
  have hcx : x ∈ c.source := mem_chart_source E x
  have hky : k y ∈ k.target := mem_chart_target F y
  have hf_inv : f.symm (k y) = c x := by
    change c (e.symm (k.symm (k y))) = c x
    rw [k.left_inv (mem_chart_source F y)]
  have hf_target : k y ∈ f.target := by
    change k y ∈ k.target ∩ k.symm ⁻¹' (Set.univ ∩ e.symm ⁻¹' c.source)
    simpa only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_univ, true_and,
      k.left_inv (mem_chart_source F y)] using And.intro hky hcx
  have hdiff := (he x).mdifferentiableAt (by simp)
  let A := ((tangentSpaceCastModel 𝓘(ℝ, F) (e x)) :
      TangentSpace 𝓘(ℝ, F) (e x) →L[ℝ] F) ∘L
    mfderiv 𝓘(ℝ, E) 𝓘(ℝ, F) e x ∘L
      ((tangentSpaceCastModel 𝓘(ℝ, E) x).symm :
        E →L[ℝ] TangentSpace 𝓘(ℝ, E) x)
  have hA : Bijective A :=
    (tangentSpaceCastModel 𝓘(ℝ, F) (e x)).bijective.comp
      ((hd x).comp (tangentSpaceCastModel 𝓘(ℝ, E) x).symm.bijective)
  let B : E ≃L[ℝ] F := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hA.1) (LinearMap.range_eq_top.mpr hA.2)
  have hf_deriv : HasFDerivAt f (B : E →L[ℝ] F) (c x) := by
    have hx := hdiff.hasMFDerivAt.2
    change HasFDerivAt (fun z => k (e (c.symm z))) A (c x)
    simpa only [writtenInExtChartAt, hex, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Set.range_id,
      hasFDerivWithinAt_univ, Function.comp_def, id_eq, A, c, k] using hx
  have hf_smooth : ContDiffAt ℝ ∞ f (c x) := by
    have hx := (contMDiffAt_iff.mp (he x)).2
    change ContDiffAt ℝ ∞ (fun z => k (e (c.symm z))) (c x)
    simpa only [hex, extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Set.range_id, contDiffWithinAt_univ,
      Function.comp_def, id_eq, c, k] using hx
  have hi := f.contDiffAt_symm hf_target
    (show HasFDerivAt f (B : E →L[ℝ] F) (f.symm (k y)) by rwa [hf_inv])
    (show ContDiffAt ℝ ∞ f (f.symm (k y)) by rwa [hf_inv])
  apply contMDiffAt_iff.mpr
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  change ContDiffWithinAt ℝ ∞ (fun z => c (e.symm (k.symm z)))
    (Set.range (id : F → F)) (k y)
  rw [Set.range_id, contDiffWithinAt_univ]
  exact hi

end GeneratedFoundations.Source.LocalSmoothInverse
