module

public import GeneratedFoundations.Probability.CompositionalGaussian
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
Weak continuity follows from square-root dilation of a probability measure.
Composition, centering, and moment assumptions are not used in this continuity
argument. The value at zero is an extension of the positive-parameter family.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter BoundedContinuousFunction
open scoped NNReal Topology

namespace GeneratedFoundations.Probability.SourceContinuity

def nullLaw : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩

def scaledLaw (ν : ProbabilityMeasure ℝ) (t : ℝ≥0) : ProbabilityMeasure ℝ :=
  ν.map (fun x : ℝ => Real.sqrt (t : ℝ) * x)

theorem integral_scaledLaw (ν : ProbabilityMeasure ℝ) (t : ℝ≥0) (f : ℝ →ᵇ ℝ) :
    (∫ y : ℝ, f y ∂(scaledLaw ν t : Measure ℝ)) =
      ∫ x : ℝ, f (Real.sqrt (t : ℝ) * x) ∂(ν : Measure ℝ) := by
  exact integral_map_of_stronglyMeasurable
    (measurable_const.mul measurable_id) f.continuous.stronglyMeasurable

theorem scaledLaw_zero (ν : ProbabilityMeasure ℝ) : scaledLaw ν 0 = nullLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [scaledLaw, nullLaw, ProbabilityMeasure.map, Measure.map_const]

theorem scaledLaw_one (ν : ProbabilityMeasure ℝ) : scaledLaw ν 1 = ν := by
  apply ProbabilityMeasure.toMeasure_injective
  simp [scaledLaw, ProbabilityMeasure.map]

theorem continuous_scaledLaw (ν : ProbabilityMeasure ℝ) : Continuous (scaledLaw ν) := by
  apply ProbabilityMeasure.continuous_iff_forall_continuous_integral.mpr
  intro f
  simp_rw [integral_scaledLaw]
  apply continuous_of_dominated (bound := fun _ : ℝ => ‖f‖)
  · intro t
    exact (f.continuous.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
  · intro t
    exact ae_of_all _ fun x => f.norm_coe_le_norm _
  · exact integrable_const ‖f‖
  · exact ae_of_all _ fun x =>
      f.continuous.comp ((Real.continuous_sqrt.comp continuous_subtype_val).mul continuous_const)

theorem scaledLaw_tendsto_zero (ν : ProbabilityMeasure ℝ) :
    Tendsto (scaledLaw ν) (𝓝 (0 : ℝ≥0)) (𝓝 nullLaw) := by
  simpa only [scaledLaw_zero] using (continuous_scaledLaw ν).tendsto (0 : ℝ≥0)

theorem integral_scaledLaw_tendsto_zero (ν : ProbabilityMeasure ℝ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun t : ℝ≥0 => ∫ x : ℝ, f x ∂(scaledLaw ν t : Measure ℝ))
      (𝓝 0) (𝓝 (f 0)) := by
  have h := ((ProbabilityMeasure.continuous_integral_boundedContinuousFunction f).tendsto nullLaw).comp
    (scaledLaw_tendsto_zero ν)
  simpa only [nullLaw, ProbabilityMeasure.toMeasure, integral_dirac, Function.comp_def] using h

def sourceExtension {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ) :
    ℝ≥0 → ProbabilityMeasure ℝ := scaledLaw ⟨μ 1, hμ.probability 1 zero_lt_one⟩

theorem sourceExtension_eq {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ)
    {t : ℝ≥0} (ht : 0 < t) : (sourceExtension hμ t : Measure ℝ) = μ (t : ℝ) := by
  exact (hμ.scale (t : ℝ) ht).symm

theorem sourceExtension_zero {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ) :
    sourceExtension hμ 0 = nullLaw := scaledLaw_zero _

theorem sourceExtension_continuous {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ) :
    Continuous (sourceExtension hμ) := continuous_scaledLaw _

def positiveSource {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ)
    (t : Set.Ioi (0 : ℝ)) : ProbabilityMeasure ℝ := ⟨μ t, hμ.probability t t.property⟩

theorem positiveSource_eq_extension {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ)
    (t : Set.Ioi (0 : ℝ)) : positiveSource hμ t = sourceExtension hμ (t : ℝ).toNNReal := by
  apply ProbabilityMeasure.toMeasure_injective
  have ht : 0 < (t : ℝ).toNNReal := Real.toNNReal_pos.mpr t.property
  rw [sourceExtension_eq hμ ht, Real.coe_toNNReal _ t.property.le]
  rfl

theorem positiveSource_continuous {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ) :
    Continuous (positiveSource hμ) := by
  have hf : positiveSource hμ = fun t : Set.Ioi (0 : ℝ) => sourceExtension hμ (t : ℝ).toNNReal :=
    funext (positiveSource_eq_extension hμ)
  rw [hf]
  exact (sourceExtension_continuous hμ).comp
    (continuous_real_toNNReal.comp continuous_subtype_val)

theorem source_integral_tendsto_zero {μ : ℝ → Measure ℝ} (hμ : CompositionalGaussianAxioms μ)
    (f : ℝ →ᵇ ℝ) :
    Tendsto (fun t : ℝ => ∫ x : ℝ, f x ∂μ t) (𝓝[>] 0) (𝓝 (f 0)) := by
  have hparameter : Tendsto (fun t : ℝ => t.toNNReal) (𝓝[>] 0) (𝓝 (0 : ℝ≥0)) := by
    simpa using (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds : 𝓝[>] 0 ≤ 𝓝 (0 : ℝ))
  have h := (integral_scaledLaw_tendsto_zero ⟨μ 1, hμ.probability 1 zero_lt_one⟩ f).comp hparameter
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  change (∫ x : ℝ, f x ∂(sourceExtension hμ t.toNNReal : Measure ℝ)) = ∫ x : ℝ, f x ∂μ t
  rw [sourceExtension_eq hμ (Real.toNNReal_pos.mpr ht'), Real.coe_toNNReal _ ht'.le]

end GeneratedFoundations.Probability.SourceContinuity
