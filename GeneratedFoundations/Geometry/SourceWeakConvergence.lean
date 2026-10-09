module

public import GeneratedFoundations.Geometry.SourceCompleteCoefficients
public import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
# Probability laws determined by the actual source coefficients

The source group is the original compact matrix group. Its proved coefficient
density separates all Borel probability laws, not just Haar densities. For an
arbitrary nontrivial filter, convergence of every actual matrix coefficient
therefore constructs a unique limiting probability law and proves weak
convergence to it. Existence is obtained from compactness of probability
measures; no candidate limiting law or positive density is assumed.

The final specialization records the heat coefficients used by the actual
finite source-operation walks. It still requires their coefficient limits,
which are supplied by the separate single-step and power-limit arguments.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ENNReal
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceCoefficientProducts
open GeneratedFoundations.Geometry.SourceCoefficientDensity
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients

namespace GeneratedFoundations.Geometry.SourceWeakConvergence

local instance : TopologicalSpace.PseudoMetrizableSpace (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin 2 → Fin 2 → ℂ))

local instance : TopologicalSpace.PseudoMetrizableSpace SU2 :=
  Topology.IsInducing.subtypeVal.pseudoMetrizableSpace

/-- The tests are the original source matrix coefficients in all degrees. -/
def entryTest (a : Index) : C(SU2, ℂ) :=
  matrixEntry a.1 a.2.1 a.2.2

theorem test_integrable (μ : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) :
    Integrable f (μ : Measure SU2) :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (μ := (μ : Measure SU2)) (p := 1) ℂ f)

/-- Integration against an actual probability law is a bounded linear
functional for the uniform norm. -/
def expectation (μ : ProbabilityMeasure SU2) : C(SU2, ℂ) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ U, f U ∂(μ : Measure SU2)
      map_add' := fun f g => integral_add (test_integrable μ f) (test_integrable μ g)
      map_smul' := fun c f => integral_smul c f }
    1 (fun f => by
      simpa [measureReal_def] using
        (norm_integral_le_of_norm_le_const
          (μ := (μ : Measure SU2))
          (Eventually.of_forall (fun U => f.norm_coe_le_norm U))))

@[simp] theorem expectation_apply (μ : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) :
    expectation μ f = ∫ U, f U ∂(μ : Measure SU2) := rfl

theorem expectation_continuous (f : C(SU2, ℂ)) :
    Continuous (fun μ : ProbabilityMeasure SU2 => expectation μ f) := by
  rw [continuous_iff_continuousAt]
  intro μ
  exact (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto
    (Ω := SU2) ℂ (F := 𝓝 μ) (μs := id) (μ := μ)).mp tendsto_id
      (ContinuousMap.equivBoundedOfCompact SU2 ℂ f)

/-- The actual matrix entries determine every bounded complex-linear map
on the full continuous observation space. -/
theorem linearMap_ext_of_entries {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {L M : C(SU2, ℂ) →L[ℂ] E}
    (h : ∀ a : Index, L (entryTest a) = M (entryTest a)) : L = M := by
  apply ContinuousLinearMap.ext_on (s := coefficientGenerators) coefficientSpan_dense
  rintro f ⟨m, φ, v, rfl⟩
  simp only [coefficient_expansion, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact congrArg (fun z : E =>
    (φ ((SourceSymmetricUnitary.carrierEquiv m).symm (sourceBasis m i)) *
      inner ℂ (sourceBasis m j) (SourceSymmetricUnitary.carrierEquiv m v)) • z)
    (h ⟨m, i, j⟩)

/-- Equality on all actual source matrix coefficients determines a Borel
probability measure. The intervening uniform density is already proved from
the original source-coordinate algebra. -/
theorem probability_ext {μ ν : ProbabilityMeasure SU2}
    (h : ∀ a : Index, expectation μ (entryTest a) = expectation ν (entryTest a)) :
    μ = ν := by
  have he := linearMap_ext_of_entries h
  apply ProbabilityMeasure.toMeasure_injective
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(SU2, ℂ) :=
    ⟨fun U => (f U : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hfc := congrArg (fun T : C(SU2, ℂ) →L[ℂ] ℂ => T fc) he
  change (∫ U, (f U : ℂ) ∂(μ : Measure SU2)) =
    ∫ U, (f U : ℂ) ∂(ν : Measure SU2) at hfc
  rw [integral_complex_ofReal, integral_complex_ofReal] at hfc
  exact Complex.ofReal_injective hfc

def HasEntryIntegrals (μ : ProbabilityMeasure SU2) (values : Index → ℂ) : Prop :=
  ∀ a, expectation μ (entryTest a) = values a

theorem hasEntryIntegrals_unique {μ ν : ProbabilityMeasure SU2} {values : Index → ℂ}
    (hμ : HasEntryIntegrals μ values) (hν : HasEntryIntegrals ν values) : μ = ν :=
  probability_ext (fun a => (hμ a).trans (hν a).symm)

/-- Every cluster law inherits the supplied limits along the same filter. -/
theorem cluster_hasEntryIntegrals {ι : Type*} {l : Filter ι}
    {ν : ι → ProbabilityMeasure SU2} {values : Index → ℂ}
    (hν : ∀ a, Tendsto (fun i => expectation (ν i) (entryTest a)) l (𝓝 (values a)))
    {μ : ProbabilityMeasure SU2} (hμ : MapClusterPt μ l ν) :
    HasEntryIntegrals μ values := by
  let : NeBot (𝓝 μ ⊓ Filter.map ν l) := hμ
  intro a
  have hmap : Tendsto (fun ρ => expectation ρ (entryTest a)) (Filter.map ν l)
      (𝓝 (values a)) :=
    tendsto_map'_iff.mpr (hν a)
  exact tendsto_nhds_unique
    (((expectation_continuous (entryTest a)).tendsto μ).mono_left inf_le_left)
    (hmap.mono_left inf_le_right)

/-- The limiting probability law is constructed from the given family.
Uniqueness concerns all probability laws with these coefficients, not merely
the limit of this one family. -/
theorem existsUnique_probability_of_entry_limits {ι : Type*}
    (l : Filter ι) [NeBot l] (ν : ι → ProbabilityMeasure SU2) (values : Index → ℂ)
    (hν : ∀ a, Tendsto (fun i => expectation (ν i) (entryTest a)) l (𝓝 (values a))) :
    ∃! μ : ProbabilityMeasure SU2, HasEntryIntegrals μ values := by
  obtain ⟨μ, hμ⟩ := exists_clusterPt_of_compactSpace (Filter.map ν l)
  have hm : HasEntryIntegrals μ values := cluster_hasEntryIntegrals hν hμ
  exact ⟨μ, hm, fun ρ hρ => hasEntryIntegrals_unique hρ hm⟩

/-- Uniqueness of cluster laws upgrades coefficient convergence to weak
convergence of the entire family, including punctured real step-size filters. -/
theorem tendsto_of_entry_limits {ι : Type*} {l : Filter ι}
    {ν : ι → ProbabilityMeasure SU2} {values : Index → ℂ}
    (hν : ∀ a, Tendsto (fun i => expectation (ν i) (entryTest a)) l (𝓝 (values a)))
    {μ : ProbabilityMeasure SU2} (hμ : HasEntryIntegrals μ values) :
    Tendsto ν l (𝓝 μ) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro ρ hρ
  exact hasEntryIntegrals_unique (cluster_hasEntryIntegrals hν hρ) hμ

/-- Existence, uniqueness among all probability laws, and weak convergence
are obtained together without supplying a target law as an input. -/
theorem probability_limit {ι : Type*}
    (l : Filter ι) [NeBot l] (ν : ι → ProbabilityMeasure SU2) (values : Index → ℂ)
    (hν : ∀ a, Tendsto (fun i => expectation (ν i) (entryTest a)) l (𝓝 (values a))) :
    ∃ μ : ProbabilityMeasure SU2,
      HasEntryIntegrals μ values ∧ Tendsto ν l (𝓝 μ) ∧
        ∀ ρ : ProbabilityMeasure SU2, HasEntryIntegrals ρ values → ρ = μ := by
  obtain ⟨μ, hμ, hu⟩ := existsUnique_probability_of_entry_limits l ν values hν
  exact ⟨μ, hμ, tendsto_of_entry_limits hν hμ, hu⟩

/-- The trace-unit-axis Casimir eigenvalue is `m * (m + 2)`; both actual
matrix indices are retained. -/
def heatCoefficient (t : ℝ) (a : Index) : ℂ :=
  (Real.exp (-t * ((a.1 : ℝ) * ((a.1 : ℝ) + 2))) : ℂ) *
    (if a.2.1 = a.2.2 then 1 else 0)

theorem heat_probability_limit {ι : Type*}
    (l : Filter ι) [NeBot l] (ν : ι → ProbabilityMeasure SU2) (t : ℝ)
    (hν : ∀ a, Tendsto (fun i => expectation (ν i) (entryTest a)) l
      (𝓝 (heatCoefficient t a))) :
    ∃ μ : ProbabilityMeasure SU2,
      HasEntryIntegrals μ (heatCoefficient t) ∧ Tendsto ν l (𝓝 μ) ∧
        ∀ ρ : ProbabilityMeasure SU2, HasEntryIntegrals ρ (heatCoefficient t) → ρ = μ :=
  probability_limit l ν (heatCoefficient t) hν

end GeneratedFoundations.Geometry.SourceWeakConvergence
