module

public import GeneratedFoundations.Probability.SourceContinuity
public import GeneratedFoundations.Source.TraceLieGeometry
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# The compositional law on the generated trace Lie line

The probability part of minimal unbiased compositional change is expressed
on the Hilbert space itself. It includes composition, square-root scaling,
finite second moment and unit covariance, the last stated through every real
linear observation. These are explicit root conditions, not downstream
endpoint or boundary assumptions.
Neither centering nor a coordinate Gaussian law is assumed.

Linear isometries preserve these hypotheses. On a real Hilbert line, the
already established real C/S/V theorem therefore identifies the actual
measure. Pullback of the real Gaussian family proves existence; uniqueness
shows that the law is independent of the coordinate and its orientation.

The final statements apply to the trace Hilbert space of the original Lie
algebra. Its identity-on-vectors continuous linear equivalence with the
original tangent space explicitly transports the resulting measures, without
changing the original chart norm or manifold structure.
-/

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology RealInnerProductSpace Manifold

namespace GeneratedFoundations.Probability

section HilbertSpaces

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- Intrinsic C/S/V data. The covariance identity uses the given Hilbert norm,
not the norm of a selected coordinate or a manifold chart. -/
structure HilbertCompositionalAxioms (μ : ℝ → Measure E) : Prop where
  probability : ∀ t, 0 < t → IsProbabilityMeasure (μ t)
  compose : ∀ s t, 0 < s → 0 < t → μ (s + t) = μ s ∗ μ t
  scale : ∀ t, 0 < t → μ t = (μ 1).map (fun x : E => Real.sqrt t • x)
  memLp_two : MemLp (fun x : E => x) 2 (μ 1)
  unit_covariance : ∀ v : E, variance (fun x : E => inner ℝ v x) (μ 1) = ‖v‖ ^ 2

theorem isometry_map_symm_map (e : E ≃ₗᵢ[ℝ] F) (ν : Measure E) :
    (ν.map e).map e.symm = ν := by
  rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
  have hcomp : (e.symm : F → E) ∘ (e : E → F) = id := by
    funext x
    exact e.symm_apply_apply x
  rw [hcomp, Measure.map_id]

namespace HilbertCompositionalAxioms

variable {μ ν : ℝ → Measure E} (hμ : HilbertCompositionalAxioms μ)

include hμ

theorem map [SecondCountableTopology E] [SecondCountableTopology F]
    (e : E ≃ₗᵢ[ℝ] F) : HilbertCompositionalAxioms (fun t => (μ t).map e) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    let : IsProbabilityMeasure (μ t) := hμ.probability t ht
    exact Measure.isProbabilityMeasure_map_iff e.continuous.measurable.aemeasurable |>.mpr
      inferInstance
  · intro s t hs ht
    let : IsProbabilityMeasure (μ s) := hμ.probability s hs
    let : IsProbabilityMeasure (μ t) := hμ.probability t ht
    rw [hμ.compose s t hs ht]
    exact Measure.map_conv_continuousLinearMap e.toContinuousLinearEquiv.toContinuousLinearMap
  · intro t ht
    have hscaleE : Measurable (fun x : E => Real.sqrt t • x) :=
      (continuous_const.smul continuous_id).measurable
    have hscaleF : Measurable (fun x : F => Real.sqrt t • x) :=
      (continuous_const.smul continuous_id).measurable
    rw [hμ.scale t ht,
      Measure.map_map e.continuous.measurable hscaleE,
      Measure.map_map hscaleF e.continuous.measurable]
    congr 1
    funext x
    exact e.map_smul (Real.sqrt t) x
  · apply (memLp_map_measure_iff aestronglyMeasurable_id
      e.continuous.measurable.aemeasurable).mpr
    simpa only [Function.comp_def, Function.id_def, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv] using
      e.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hμ.memLp_two
  · intro v
    have hvmeas : AEMeasurable (fun y : F => inner ℝ v y) ((μ 1).map e) :=
      (continuous_const.inner continuous_id).measurable.aemeasurable
    rw [variance_map hvmeas e.continuous.measurable.aemeasurable]
    have hfun : (fun y : F => inner ℝ v y) ∘ (e : E → F) =
        (fun x : E => inner ℝ (e.symm v) x) := by
      funext x
      simpa only [Function.comp_apply, LinearIsometryEquiv.apply_symm_apply] using
        e.inner_map_map (e.symm v) x
    rw [hfun, hμ.unit_covariance, e.symm.norm_map]

omit hμ in
theorem real_axioms {η : ℝ → Measure ℝ} (hη : HilbertCompositionalAxioms η) :
    CompositionalGaussianAxioms η := by
  refine ⟨hη.probability, hη.compose, ?_, hη.memLp_two, ?_⟩
  · intro t ht
    simpa only [smul_eq_mul] using hη.scale t ht
  · have hv := hη.unit_covariance 1
    change variance (fun x : ℝ => x * 1) (η 1) = ‖(1 : ℝ)‖ ^ 2 at hv
    simpa only [mul_one, norm_one, one_pow] using hv

theorem coordinate_axioms [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ) :
    CompositionalGaussianAxioms (fun t => (μ t).map e) :=
  (hμ.map e).real_axioms

/-- The actual law in any isometric real coordinate is Gaussian. -/
theorem coordinate_law [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) :
    (μ t).map e = gaussianReal 0 (NNReal.mk t ht.le) :=
  (hμ.coordinate_axioms e).law_eq_gaussian ht

/-- Equality of the original measure, not only equality of a set of moments. -/
theorem law_eq [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) :
    μ t = (gaussianReal 0 (NNReal.mk t ht.le)).map e.symm := by
  rw [← hμ.coordinate_law e ht, isometry_map_symm_map]

theorem unique [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ)
    (hν : HilbertCompositionalAxioms ν) {t : ℝ} (ht : 0 < t) : μ t = ν t := by
  rw [hμ.law_eq e ht, hν.law_eq e ht]

theorem reflection_invariant [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) : (μ t).map (fun x : E => -x) = μ t := by
  apply e.toHomeomorph.measurableEmbedding.map_injective
  calc
    ((μ t).map (fun x : E => -x)).map e =
        ((μ t).map e).map (fun x : ℝ => -x) := by
      rw [Measure.map_map e.continuous.measurable measurable_neg,
        Measure.map_map measurable_neg e.continuous.measurable]
      congr 1
      funext x
      exact e.map_neg x
    _ = (μ t).map e := (hμ.coordinate_axioms e).reflection_invariant ht

/-- A continuous extension at zero is constructed; the unconstrained value
of the original family at nonpositive parameters is not asserted to be unique. -/
def extension [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ) :
    ℝ≥0 → ProbabilityMeasure E :=
  fun t => (SourceContinuity.sourceExtension (hμ.coordinate_axioms e) t).map e.symm

theorem extension_eq [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ)
    {t : ℝ≥0} (ht : 0 < t) : (hμ.extension e t : Measure E) = μ (t : ℝ) := by
  change (SourceContinuity.sourceExtension (hμ.coordinate_axioms e) t : Measure ℝ).map e.symm = _
  rw [SourceContinuity.sourceExtension_eq _ ht, isometry_map_symm_map]

theorem extension_zero [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ) :
    (hμ.extension e 0 : Measure E) = Measure.dirac 0 := by
  change (SourceContinuity.sourceExtension (hμ.coordinate_axioms e) 0 : Measure ℝ).map e.symm = _
  rw [SourceContinuity.sourceExtension_zero]
  change (Measure.dirac (0 : ℝ)).map e.symm = _
  rw [Measure.map_dirac' e.symm.continuous.measurable, map_zero]

theorem extension_continuous [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ) :
    Continuous (hμ.extension e) :=
  (ProbabilityMeasure.continuous_map e.symm.continuous).comp
    (SourceContinuity.sourceExtension_continuous (hμ.coordinate_axioms e))

end HilbertCompositionalAxioms

theorem realHilbert_axioms {η : ℝ → Measure ℝ} (hη : CompositionalGaussianAxioms η) :
    HilbertCompositionalAxioms η := by
  refine ⟨hη.probability, hη.compose, ?_, hη.memLp_two, ?_⟩
  · intro t ht
    simpa only [smul_eq_mul] using hη.scale t ht
  · intro v
    change variance (fun x : ℝ => x * v) (η 1) = ‖v‖ ^ 2
    rw [variance_mul_const, hη.variance_one, one_mul, Real.norm_eq_abs, sq_abs]

def lineGaussianFamily (e : E ≃ₗᵢ[ℝ] ℝ) (t : ℝ) : Measure E :=
  (gaussianFamily t).map e.symm

theorem lineGaussianFamily_axioms [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ) :
    HilbertCompositionalAxioms (lineGaussianFamily e) :=
  (realHilbert_axioms gaussianFamily_axioms).map e.symm

/-- Isometric coordinates, including the two orientations, determine the same
positive-parameter law. No orientation is selected by the Gaussian family. -/
theorem lineGaussianFamily_coordinate_independent [SecondCountableTopology E]
    (e f : E ≃ₗᵢ[ℝ] ℝ) {t : ℝ} (ht : 0 < t) :
    lineGaussianFamily e t = lineGaussianFamily f t :=
  (lineGaussianFamily_axioms e).unique e (lineGaussianFamily_axioms f) ht

theorem lineGaussianFamily_exists_unique [SecondCountableTopology E] (e : E ≃ₗᵢ[ℝ] ℝ) :
    ∃ μ : ℝ → Measure E, HilbertCompositionalAxioms μ ∧
      ∀ ν : ℝ → Measure E, HilbertCompositionalAxioms ν →
        ∀ t : ℝ, 0 < t → μ t = ν t := by
  refine ⟨lineGaussianFamily e, lineGaussianFamily_axioms e, ?_⟩
  intro ν hν t ht
  exact (lineGaussianFamily_axioms e).unique e hν ht

end HilbertSpaces

namespace GeneratedTangentLaw

open Source Source.TraceLieGeometry

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)

instance instMeasurableSpaceTraceLieSpace : MeasurableSpace (TraceLieSpace d h) :=
  borel (TraceLieSpace d h)

instance instBorelSpaceTraceLieSpace : BorelSpace (TraceLieSpace d h) := ⟨rfl⟩

/-- Existence and uniqueness use the original generated trace line. Its real
coordinate is obtained inside the proof from the original minimal action. -/
theorem exists_unique :
    ∃ μ : ℝ → Measure (TraceLieSpace d h), HilbertCompositionalAxioms μ ∧
      ∀ ν : ℝ → Measure (TraceLieSpace d h), HilbertCompositionalAxioms ν →
        ∀ t : ℝ, 0 < t → μ t = ν t := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  exact lineGaussianFamily_exists_unique (phaseIsometry d h e χ hχ haction)

/-- The Gaussian identification retains the same carrier coordinate, original
group character, and actual representation differential. -/
theorem classification {μ : ℝ → Measure (TraceLieSpace d h)}
    (hμ : HilbertCompositionalAxioms μ) :
    ∃ (e : d.Carrier ≃ₗᵢ[ℝ] ℂ) (χ : d.Changes ≃* Circle) (hχ : Continuous χ)
      (haction : ∀ g v, e (d.action g v) = (χ g : ℂ) * e v),
      ∀ (t : ℝ) (ht : 0 < t),
        μ t = (gaussianReal 0 (NNReal.mk t ht.le)).map
          (phaseIsometry d h e χ hχ haction).symm := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  exact ⟨e, χ, hχ, haction, fun _ ht => hμ.law_eq (phaseIsometry d h e χ hχ haction) ht⟩

theorem reflection_invariant {μ : ℝ → Measure (TraceLieSpace d h)}
    (hμ : HilbertCompositionalAxioms μ) {t : ℝ} (ht : 0 < t) :
    (μ t).map (fun X : TraceLieSpace d h => -X) = μ t := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  exact hμ.reflection_invariant (phaseIsometry d h e χ hχ haction) ht

theorem continuous_zero_extension {μ : ℝ → Measure (TraceLieSpace d h)}
    (hμ : HilbertCompositionalAxioms μ) :
    ∃ ν : ℝ≥0 → ProbabilityMeasure (TraceLieSpace d h), Continuous ν ∧
      (ν 0 : Measure (TraceLieSpace d h)) = Measure.dirac 0 ∧
      ∀ t : ℝ≥0, 0 < t → (ν t : Measure (TraceLieSpace d h)) = μ (t : ℝ) := by
  obtain ⟨_, e, χ, hχ, _, haction⟩ := MinimalCarrier.minimalCarrier_classification d h
  let q := phaseIsometry d h e χ hχ haction
  exact ⟨hμ.extension q, hμ.extension_continuous q, hμ.extension_zero q,
    fun _ ht => hμ.extension_eq q ht⟩

section OriginalTangent

variable [MeasurableSpace (GroupLieAlgebra (𝓡 d.groupDimension) d.Changes)]
  [BorelSpace (GroupLieAlgebra (𝓡 d.groupDimension) d.Changes)]

/-- Pushforward by the established identity on vectors expresses the same law
on the original tangent-space type, with its original topology and atlas. -/
theorem original_tangent_law {μ : ℝ → Measure (TraceLieSpace d h)}
    (hμ : HilbertCompositionalAxioms μ) (q : TraceLieSpace d h ≃ₗᵢ[ℝ] ℝ)
    {t : ℝ} (ht : 0 < t) :
    (μ t).map (underlyingContinuousLinearEquiv d h) =
      (gaussianReal 0 (NNReal.mk t ht.le)).map
        ((underlyingContinuousLinearEquiv d h) ∘ q.symm) := by
  rw [hμ.law_eq q ht,
    Measure.map_map (underlyingContinuousLinearEquiv d h).continuous.measurable
      q.symm.continuous.measurable]

end OriginalTangent

end GeneratedTangentLaw

end GeneratedFoundations.Probability
