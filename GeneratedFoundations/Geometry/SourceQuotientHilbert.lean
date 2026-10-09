module

public import GeneratedFoundations.Geometry.SourceCentralSpectralProjection
public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Haar Hilbert space of the central source quotient

The quotient measure is the pushforward of the original probability Haar
measure. Its pullback is an isometry into the original source Hilbert space.
Continuous invariant observations provide the descent on a dense subspace;
completeness then identifies the entire image with the fixed space of central
averaging. No measurable descent or surjectivity is assumed.

The even matrix coefficients descend with their existing normalization and
both matrix indices. Their completeness on the quotient follows from the
full source Hilbert basis and the proved central parity action. Differential
operators are not defined in this file.
-/

@[expose] public section

noncomputable section

open MeasureTheory Module
open scoped ComplexConjugate lp
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceCentralSpectralProjection

namespace GeneratedFoundations.Geometry.SourceQuotientHilbert

/-- The measurable structure is the Borel structure of the existing quotient topology. -/
instance quotientMeasurableSpace : MeasurableSpace CentralQuotient := borel CentralQuotient

instance quotientBorelSpace : BorelSpace CentralQuotient := ⟨rfl⟩

/-- No measure is chosen independently of the original source Haar measure. -/
def quotientHaar : Measure CentralQuotient := Measure.map quotientContinuous sourceHaar

instance quotientHaar_isProbability : IsProbabilityMeasure quotientHaar :=
  inferInstanceAs (IsProbabilityMeasure (Measure.map quotientContinuous sourceHaar))

/-- The actual quotient homomorphism carries the finite source Haar measure
to a Haar measure on the central quotient. -/
instance quotientHaar_isHaar : Measure.IsHaarMeasure quotientHaar :=
  Measure.isHaarMeasure_map_of_isFiniteMeasure sourceHaar quotientMap
    quotientContinuous.continuous quotientContinuous_surjective

instance quotientHaar_innerRegular : quotientHaar.InnerRegularCompactLTTop := by
  let : sourceHaar.Regular := inferInstanceAs
    ((Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).Regular)
  exact Measure.InnerRegularCompactLTTop.map_of_continuous quotientContinuous.continuous

theorem quotient_measurePreserving :
    MeasurePreserving quotientContinuous sourceHaar quotientHaar :=
  ⟨quotientContinuous.continuous.measurable, rfl⟩

theorem quotientHaar_apply {A : Set CentralQuotient} (hA : MeasurableSet A) :
    quotientHaar A = sourceHaar (quotientContinuous ⁻¹' A) :=
  Measure.map_apply quotientContinuous.continuous.measurable hA

abbrev QuotientL2 := Lp ℂ 2 quotientHaar

/-- The map acts on genuine equivalence classes by the existing quotient map. -/
def pullbackL2 : QuotientL2 →ₗᵢ[ℂ] SourceL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ quotientContinuous quotient_measurePreserving

theorem pullbackL2_toLp (f : C(CentralQuotient, ℂ)) :
    pullbackL2 (ContinuousMap.toLp 2 quotientHaar ℂ f) =
      ContinuousMap.toLp 2 sourceHaar ℂ (f.comp quotientContinuous) := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 quotientHaar ℂ f) quotient_measurePreserving
  have hf := quotient_measurePreserving.quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) quotientHaar f)
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar
    (f.comp quotientContinuous)
  filter_upwards [hcomp, hf, hr] with U hc hu hright
  exact hc.trans (hu.trans hright.symm)

theorem quotientContinuous_dense :
    DenseRange (ContinuousMap.toLp 2 quotientHaar ℂ :
      C(CentralQuotient, ℂ) →L[ℂ] QuotientL2) :=
  ContinuousMap.toLp_denseRange ℂ quotientHaar ℂ (by norm_num)

/-- Descent of continuous observations extends to the full quotient Haar space. -/
theorem averageL2_pullback (f : QuotientL2) :
    averageL2 (pullbackL2 f) = pullbackL2 f := by
  refine Dense.induction quotientContinuous_dense ?_ ?_ f
  · rintro _ ⟨g, rfl⟩
    rw [pullbackL2_toLp, averageL2_toLp]
    exact congrArg (ContinuousMap.toLp 2 sourceHaar ℂ)
      (centralAverage_of_invariant (pullback g).property)
  · exact isClosed_eq (averageL2.continuous.comp pullbackL2.continuous)
      pullbackL2.continuous

theorem pullbackL2_range_closed : IsClosed (Set.range pullbackL2) :=
  pullbackL2.isometry.isClosedEmbedding.isClosed_range

/-- Every central average is the pullback of an actual quotient Haar class.
The extension uses the closed range of an isometry from a complete space. -/
theorem averageL2_mem_pullback_range (f : SourceL2) :
    averageL2 f ∈ Set.range pullbackL2 := by
  let : sourceHaar.Regular := inferInstanceAs
    ((Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).Regular)
  have hd : DenseRange (ContinuousMap.toLp 2 sourceHaar ℂ :
      C(SU2, ℂ) →L[ℂ] SourceL2) :=
    ContinuousMap.toLp_denseRange ℂ sourceHaar ℂ (by norm_num)
  refine Dense.induction hd ?_ ?_ f
  · rintro _ ⟨g, rfl⟩
    refine ⟨ContinuousMap.toLp 2 quotientHaar ℂ
      (descend (centralAverage g) (centralAverage_invariant g)), ?_⟩
    rw [pullbackL2_toLp,
      descend_comp (centralAverage g) (centralAverage_invariant g), averageL2_toLp]
  · exact pullbackL2_range_closed.preimage averageL2.continuous

theorem mem_pullbackL2_range_iff (f : SourceL2) :
    f ∈ Set.range pullbackL2 ↔ averageL2 f = f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact averageL2_pullback g
  · intro hf
    rw [← hf]
    exact averageL2_mem_pullback_range f

/-- The fixed space refers to the previously defined group average. -/
def centralFixedSpace : Submodule ℂ SourceL2 where
  carrier := {f | averageL2 f = f}
  zero_mem' := map_zero averageL2
  add_mem' := by
    intro f g hf hg
    change averageL2 f = f at hf
    change averageL2 g = g at hg
    change averageL2 (f + g) = f + g
    rw [map_add, hf, hg]
  smul_mem' := by
    intro c f hf
    change averageL2 f = f at hf
    change averageL2 (c • f) = c • f
    rw [map_smul, hf]

@[simp] theorem mem_centralFixedSpace (f : SourceL2) :
    f ∈ centralFixedSpace ↔ averageL2 f = f := Iff.rfl

theorem centralFixedSpace_closed : IsClosed (centralFixedSpace : Set SourceL2) :=
  isClosed_eq averageL2.continuous continuous_id

theorem pullbackL2_range_eq : LinearMap.range pullbackL2.toLinearMap = centralFixedSpace := by
  ext f
  exact mem_pullbackL2_range_iff f

/-- The quotient Haar space is the entire invariant source space, not a proper
subspace selected by finite coefficient truncation. -/
def invariantEquiv : QuotientL2 ≃ₗᵢ[ℂ] centralFixedSpace :=
  pullbackL2.equivRange.trans
    (LinearIsometryEquiv.ofEq _ _ pullbackL2_range_eq)

@[simp] theorem invariantEquiv_apply (f : QuotientL2) :
    (invariantEquiv f : SourceL2) = pullbackL2 f := rfl

theorem quotientClass_existsUnique (f : SourceL2) (hf : averageL2 f = f) :
    ∃! g : QuotientL2, pullbackL2 g = f := by
  obtain ⟨g, hg⟩ := (mem_pullbackL2_range_iff f).mpr hf
  refine ⟨g, hg, ?_⟩
  intro h hh
  exact pullbackL2.injective (hh.trans hg.symm)

theorem pullbackL2_odd_coefficients (f : QuotientL2) (a : Index) (ha : Odd a.1) :
    coefficients (pullbackL2 f) a = 0 :=
  (averageL2_fixed_iff _).mp (averageL2_pullback f) a ha

/-- Every even degree retains both matrix indices from the complete source basis. -/
abbrev EvenIndex := {a : Index // Even a.1}

def quotientBasisVector (a : EvenIndex) : QuotientL2 :=
  normalization a.val.1 • ContinuousMap.toLp 2 quotientHaar ℂ
    (quotientEntry a.property a.val.2.1 a.val.2.2)

@[simp] theorem pullbackL2_basisVector (a : EvenIndex) :
    pullbackL2 (quotientBasisVector a) = basisVector a.val := by
  rw [quotientBasisVector, map_smul, pullbackL2_toLp]
  change normalization a.val.1 • ContinuousMap.toLp 2 sourceHaar ℂ
    ((descend (matrixEntry a.val.1 a.val.2.1 a.val.2.2)
      (matrixEntry_even_invariant a.property a.val.2.1 a.val.2.2)).comp
        quotientContinuous) = basisVector a.val
  rw [descend_comp]
  rfl

theorem quotientBasisVector_orthonormal : Orthonormal ℂ quotientBasisVector := by
  apply (pullbackL2.orthonormal_comp_iff).mp
  have h := basisVector_orthonormal.comp (fun a : EvenIndex => a.val) Subtype.val_injective
  simpa only [Function.comp_def, pullbackL2_basisVector] using h

theorem quotientBasisVector_inner (a : EvenIndex) (f : QuotientL2) :
    inner ℂ (quotientBasisVector a) f = inner ℂ (basisVector a.val) (pullbackL2 f) := by
  rw [← pullbackL2_basisVector]
  exact (pullbackL2.inner_map_map _ _).symm

def quotientEntrySpan : Submodule ℂ QuotientL2 :=
  Submodule.span ℂ (Set.range quotientBasisVector)

/-- Completeness uses the full source coefficient theorem: the missing odd
coefficients vanish by the quotient action, while all even coefficients remain. -/
theorem quotientEntrySpan_orthogonal : quotientEntrySpanᗮ = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  have hall : ∀ a : Index, inner ℂ (basisVector a) (pullbackL2 f) = 0 := by
    intro a
    rcases Nat.even_or_odd a.1 with ha | ha
    · rw [← quotientBasisVector_inner ⟨a, ha⟩ f]
      exact (quotientEntrySpan.mem_orthogonal f).mp hf
        (quotientBasisVector ⟨a, ha⟩) (Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩)
    · exact (coefficients_apply (pullbackL2 f) a).symm.trans
        (pullbackL2_odd_coefficients f a ha)
  have hp : pullbackL2 f = 0 := by
    apply eq_of_coefficients_eq
    intro a
    rw [hall a, inner_zero_right]
  have hfzero : f = 0 := pullbackL2.injective (hp.trans (map_zero pullbackL2).symm)
  simpa only [Submodule.mem_bot] using hfzero

def quotientBasis : HilbertBasis EvenIndex ℂ QuotientL2 :=
  HilbertBasis.mkOfOrthogonalEqBot quotientBasisVector_orthonormal quotientEntrySpan_orthogonal

@[simp] theorem quotientBasis_apply (a : EvenIndex) :
    quotientBasis a = quotientBasisVector a :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot
    quotientBasisVector_orthonormal quotientEntrySpan_orthogonal) a

/-- These are actual quotient-function coefficients, with the source normalization. -/
def quotientCoefficients : QuotientL2 ≃ₗᵢ[ℂ] ℓ²(EvenIndex, ℂ) := quotientBasis.repr

theorem quotientCoefficients_apply (f : QuotientL2) (a : EvenIndex) :
    quotientCoefficients f a = coefficients (pullbackL2 f) a.val := by
  rw [quotientCoefficients, HilbertBasis.repr_apply_apply, quotientBasis_apply,
    quotientBasisVector_inner, coefficients_apply]

theorem quotient_hasSum_expansion (f : QuotientL2) :
    HasSum (fun a : EvenIndex =>
      inner ℂ (quotientBasisVector a) f • quotientBasisVector a) f := by
  simpa only [HilbertBasis.repr_apply_apply, quotientBasis_apply]
    using quotientBasis.hasSum_repr f

theorem quotient_eq_of_coefficients_eq {f g : QuotientL2}
    (hfg : ∀ a : EvenIndex,
      coefficients (pullbackL2 f) a.val = coefficients (pullbackL2 g) a.val) : f = g := by
  apply quotientCoefficients.injective
  apply lp.ext
  funext a
  simpa only [quotientCoefficients_apply] using hfg a

end GeneratedFoundations.Geometry.SourceQuotientHilbert
