module

public import GeneratedFoundations.Geometry.SourceCoefficientProducts
public import Mathlib.Algebra.Group.Submonoid.Membership
public import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-!
# Density of coefficients of the actual source representations

The proved degree-one product rule is iterated over finite words in the
actual source matrix entries. The determinant-one unitary relations express
their complex conjugates as signed entries, so the coordinate star algebra
also lies in the same linear span of homogeneous representation coefficients.

The entries separate the original source matrices. Stone--Weierstrass then
gives uniform density, and the continuous inclusion into the actual source
Haar `L²` space gives density there. Neither multiplication closure of the
whole coefficient span nor a general Peter--Weyl theorem is assumed.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal ComplexConjugate Pointwise
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceCoefficientProducts

namespace GeneratedFoundations.Geometry.SourceCoefficientDensity

def coordinateGenerators : Set C(SU2, ℂ) :=
  Set.range (fun ij : Fin 2 × Fin 2 => sourceEntry ij.1 ij.2)

def coordinateAlgebra : StarSubalgebra ℂ C(SU2, ℂ) :=
  StarAlgebra.adjoin ℂ coordinateGenerators

theorem sourceEntry_mem_coordinateAlgebra (i j : Fin 2) :
    sourceEntry i j ∈ coordinateAlgebra :=
  StarAlgebra.subset_adjoin ℂ coordinateGenerators ⟨(i, j), rfl⟩

/-- These are identities on the actual special-unitary matrices. -/
theorem sourceEntry11_eq_star00 : sourceEntry 1 1 = star (sourceEntry 0 0) := by
  ext U
  simpa [sourceEntry, canonical] using
    congrArg (fun A : Mat2 => A 1 1) (specialUnitary_entries (U : Mat2) U.property)

theorem sourceEntry10_eq_neg_star01 : sourceEntry 1 0 = -star (sourceEntry 0 1) := by
  ext U
  simpa [sourceEntry, canonical] using
    congrArg (fun A : Mat2 => A 1 0) (specialUnitary_entries (U : Mat2) U.property)

/-- Conjugated coordinate multiplication is reduced to the proved
degree-one product rule, not to a postulated coefficient algebra. -/
theorem star_sourceEntry_mul_mem (i j : Fin 2) {f : C(SU2, ℂ)}
    (hf : f ∈ coefficientSpan) : star (sourceEntry i j) * f ∈ coefficientSpan := by
  fin_cases i <;> fin_cases j
  · change star (sourceEntry 0 0) * f ∈ coefficientSpan
    rw [← sourceEntry11_eq_star00]
    exact sourceEntry_mul_mem 1 1 hf
  · change star (sourceEntry 0 1) * f ∈ coefficientSpan
    have he : star (sourceEntry 0 1) = -sourceEntry 1 0 := by
      rw [sourceEntry10_eq_neg_star01, neg_neg]
    rw [he, neg_mul]
    exact coefficientSpan.neg_mem (sourceEntry_mul_mem 1 0 hf)
  · change star (sourceEntry 1 0) * f ∈ coefficientSpan
    rw [sourceEntry10_eq_neg_star01, star_neg, star_star, neg_mul]
    exact coefficientSpan.neg_mem (sourceEntry_mul_mem 0 1 hf)
  · change star (sourceEntry 1 1) * f ∈ coefficientSpan
    rw [sourceEntry11_eq_star00, star_star]
    exact sourceEntry_mul_mem 0 0 hf

/-- Every finite coordinate word, including conjugated entries, has a
finite expansion in coefficients of the actual homogeneous source family. -/
theorem coordinate_word_mem {f : C(SU2, ℂ)}
    (hf : f ∈ Submonoid.closure (coordinateGenerators ∪ star coordinateGenerators)) :
    f ∈ coefficientSpan := by
  induction hf using Submonoid.closure_induction_left with
  | one => exact SourceCoefficientProducts.one_mem
  | mul_left x hx y hy ih =>
      rcases hx with hx | hx
      · obtain ⟨⟨i, j⟩, rfl⟩ := hx
        exact sourceEntry_mul_mem i j ih
      · change star x ∈ coordinateGenerators at hx
        obtain ⟨⟨i, j⟩, he⟩ := hx
        have he' := congrArg star he
        simp only [star_star] at he'
        rw [← he']
        exact star_sourceEntry_mul_mem i j ih

theorem coordinateAlgebra_le_coefficientSpan :
    coordinateAlgebra.toSubalgebra.toSubmodule ≤ coefficientSpan := by
  rw [coordinateAlgebra, StarAlgebra.adjoin_eq_span]
  exact Submodule.span_le.mpr (fun f hf => coordinate_word_mem hf)

/-- In particular, the ordinary polynomial algebra of the original
coordinates already lies in the same coefficient span. -/
theorem coordinate_polynomial_mem {f : C(SU2, ℂ)}
    (hf : f ∈ Algebra.adjoin ℂ coordinateGenerators) : f ∈ coefficientSpan := by
  have ha : Algebra.adjoin ℂ coordinateGenerators ≤ coordinateAlgebra.toSubalgebra :=
    Algebra.adjoin_le (fun g hg => StarAlgebra.subset_adjoin ℂ coordinateGenerators hg)
  exact coordinateAlgebra_le_coefficientSpan (ha hf)

theorem coordinateAlgebra_separates : coordinateAlgebra.SeparatesPoints := by
  intro U V hUV
  have hentry : ∃ i j : Fin 2, sourceEntry i j U ≠ sourceEntry i j V := by
    by_contra hn
    apply hUV
    apply Subtype.ext
    funext i j
    by_contra hij
    exact hn ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := hentry
  exact ⟨sourceEntry i j, ⟨sourceEntry i j, sourceEntry_mem_coordinateAlgebra i j, rfl⟩, hij⟩

theorem coordinateAlgebra_complete : coordinateAlgebra.topologicalClosure = ⊤ :=
  ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    coordinateAlgebra coordinateAlgebra_separates

/-- Uniform density on the complete source group, including its central sign. -/
theorem coefficientSpan_dense : Dense (coefficientSpan : Set C(SU2, ℂ)) := by
  have hd : Dense (coordinateAlgebra : Set C(SU2, ℂ)) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe,
      coordinateAlgebra_complete]
    rfl
  exact hd.mono coordinateAlgebra_le_coefficientSpan

theorem coefficientSpan_closure : coefficientSpan.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp coefficientSpan_dense

/-- The inclusion uses exactly the normalized Haar measure of the source
orbit construction, with no independently chosen measure. -/
theorem coefficientSpan_toLp_dense :
    Dense (Set.range (fun f : coefficientSpan =>
      ContinuousMap.toLp 2 sourceHaar ℂ f.val)) := by
  let : sourceHaar.Regular := inferInstanceAs
    ((Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).Regular)
  have hto : DenseRange
      (ContinuousMap.toLp 2 sourceHaar ℂ : C(SU2, ℂ) →L[ℂ] Lp ℂ 2 sourceHaar) :=
    ContinuousMap.toLp_denseRange ℂ sourceHaar ℂ (by norm_num)
  exact hto.dense_of_mapsTo (ContinuousMap.toLp 2 sourceHaar ℂ).continuous
    coefficientSpan_dense (fun f hf => ⟨⟨f, hf⟩, rfl⟩)

/-- The span as an actual submodule of the same source Haar `L²` space. -/
def coefficientL2Span : Submodule ℂ (Lp ℂ 2 sourceHaar) :=
  coefficientSpan.map (ContinuousMap.toLp 2 sourceHaar ℂ).toLinearMap

theorem coefficientL2Span_eq_span :
    coefficientL2Span = Submodule.span ℂ
      ((ContinuousMap.toLp 2 sourceHaar ℂ) '' coefficientGenerators) := by
  exact Submodule.map_span (ContinuousMap.toLp 2 sourceHaar ℂ).toLinearMap
    coefficientGenerators

theorem coefficientL2Span_dense : Dense (coefficientL2Span : Set (Lp ℂ 2 sourceHaar)) := by
  apply coefficientSpan_toLp_dense.mono
  rintro f ⟨g, rfl⟩
  exact Submodule.mem_map.mpr ⟨g.val, g.property, rfl⟩

theorem coefficientL2Span_closure : coefficientL2Span.topologicalClosure = ⊤ :=
  Submodule.dense_iff_topologicalClosure_eq_top.mp coefficientL2Span_dense

end GeneratedFoundations.Geometry.SourceCoefficientDensity
