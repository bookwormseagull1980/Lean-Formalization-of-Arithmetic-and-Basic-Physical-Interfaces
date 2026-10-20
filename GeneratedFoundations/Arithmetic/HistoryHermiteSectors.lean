module

public import GeneratedFoundations.Arithmetic.HistoryChiralCoordinates

/-!
# Sector projections in the original Gaussian realization

Both full arithmetic source sectors are embedded in the original Gaussian
Hilbert space. Their actual corner projections intertwine with the source
projections, and their complete ranges are the embedded sector spaces.
Their rank is twice the generated history--phase label count. The value is
calculated on the arithmetic fibre rather than copied from a physical
multiplicity.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Arithmetic.HistoryHermiteSectors

open HistoryCliffordAction HistoryComplexConnector
open Operations

def positive (N : ℕ) := fullHermiteOperator N (positiveProjection N)
def negative (N : ℕ) := fullHermiteOperator N (negativeProjection N)

theorem positive_formula (N : ℕ) : positiveProjection N =
    (1 / 2 : ℂ) • (1 + sourceGrading N) := by
  have hs := projections_sum N
  have hg := HistoryChiralBlocks.grading_eq_projections N
  have hg' : sourceGrading N = positiveProjection N - negativeProjection N :=
    (action N).injective (by simpa only [map_sub] using hg)
  rw [← hs, hg']
  module

theorem negative_formula (N : ℕ) : negativeProjection N =
    (1 / 2 : ℂ) • (1 - sourceGrading N) := by
  have hs := projections_sum N
  have hg := HistoryChiralBlocks.grading_eq_projections N
  have hg' : sourceGrading N = positiveProjection N - negativeProjection N :=
    (action N).injective (by simpa only [map_sub] using hg)
  rw [← hs, hg']
  module

theorem coordinates_positive (N : ℕ) :
    HistoryChiralCoordinates.fullMatrixCoordinates N (action N (positiveProjection N)) =
      SourceCliffordComplex.colourPositive (Fintype.card (HistoryLabel N)) := by
  rw [HistoryChiralCoordinates.fullMatrixCoordinates_action, positive_formula,
    map_smul, map_add, map_one, HistoryChiralCoordinates.matrixCoordinates_grading,
    SourceCliffordComplex.colourPositive_formula]

theorem coordinates_negative (N : ℕ) :
    HistoryChiralCoordinates.fullMatrixCoordinates N (action N (negativeProjection N)) =
      SourceCliffordComplex.colourNegative (Fintype.card (HistoryLabel N)) := by
  rw [HistoryChiralCoordinates.fullMatrixCoordinates_action, negative_formula,
    map_smul, map_sub, map_one, HistoryChiralCoordinates.matrixCoordinates_grading,
    SourceCliffordComplex.colourNegative_formula]

theorem positive_intertwines (N : ℕ) (x : Space N) :
    positive N (hermiteIsometry N x) =
      hermiteIsometry N (action N (positiveProjection N) x) :=
  (hermiteIsometry_intertwines N _ x).symm

theorem negative_intertwines (N : ℕ) (x : Space N) :
    negative N (hermiteIsometry N x) =
      hermiteIsometry N (action N (negativeProjection N) x) :=
  (hermiteIsometry_intertwines N _ x).symm

theorem positive_fixes_iff (N : ℕ) (x : Space N) :
    positive N (hermiteIsometry N x) = hermiteIsometry N x ↔
      action N (positiveProjection N) x = x := by
  rw [positive_intertwines]
  exact (hermiteIsometry N).injective.eq_iff

theorem negative_fixes_iff (N : ℕ) (x : Space N) :
    negative N (hermiteIsometry N x) = hermiteIsometry N x ↔
      action N (negativeProjection N) x = x := by
  rw [negative_intertwines]
  exact (hermiteIsometry N).injective.eq_iff

def positiveEmbedding (N : ℕ) : SectorSpace N →ₗ[ℂ]
    Correlation.ComplexGaussianStates.ComplexL2 :=
  (hermiteIsometry N).toLinearMap.comp (positiveInclusion N)

def negativeEmbedding (N : ℕ) : SectorSpace N →ₗ[ℂ]
    Correlation.ComplexGaussianStates.ComplexL2 :=
  (hermiteIsometry N).toLinearMap.comp (negativeInclusion N)

theorem positiveEmbedding_injective (N : ℕ) : Function.Injective (positiveEmbedding N) := by
  intro x y h
  have he := (hermiteIsometry N).injective h
  apply PiLp.ext
  rintro ⟨h, i⟩
  exact congrArg (fun z : Space N => z (h, Sum.inl i)) he

theorem negativeEmbedding_injective (N : ℕ) : Function.Injective (negativeEmbedding N) := by
  intro x y h
  have he := (hermiteIsometry N).injective h
  apply PiLp.ext
  rintro ⟨h, i⟩
  exact congrArg (fun z : Space N => z (h, Sum.inr i)) he

theorem positive_reconstruct (N : ℕ) (x : Space N) :
    positiveInclusion N (sectorCoordinates N x).fst = action N (positiveProjection N) x := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  cases i with
  | inl i => exact (positive_left N x h i).symm
  | inr i => exact (positive_right N x h i).symm

theorem negative_reconstruct (N : ℕ) (x : Space N) :
    negativeInclusion N (sectorCoordinates N x).snd = action N (negativeProjection N) x := by
  apply PiLp.ext
  rintro ⟨h, i⟩
  cases i with
  | inl i => exact (negative_left N x h i).symm
  | inr i => exact (negative_right N x h i).symm

theorem projection_eq_identityCorner (N : ℕ) :
    FiniteHermiteCorner.projection Source.CanonicalRealization.width_pos
      (hermiteMode N) = fullHermiteOperator N 1 := by
  apply SourceMatrixUnits.end_ext Source.CanonicalRealization.width_pos
  intro n
  by_cases hn : ∃ i : Index N, hermiteMode N i = n
  · obtain ⟨i, rfl⟩ := hn
    rw [FiniteHermiteCorner.projection_state _ _ (hermiteMode_injective N)]
    unfold fullHermiteOperator
    rw [map_one]
    exact (FiniteHermiteCorner.projection_state _ _
      (SourceCliffordConnector.sourceMode_injective _) (indexCoordinates N i)).symm
  · have hleft : ∀ i : Index N, hermiteMode N i ≠ n := fun i hi => hn ⟨i, hi⟩
    have hright : ∀ j : SourceCliffordConnector.ColourIndex
        (Fintype.card (HistoryLabel N)), SourceCliffordConnector.sourceMode j ≠ n := by
      intro j hj
      apply hn
      refine ⟨(indexCoordinates N).symm j, ?_⟩
      simpa [hermiteMode] using hj
    unfold FiniteHermiteCorner.projection fullHermiteOperator
    rw [FiniteHermiteCorner.corner_state_outside _ _ _ n hleft,
      FiniteHermiteCorner.corner_state_outside _ _ _ n hright]

theorem positive_range (N : ℕ) :
    LinearMap.range (positive N).toLinearMap = LinearMap.range (positiveEmbedding N) := by
  ext F
  constructor
  · rintro ⟨G, rfl⟩
    have hm := FiniteHermiteCorner.projection_mem Source.CanonicalRealization.width_pos
      (hermiteMode N) G
    rw [← HistoryChiralCoordinates.hermiteIsometry_range N] at hm
    obtain ⟨x, hx⟩ := hm
    change hermiteIsometry N x =
      FiniteHermiteCorner.projection Source.CanonicalRealization.width_pos (hermiteMode N) G at hx
    refine ⟨(sectorCoordinates N x).fst, ?_⟩
    change hermiteIsometry N (positiveInclusion N (sectorCoordinates N x).fst) = positive N G
    rw [positive_reconstruct, ← positive_intertwines, hx]
    rw [projection_eq_identityCorner]
    change (fullHermiteOperator N (positiveProjection N) * fullHermiteOperator N 1) G = _
    rw [← fullHermiteOperator_mul, mul_one]
    rfl
  · rintro ⟨x, rfl⟩
    refine ⟨positiveEmbedding N x, ?_⟩
    change positive N (hermiteIsometry N (positiveInclusion N x)) =
      hermiteIsometry N (positiveInclusion N x)
    rw [positive_intertwines]
    apply congrArg (hermiteIsometry N)
    apply PiLp.ext
    rintro ⟨h, i⟩
    cases i with
    | inl i => exact positive_left N _ h i
    | inr i => exact positive_right N _ h i

theorem negative_range (N : ℕ) :
    LinearMap.range (negative N).toLinearMap = LinearMap.range (negativeEmbedding N) := by
  ext F
  constructor
  · rintro ⟨G, rfl⟩
    have hm := FiniteHermiteCorner.projection_mem Source.CanonicalRealization.width_pos
      (hermiteMode N) G
    rw [← HistoryChiralCoordinates.hermiteIsometry_range N] at hm
    obtain ⟨x, hx⟩ := hm
    change hermiteIsometry N x =
      FiniteHermiteCorner.projection Source.CanonicalRealization.width_pos (hermiteMode N) G at hx
    refine ⟨(sectorCoordinates N x).snd, ?_⟩
    change hermiteIsometry N (negativeInclusion N (sectorCoordinates N x).snd) = negative N G
    rw [negative_reconstruct, ← negative_intertwines, hx]
    rw [projection_eq_identityCorner]
    change (fullHermiteOperator N (negativeProjection N) * fullHermiteOperator N 1) G = _
    rw [← fullHermiteOperator_mul, mul_one]
    rfl
  · rintro ⟨x, rfl⟩
    refine ⟨negativeEmbedding N x, ?_⟩
    change negative N (hermiteIsometry N (negativeInclusion N x)) =
      hermiteIsometry N (negativeInclusion N x)
    rw [negative_intertwines]
    apply congrArg (hermiteIsometry N)
    apply PiLp.ext
    rintro ⟨h, i⟩
    cases i with
    | inl i => exact negative_left N _ h i
    | inr i => exact negative_right N _ h i

theorem positive_finrank (N : ℕ) :
    Module.finrank ℂ (LinearMap.range (positive N).toLinearMap) =
      2 * Fintype.card (HistoryLabel N) := by
  rw [positive_range, LinearMap.finrank_range_of_inj (positiveEmbedding_injective N)]
  exact sector_dimension N

theorem negative_finrank (N : ℕ) :
    Module.finrank ℂ (LinearMap.range (negative N).toLinearMap) =
      2 * Fintype.card (HistoryLabel N) := by
  rw [negative_range, LinearMap.finrank_range_of_inj (negativeEmbedding_injective N)]
  exact sector_dimension N

end GeneratedFoundations.Arithmetic.HistoryHermiteSectors
