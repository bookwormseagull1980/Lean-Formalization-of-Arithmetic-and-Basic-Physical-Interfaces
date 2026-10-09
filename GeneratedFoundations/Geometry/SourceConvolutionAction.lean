module

public import GeneratedFoundations.Geometry.SourceOperationDiffusion
public import GeneratedFoundations.Geometry.SourceHeatSemigroup
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual probability convolution on the original source Haar space

Right multiplication preserves the original probability Haar measure.
Its action on `L²` is therefore an isometry, and its strongly continuous
orbit can be integrated against any Borel probability law. This constructs
the convolution contraction directly, before any spectral identification.

On continuous functions it is the pointwise integral `∫ U, f (g * U)`.
The proved representation mean of the actual diffusion law gives its
matrix-coefficient multipliers. Completeness then identifies this actual
convolution with the already constructed source Casimir heat semigroup.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceSchurOrthogonality
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceOperationWalk
open GeneratedFoundations.Geometry.SourceOperationDiffusion
open GeneratedFoundations.Geometry.SourceHeatSemigroup

namespace GeneratedFoundations.Geometry.SourceConvolutionAction

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.secondCountableTopology_induced SU2
    (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val

local instance : sourceHaar.Regular := inferInstanceAs
  ((Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)).Regular)

local instance (m : ℕ) : CompleteSpace (HilbertCarrier m) :=
  FiniteDimensional.complete ℂ (HilbertCarrier m)

local instance (m : ℕ) : NormedAddCommGroup (End m) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (m : ℕ) : NormedSpace ℂ (End m) :=
  ContinuousLinearMap.toNormedSpace

local instance (m : ℕ) : NormedSpace ℝ (End m) :=
  ContinuousLinearMap.toNormedSpace

private theorem integral_operator_inner {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    (ν : Measure X) (f : X → H →L[ℂ] H) (hf : Integrable f ν)
    (T : H →L[ℂ] H) (v a : H) :
    (∫ x, inner ℂ v (T (f x a)) ∂ν) = inner ℂ v (T ((∫ x, f x ∂ν) a)) :=
  ((innerSL ℂ v).comp (T.comp (ContinuousLinearMap.apply ℂ H a))).integral_comp_comm hf

def rightMap (U : SU2) : C(SU2, SU2) :=
  ⟨fun g => g * U, continuous_id.mul continuous_const⟩

@[simp] theorem rightMap_apply (U g : SU2) : rightMap U g = g * U := rfl

theorem rightMap_continuous : Continuous rightMap :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (continuous_snd.mul continuous_fst)

/-- Right invariance follows from uniqueness and the total mass of the
same Haar measure; commutativity of the source group is not assumed. -/
theorem rightMap_measurePreserving (U : SU2) :
    MeasurePreserving (rightMap U) sourceHaar sourceHaar := by
  refine ⟨(rightMap U).continuous.measurable, ?_⟩
  change sourceHaar.map (fun g => g * U) =
    Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts SU2)
  simpa only [TopologicalSpace.PositiveCompacts.coe_top, measure_univ, one_smul] using
    (Measure.haarMeasure_unique (sourceHaar.map (fun g => g * U))
      (⊤ : TopologicalSpace.PositiveCompacts SU2))

/-- The genuine pullback of an `L²` class by right multiplication. -/
def rightTranslation (U : SU2) : SourceL2 →ₗᵢ[ℂ] SourceL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (rightMap U) (rightMap_measurePreserving U)

theorem rightTranslation_norm (U : SU2) (f : SourceL2) :
    ‖rightTranslation U f‖ = ‖f‖ := (rightTranslation U).norm_map f

/-- Strong continuity concerns the original `L²` classes, not just a
finite coefficient truncation or the operator norm topology. -/
theorem rightTranslation_continuous (f : SourceL2) :
    Continuous (fun U => rightTranslation U f) :=
  continuous_const.compMeasurePreservingLp rightMap_continuous
    rightMap_measurePreserving (by norm_num)

theorem rightTranslation_integrable (ν : ProbabilityMeasure SU2) (f : SourceL2) :
    Integrable (fun U => rightTranslation U f) (ν : Measure SU2) := by
  apply (integrable_const ‖f‖).mono'
    (rightTranslation_continuous f).aestronglyMeasurable
  exact Eventually.of_forall fun U => (rightTranslation_norm U f).le

def actionLinear (ν : ProbabilityMeasure SU2) : SourceL2 →ₗ[ℂ] SourceL2 where
  toFun f := ∫ U, rightTranslation U f ∂(ν : Measure SU2)
  map_add' f g := by
    simp only [map_add]
    exact integral_add (rightTranslation_integrable ν f) (rightTranslation_integrable ν g)
  map_smul' c f := by
    simp only [map_smul, integral_smul, RingHom.id_apply]

theorem actionLinear_norm_le (ν : ProbabilityMeasure SU2) (f : SourceL2) :
    ‖actionLinear ν f‖ ≤ ‖f‖ := by
  change ‖∫ U, rightTranslation U f ∂(ν : Measure SU2)‖ ≤ ‖f‖
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := (ν : Measure SU2))
      (Eventually.of_forall fun U => (rightTranslation_norm U f).le))

/-- Probability convolution is constructed by averaging actual Haar
isometries. Its norm bound is proved independently of the heat spectrum. -/
def action (ν : ProbabilityMeasure SU2) : SourceL2 →L[ℂ] SourceL2 :=
  (actionLinear ν).mkContinuous 1 (by
    intro f
    simpa only [one_mul] using actionLinear_norm_le ν f)

@[simp] theorem action_apply (ν : ProbabilityMeasure SU2) (f : SourceL2) :
    action ν f = ∫ U, rightTranslation U f ∂(ν : Measure SU2) := rfl

theorem action_norm_le (ν : ProbabilityMeasure SU2) (f : SourceL2) :
    ‖action ν f‖ ≤ ‖f‖ := actionLinear_norm_le ν f

theorem action_opNorm_le (ν : ProbabilityMeasure SU2) : ‖action ν‖ ≤ 1 :=
  (action ν).opNorm_le_bound zero_le_one (fun f => by
    simpa only [one_mul] using action_norm_le ν f)

def continuousTranslation (U : SU2) (f : C(SU2, ℂ)) : C(SU2, ℂ) := f.comp (rightMap U)

@[simp] theorem continuousTranslation_apply (U : SU2) (f : C(SU2, ℂ)) (g : SU2) :
    continuousTranslation U f g = f (g * U) := rfl

theorem continuousTranslation_continuous (f : C(SU2, ℂ)) :
    Continuous (fun U => continuousTranslation U f) :=
  ContinuousMap.continuous_of_continuous_uncurry _
    (f.continuous.comp (continuous_snd.mul continuous_fst))

theorem continuousTranslation_norm_le (U : SU2) (f : C(SU2, ℂ)) :
    ‖continuousTranslation U f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg f)).mpr fun g => f.norm_coe_le_norm (g * U)

theorem continuousTranslation_integrable (ν : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) :
    Integrable (fun U => continuousTranslation U f) (ν : Measure SU2) := by
  apply (integrable_const ‖f‖).mono'
    (continuousTranslation_continuous f).aestronglyMeasurable
  exact Eventually.of_forall fun U => continuousTranslation_norm_le U f

def continuousConvolution (ν : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) : C(SU2, ℂ) :=
  ∫ U, continuousTranslation U f ∂(ν : Measure SU2)

/-- The continuous representative is the actual pointwise right integral. -/
theorem continuousConvolution_apply (ν : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) (g : SU2) :
    continuousConvolution ν f g = ∫ U, f (g * U) ∂(ν : Measure SU2) :=
  ContinuousMap.integral_apply (continuousTranslation_integrable ν f) g

theorem continuousConvolution_one (ν : ProbabilityMeasure SU2) :
    continuousConvolution ν 1 = 1 := by
  ext g
  rw [continuousConvolution_apply]
  simp

/-- The directly constructed probability action preserves real,
nonnegative continuous observations. -/
theorem continuousConvolution_nonneg (ν : ProbabilityMeasure SU2) (f : C(SU2, ℂ))
    (hf : ∀ g, (f g).im = 0 ∧ 0 ≤ (f g).re) (g : SU2) :
    (continuousConvolution ν f g).im = 0 ∧ 0 ≤ (continuousConvolution ν f g).re := by
  have hi : Integrable (fun U => f (g * U)) (ν : Measure SU2) :=
    (f.continuous.comp (continuous_const.mul continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  rw [continuousConvolution_apply]
  change RCLike.im (∫ U, f (g * U) ∂(ν : Measure SU2)) = 0 ∧
    0 ≤ RCLike.re (∫ U, f (g * U) ∂(ν : Measure SU2))
  rw [← integral_im hi, ← integral_re hi]
  constructor
  · change (∫ U, (f (g * U)).im ∂(ν : Measure SU2)) = 0
    simp only [(hf _).1, integral_zero]
  · exact integral_nonneg (fun U => (hf (g * U)).2)

theorem rightTranslation_toLp (U : SU2) (f : C(SU2, ℂ)) :
    rightTranslation U (ContinuousMap.toLp 2 sourceHaar ℂ f) =
      ContinuousMap.toLp 2 sourceHaar ℂ (continuousTranslation U f) := by
  apply Lp.ext
  have hcomp := Lp.coeFn_compMeasurePreserving
    (ContinuousMap.toLp 2 sourceHaar ℂ f) (rightMap_measurePreserving U)
  have hf := (rightMap_measurePreserving U).quasiMeasurePreserving.ae
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar f)
  have hr := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) sourceHaar
    (continuousTranslation U f)
  filter_upwards [hcomp, hf, hr] with g hc hg hright
  exact hc.trans (hg.trans hright.symm)

/-- This identifies the directly constructed bounded `L²` action with
the integral representative on the dense continuous domain. -/
theorem action_toLp (ν : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) :
    action ν (ContinuousMap.toLp 2 sourceHaar ℂ f) =
      ContinuousMap.toLp 2 sourceHaar ℂ (continuousConvolution ν f) := by
  rw [action_apply]
  simp_rw [rightTranslation_toLp]
  exact (ContinuousMap.toLp 2 sourceHaar ℂ).integral_comp_comm
    (continuousTranslation_integrable ν f)

theorem continuousConvolution_L2_norm_le (ν : ProbabilityMeasure SU2) (f : C(SU2, ℂ)) :
    ‖ContinuousMap.toLp 2 sourceHaar ℂ (continuousConvolution ν f)‖ ≤
      ‖ContinuousMap.toLp 2 sourceHaar ℂ f‖ := by
  rw [← action_toLp]
  exact action_norm_le ν _

/-- Right convolution acts in the second, complex-linear coefficient
slot by the actual mean of the source representation. -/
theorem continuousConvolution_matrixCoefficient (ν : ProbabilityMeasure SU2)
    (m : ℕ) (v a : HilbertCarrier m) (g : SU2) :
    continuousConvolution ν (matrixCoefficient m v a) g =
      inner ℂ v (unitaryAction m g (groupMean (ν : Measure SU2) m a)) := by
  rw [continuousConvolution_apply]
  simp only [matrixCoefficient_apply, SourceSchurOrthogonality.action_mul]
  exact integral_operator_inner (ν : Measure SU2) (groupOperator m)
    (groupOperator_integrable (ν : Measure SU2) m) (groupOperator m g) v a

theorem continuousConvolution_heatLaw_matrixCoefficient
    {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
    (h : CenteredIsotropic μ c) (t : ℝ≥0) (m : ℕ) (v a : HilbertCarrier m) :
    continuousConvolution (heatLaw h t t.property) (matrixCoefficient m v a) =
      (decay t m : ℂ) • matrixCoefficient m v a := by
  ext g
  rw [continuousConvolution_matrixCoefficient]
  have hm := congrArg (fun T : End m => inner ℂ v (unitaryAction m g (T a)))
    (heatLaw_groupMean h (t : ℝ) t.property m)
  change inner ℂ v (unitaryAction m g (groupMean (heatLaw h t t.property : Measure SU2) m a)) =
    (Real.exp (-(t : ℝ) * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ) *
      inner ℂ v (unitaryAction m g a)
  calc
    _ = inner ℂ v ((Real.exp (-(t : ℝ) * ((m : ℝ) * ((m : ℝ) + 2))) : ℂ) •
        unitaryAction m g a) := by
      simpa only [_root_.smul_apply, one_apply_eq_self, map_smul] using! hm
    _ = _ := inner_smul_right (𝕜 := ℂ) v (unitaryAction m g a) _

theorem action_heatLaw_basis {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
    (h : CenteredIsotropic μ c) (t : ℝ≥0) (a : Index) :
    action (heatLaw h t t.property) (basisVector a) =
      (decay t a.1 : ℂ) • basisVector a := by
  rcases a with ⟨m, i, j⟩
  have he : action (heatLaw h t t.property) (entry m i j) =
      (decay t m : ℂ) • entry m i j := by
    change action (heatLaw h t t.property)
      (ContinuousMap.toLp 2 sourceHaar ℂ (matrixCoefficient m (sourceBasis m i) (sourceBasis m j))) = _
    rw [action_toLp, continuousConvolution_heatLaw_matrixCoefficient, map_smul]
    rfl
  change action (heatLaw h t t.property) (normalization m • entry m i j) =
    (decay t m : ℂ) • (normalization m • entry m i j)
  rw [map_smul, he, smul_comm]

/-- The actual process-derived probability convolution equals the heat
semigroup on the whole original source Haar space, not only on its modes. -/
theorem action_heatLaw_eq_heat {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
    (h : CenteredIsotropic μ c) (t : ℝ≥0) :
    action (heatLaw h t t.property) = heat t := by
  apply ContinuousLinearMap.ext_on matrixCoefficients_dense
  rintro _ ⟨a, rfl⟩
  rw [action_heatLaw_basis, heat_basis]

/-- The right generator of the actual operation-limit convolution has
exactly the full domain of the original closed differential Casimir. -/
theorem action_heatLaw_rightGenerator_iff
    {μ : Measure Direction} [IsProbabilityMeasure μ] {c : ℝ}
    (h : CenteredIsotropic μ c) (f g : SourceL2) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) •
      (action (heatLaw h t t.property) f - f)) (𝓝[>] 0) (𝓝 g) ↔
      ∃ hf : f ∈ SourceCasimirClosure.operator.domain,
        g = -(SourceCasimirClosure.operator ⟨f, hf⟩) := by
  simpa only [HasRightGenerator, action_heatLaw_eq_heat] using rightGenerator_iff f g

end GeneratedFoundations.Geometry.SourceConvolutionAction
