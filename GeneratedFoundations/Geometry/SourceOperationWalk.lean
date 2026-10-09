module

public import GeneratedFoundations.Geometry.SourceStepExpansion
public import GeneratedFoundations.Geometry.SourceSchurOrthogonality
public import Mathlib.MeasureTheory.Group.IntegralConvolution
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Probability laws of independently composed source operations

The step law is the measurable pushforward of the original direction law
by the actual source step. Repeated multiplicative convolution records its
independent ordered composition. The representation mean of convolution is
proved using the actual representation law and Bochner Fubini, yielding the
power of the previously defined single-step mean.

A recursive finite Cartesian sample space carries the independent product
law itself. Its source-product pushforward is identified with the same walk
law. No matrix-coefficient product rule is assumed. The probability and norm
statements here require no moment or centering condition on the direction law.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceAxisDifferentiation
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceStepExpansion
open GeneratedFoundations.Geometry.SourceSchurOrthogonality

namespace GeneratedFoundations.Geometry.SourceOperationWalk

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.secondCountableTopology_induced SU2
    (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val

local instance : MeasurableMul₂ SU2 := ⟨continuous_mul.measurable⟩

local instance (m : ℕ) : CompleteSpace (HilbertCarrier m) :=
  FiniteDimensional.complete ℂ (HilbertCarrier m)

local instance (m : ℕ) : NormedAddCommGroup (End m) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (m : ℕ) : NormedRing (End m) :=
  ContinuousLinearMap.toNormedRing

local instance (m : ℕ) : NormedSpace ℂ (End m) :=
  ContinuousLinearMap.toNormedSpace

local instance (m : ℕ) : NormedSpace ℝ (End m) :=
  ContinuousLinearMap.toNormedSpace

local instance (m : ℕ) : NormedAlgebra ℂ (End m) :=
  ContinuousLinearMap.toNormedAlgebra

local instance (m : ℕ) : NormedAlgebra ℝ (End m) :=
  NormedAlgebra.restrictScalars ℝ ℂ (End m)

private theorem integral_operator_inner {X H : Type*} [MeasurableSpace X]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedSpace ℝ H] [IsScalarTower ℝ ℂ H]
    (ν : Measure X) (f : X → H →L[ℂ] H) (hf : Integrable f ν) (v w : H) :
    (∫ x, inner ℂ v (f x w) ∂ν) = inner ℂ v ((∫ x, f x ∂ν) w) :=
  ((innerSL ℂ v).comp (ContinuousLinearMap.apply ℂ H w)).integral_comp_comm hf

private theorem basis_inner_scalar {H I : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : OrthonormalBasis I ℂ H) (i j : I) (s : ℂ) :
    inner ℂ (b i) (s • b j) = s * (if i = j then 1 else 0) := by
  rw [inner_smul_right, b.inner_eq_ite]

private theorem integral_products {X E : Type*} [MeasurableSpace X]
    [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
    (ν κ : Measure X) (f : X → E) (hν : Integrable f ν) (hκ : Integrable f κ) :
    (∫ x, ∫ y, f x * f y ∂κ ∂ν) = (∫ x, f x ∂ν) * (∫ y, f y ∂κ) := by
  simp_rw [integral_const_mul_of_integrable hκ]
  exact integral_mul_const_of_integrable hν

/-- The bounded operator of the actual source representation. -/
def groupOperator (m : ℕ) (U : SU2) : End m :=
  (unitaryAction m U).toLinearIsometry.toContinuousLinearMap

@[simp] theorem groupOperator_apply (m : ℕ) (U : SU2) (v : HilbertCarrier m) :
    groupOperator m U v = unitaryAction m U v := rfl

@[simp] theorem groupOperator_one (m : ℕ) : groupOperator m 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  exact unitaryAction_one_apply m v

theorem groupOperator_mul (m : ℕ) (U V : SU2) :
    groupOperator m (U * V) = groupOperator m U * groupOperator m V := by
  apply ContinuousLinearMap.ext
  intro v
  exact unitaryAction_mul_apply m U V v

theorem groupOperator_continuous (m : ℕ) : Continuous (groupOperator m) := by
  apply continuous_clm_apply.mpr
  intro v
  exact unitaryAction_orbit_continuous m v

theorem groupOperator_norm_le_one (m : ℕ) (U : SU2) : ‖groupOperator m U‖ ≤ 1 :=
  (unitaryAction m U).toLinearIsometry.norm_toContinuousLinearMap_le

theorem groupOperator_integrable (ν : Measure SU2) [IsFiniteMeasure ν] (m : ℕ) :
    Integrable (groupOperator m) ν := by
  apply (integrable_const (1 : ℝ)).mono'
    (groupOperator_continuous m).aestronglyMeasurable
  exact Eventually.of_forall (groupOperator_norm_le_one m)

def groupMean (ν : Measure SU2) (m : ℕ) : End m := ∫ U, groupOperator m U ∂ν

theorem groupMean_norm_le_one (ν : Measure SU2) [IsProbabilityMeasure ν] (m : ℕ) :
    ‖groupMean ν m‖ ≤ 1 := by
  simpa only [groupMean, probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const
      (μ := ν) (Eventually.of_forall (groupOperator_norm_le_one m)))

/-- The order of the two factors is the order of source composition. -/
theorem groupMean_mconv (ν κ : Measure SU2) [IsFiniteMeasure ν] [IsFiniteMeasure κ]
    (m : ℕ) : groupMean (ν ∗ₘ κ) m = groupMean ν m * groupMean κ m := by
  rw [groupMean, integral_mconv (groupOperator_integrable (ν ∗ₘ κ) m)]
  simp_rw [groupOperator_mul]
  exact integral_products ν κ (groupOperator m)
    (groupOperator_integrable ν m) (groupOperator_integrable κ m)

@[simp] theorem groupMean_dirac (U : SU2) (m : ℕ) :
    groupMean (Measure.dirac U) m = groupOperator m U := by
  simp [groupMean]

/-- Matrix entries of the existing source basis are the entries of the
Bochner mean, with the fixed vector in the conjugate-linear inner-product slot. -/
theorem groupMean_matrixEntry (ν : Measure SU2) [IsFiniteMeasure ν] (m : ℕ)
    (i j : Fin (m + 1)) :
    (∫ U, matrixEntry m i j U ∂ν) =
      inner ℂ (sourceBasis m i) (groupMean ν m (sourceBasis m j)) := by
  simpa only [matrixEntry, matrixCoefficient_apply, groupOperator_apply, groupMean] using!
    integral_operator_inner ν (groupOperator m) (groupOperator_integrable ν m)
      (sourceBasis m i) (sourceBasis m j)

theorem operator_ext_matrixEntries (m : ℕ) {A B : End m}
    (h : ∀ i j : Fin (m + 1),
      inner ℂ (sourceBasis m i) (A (sourceBasis m j)) =
        inner ℂ (sourceBasis m i) (B (sourceBasis m j))) : A = B := by
  apply ContinuousLinearMap.coe_injective
  apply (sourceBasis m).toBasis.ext
  intro j
  apply (sourceBasis m).repr.injective
  apply PiLp.ext
  intro i
  simpa only [OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis] using! h i j

/-- Scalar matrix entries determine the whole mean on the original carrier. -/
theorem groupMean_eq_scalar (ν : Measure SU2) [IsFiniteMeasure ν] (m : ℕ) (s : ℂ)
    (h : ∀ i j : Fin (m + 1),
      (∫ U, matrixEntry m i j U ∂ν) = s * (if i = j then 1 else 0)) :
    groupMean ν m = s • (1 : End m) := by
  apply operator_ext_matrixEntries m
  intro i j
  rw [← groupMean_matrixEntry, h]
  simpa only [_root_.smul_apply, one_apply_eq_self] using!
    (basis_inner_scalar (sourceBasis m) i j s).symm

theorem step_measurable (ε : ℝ) :
    Measurable (fun ξ : Direction => SourceDirectionalStep.step ξ ε) :=
  (SourceDirectionalStep.step_joint_continuous.comp
    (continuous_id.prodMk continuous_const)).measurable

/-- The original direction law is pushed forward by the actual group-valued step. -/
def stepLaw (μ : Measure Direction) (ε : ℝ) : Measure SU2 :=
  μ.map (fun ξ => SourceDirectionalStep.step ξ ε)

theorem stepLaw_apply (μ : Measure Direction) (ε : ℝ) (s : Set SU2)
    (hs : MeasurableSet s) :
    stepLaw μ ε s = μ {ξ | SourceDirectionalStep.step ξ ε ∈ s} :=
  Measure.map_apply (step_measurable ε) hs

instance stepLaw_isProbability (μ : Measure Direction) [IsProbabilityMeasure μ] (ε : ℝ) :
    IsProbabilityMeasure (stepLaw μ ε) := by
  unfold stepLaw
  infer_instance

theorem stepLaw_mean (μ : Measure Direction) (m : ℕ) (ε : ℝ) :
    groupMean (stepLaw μ ε) m = meanStep μ m ε := by
  rw [groupMean, stepLaw, integral_map (step_measurable ε).aemeasurable
    (groupOperator_continuous m).aestronglyMeasurable]
  rfl

theorem stepMatrix_integrable_probability (μ : Measure Direction) [IsProbabilityMeasure μ]
    (m : ℕ) (ε : ℝ) : Integrable (fun ξ => stepMatrix m ξ ε) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    ((groupOperator_continuous m).comp
      (SourceDirectionalStep.step_joint_continuous.comp
        (continuous_id.prodMk continuous_const))).aestronglyMeasurable
  exact Eventually.of_forall fun ξ =>
    groupOperator_norm_le_one m (SourceDirectionalStep.step ξ ε)

theorem meanStep_norm_le_one (μ : Measure Direction) [IsProbabilityMeasure μ]
    (m : ℕ) (ε : ℝ) : ‖meanStep μ m ε‖ ≤ 1 := by
  rw [← stepLaw_mean]
  exact groupMean_norm_le_one (stepLaw μ ε) m

/-- New independent operations are appended on the right. -/
def walkLaw (μ : Measure Direction) (ε : ℝ) : ℕ → Measure SU2
  | 0 => Measure.dirac 1
  | N + 1 => walkLaw μ ε N ∗ₘ stepLaw μ ε

@[simp] theorem walkLaw_zero (μ : Measure Direction) (ε : ℝ) :
    walkLaw μ ε 0 = Measure.dirac 1 := rfl

theorem walkLaw_succ (μ : Measure Direction) (ε : ℝ) (N : ℕ) :
    walkLaw μ ε (N + 1) = walkLaw μ ε N ∗ₘ stepLaw μ ε := rfl

instance walkLaw_isProbability (μ : Measure Direction) [IsProbabilityMeasure μ]
    (ε : ℝ) (N : ℕ) : IsProbabilityMeasure (walkLaw μ ε N) := by
  induction N with
  | zero => change IsProbabilityMeasure (Measure.dirac (1 : SU2)); infer_instance
  | succ N ih =>
      let := ih
      change IsProbabilityMeasure (walkLaw μ ε N ∗ₘ stepLaw μ ε)
      infer_instance

def walkProbability (μ : Measure Direction) [IsProbabilityMeasure μ]
    (ε : ℝ) (N : ℕ) : ProbabilityMeasure SU2 := ⟨walkLaw μ ε N, inferInstance⟩

@[simp] theorem coe_walkProbability (μ : Measure Direction) [IsProbabilityMeasure μ]
    (ε : ℝ) (N : ℕ) : (walkProbability μ ε N : Measure SU2) = walkLaw μ ε N := rfl

/-- The expectation-power identity is derived from the actual source law. -/
theorem walkLaw_mean_eq_power (μ : Measure Direction) [IsProbabilityMeasure μ]
    (m : ℕ) (ε : ℝ) (N : ℕ) :
    groupMean (walkLaw μ ε N) m = meanStep μ m ε ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [walkLaw_succ, groupMean_mconv, ih, stepLaw_mean, pow_succ]

theorem walkLaw_matrixEntry (μ : Measure Direction) [IsProbabilityMeasure μ]
    (m : ℕ) (ε : ℝ) (N : ℕ) (i j : Fin (m + 1)) :
    (∫ U, matrixEntry m i j U ∂walkLaw μ ε N) =
      inner ℂ (sourceBasis m i) ((meanStep μ m ε ^ N) (sourceBasis m j)) := by
  rw [groupMean_matrixEntry, walkLaw_mean_eq_power]

/-- The finite sample space is a genuine Cartesian product of direction samples. -/
def Sample : ℕ → Type
  | 0 => Unit
  | N + 1 => Sample N × Direction

instance sampleMeasurableSpace (N : ℕ) : MeasurableSpace (Sample N) := by
  induction N with
  | zero => exact inferInstanceAs (MeasurableSpace Unit)
  | succ N ih =>
      letI := ih
      exact inferInstanceAs (MeasurableSpace (Sample N × Direction))

/-- Each new coordinate has the same fixed direction law and is independent
of all previous coordinates through the product measure. -/
def sampleLaw (μ : Measure Direction) : (N : ℕ) → Measure (Sample N)
  | 0 => Measure.dirac ()
  | N + 1 => (sampleLaw μ N).prod μ

instance sampleLaw_isProbability (μ : Measure Direction) [IsProbabilityMeasure μ]
    (N : ℕ) : IsProbabilityMeasure (sampleLaw μ N) := by
  induction N with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ N ih =>
      let := ih
      change IsProbabilityMeasure ((sampleLaw μ N).prod μ)
      infer_instance

/-- The order here is the same right-appending order as in `walkLaw`. -/
def sampleProduct (ε : ℝ) : (N : ℕ) → Sample N → SU2
  | 0, _ => 1
  | N + 1, p => sampleProduct ε N p.1 * SourceDirectionalStep.step p.2 ε

theorem sampleProduct_measurable (ε : ℝ) (N : ℕ) : Measurable (sampleProduct ε N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      exact (ih.comp measurable_fst).mul ((step_measurable ε).comp measurable_snd)

/-- Recursive convolution is exactly the pushforward of independent finite
direction samples by their actual ordered source product. -/
theorem sampleProduct_pushforward (μ : Measure Direction) [IsProbabilityMeasure μ]
    (ε : ℝ) (N : ℕ) :
    (sampleLaw μ N).map (sampleProduct ε N) = walkLaw μ ε N := by
  induction N with
  | zero =>
      change (Measure.dirac ()).map (sampleProduct ε 0) = Measure.dirac (1 : SU2)
      exact Measure.map_dirac' (sampleProduct_measurable ε 0) ()
  | succ N ih =>
      change ((sampleLaw μ N).prod μ).map
        (fun p : Sample N × Direction =>
          sampleProduct ε N p.1 * SourceDirectionalStep.step p.2 ε) =
        walkLaw μ ε N ∗ₘ stepLaw μ ε
      rw [← ih, stepLaw, Measure.mconv,
        Measure.map_prod_map (sampleLaw μ N) μ
          (sampleProduct_measurable ε N) (step_measurable ε),
        Measure.map_map measurable_mul
          ((sampleProduct_measurable ε N).prodMap (step_measurable ε))]
      rfl

/-- The finite independent sample experiment and the convolution experiment
have the same representation mean. -/
theorem sampleProduct_mean_eq_power (μ : Measure Direction) [IsProbabilityMeasure μ]
    (m : ℕ) (ε : ℝ) (N : ℕ) :
    (∫ p : Sample N, groupOperator m (sampleProduct ε N p) ∂sampleLaw μ N) =
      meanStep μ m ε ^ N := by
  rw [← walkLaw_mean_eq_power μ m ε N, ← sampleProduct_pushforward]
  exact (integral_map (sampleProduct_measurable ε N).aemeasurable
    (groupOperator_continuous m).aestronglyMeasurable).symm

end GeneratedFoundations.Geometry.SourceOperationWalk
