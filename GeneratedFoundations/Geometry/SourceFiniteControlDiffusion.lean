module

public import GeneratedFoundations.Geometry.SourceFiniteControlLaw
public import GeneratedFoundations.Geometry.SourceFiniteControlLifts
public import GeneratedFoundations.Geometry.SourceConvolutionAction
public import GeneratedFoundations.Geometry.SourceHeatKernelDensity

/-!
# Independent finite controls and the round diffusion limit

Each operation samples a direction and an independent uniform control.
The selected source lift conjugates the directional step. The ordered
product of these operations has the same law as the walk driven by the
averaged direction measure. Its covariance calibration therefore gives
the round heat limit, with the closed Casimir generator and its full domain.

The input direction law needs finite second moments and positive total
second moment. It need not be centred or have nonsingular covariance.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter
open scoped Topology NNReal
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceDirectionalGenerator
open GeneratedFoundations.Geometry.SourceDirectionalMoments
open GeneratedFoundations.Geometry.SourceFiniteRotations
open GeneratedFoundations.Geometry.SourceFiniteControlLaw
open GeneratedFoundations.Geometry.SourceFiniteControlLifts
open GeneratedFoundations.Geometry.SourceOperationWalk
open GeneratedFoundations.Geometry.SourceOperationDiffusion
open GeneratedFoundations.Geometry.SourceBlockPowerLimit
open GeneratedFoundations.Geometry.SourceCompleteCoefficients
open GeneratedFoundations.Geometry.SourceWeakConvergence
open GeneratedFoundations.Geometry.SourceConvolutionAction
open GeneratedFoundations.Geometry.SourceHeatSemigroup
open GeneratedFoundations.Geometry.SourceHeatSeries
open GeneratedFoundations.Geometry.SourceHeatKernelDensity
open GeneratedFoundations.Geometry.SourceSymmetricUnitary

namespace GeneratedFoundations.Geometry.SourceFiniteControlDiffusion

local instance : SecondCountableTopology (Matrix (Fin 2) (Fin 2) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → ℂ))

local instance : SecondCountableTopology SU2 :=
  TopologicalSpace.secondCountableTopology_induced SU2
    (Matrix (Fin 2) (Fin 2) ℂ) Subtype.val

local instance : MeasurableMul₂ SU2 := ⟨continuous_mul.measurable⟩

abbrev OneSample := Control × Direction

def conjugatedStep (ε : ℝ) (p : OneSample) : SU2 :=
  controlLift p.1 * SourceDirectionalStep.step p.2 ε * (controlLift p.1)⁻¹

theorem conjugatedStep_eq (ε : ℝ) (p : OneSample) :
    conjugatedStep ε p = SourceDirectionalStep.step (rotatedDirection p) ε :=
  controlLift_step_conj p.1 p.2 ε

theorem conjugatedStep_measurable (ε : ℝ) : Measurable (conjugatedStep ε) := by
  have he : conjugatedStep ε =
      (fun ξ : Direction => SourceDirectionalStep.step ξ ε) ∘ rotatedDirection :=
    funext (conjugatedStep_eq ε)
  rw [he]
  exact (step_measurable ε).comp rotatedDirection_measurable

theorem singleStep_pushforward (μ : Measure Direction) [IsProbabilityMeasure μ] (ε : ℝ) :
    (oneSampleLaw μ).map (conjugatedStep ε) = stepLaw (averagedLaw μ) ε := by
  have he : conjugatedStep ε =
      (fun ξ : Direction => SourceDirectionalStep.step ξ ε) ∘ rotatedDirection :=
    funext (conjugatedStep_eq ε)
  rw [he, ← Measure.map_map (step_measurable ε) rotatedDirection_measurable,
    oneSample_pushforward]
  rfl

def IndependentSample : ℕ → Type
  | 0 => Unit
  | N + 1 => IndependentSample N × OneSample

instance independentSampleMeasurableSpace (N : ℕ) : MeasurableSpace (IndependentSample N) := by
  induction N with
  | zero => exact inferInstanceAs (MeasurableSpace Unit)
  | succ N ih =>
      letI := ih
      exact inferInstanceAs (MeasurableSpace (IndependentSample N × OneSample))

/-- The product measure redraws both the direction and the control at every step. -/
def independentLaw (μ : Measure Direction) : (N : ℕ) → Measure (IndependentSample N)
  | 0 => Measure.dirac ()
  | N + 1 => (independentLaw μ N).prod (oneSampleLaw μ)

instance independentLaw_isProbability (μ : Measure Direction) [IsProbabilityMeasure μ]
    (N : ℕ) : IsProbabilityMeasure (independentLaw μ N) := by
  induction N with
  | zero => change IsProbabilityMeasure (Measure.dirac ()); infer_instance
  | succ N ih =>
      let := ih
      change IsProbabilityMeasure ((independentLaw μ N).prod (oneSampleLaw μ))
      infer_instance

def operationProduct (ε : ℝ) : (N : ℕ) → IndependentSample N → SU2
  | 0, _ => 1
  | N + 1, p => operationProduct ε N p.1 * conjugatedStep ε p.2

theorem operationProduct_measurable (ε : ℝ) (N : ℕ) :
    Measurable (operationProduct ε N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih =>
      exact (ih.comp measurable_fst).mul
        ((conjugatedStep_measurable ε).comp measurable_snd)

theorem operationProduct_pushforward (μ : Measure Direction) [IsProbabilityMeasure μ]
    (ε : ℝ) (N : ℕ) :
    (independentLaw μ N).map (operationProduct ε N) = walkLaw (averagedLaw μ) ε N := by
  induction N with
  | zero =>
      change (Measure.dirac ()).map (operationProduct ε 0) = Measure.dirac (1 : SU2)
      exact Measure.map_dirac' (operationProduct_measurable ε 0) ()
  | succ N ih =>
      change ((independentLaw μ N).prod (oneSampleLaw μ)).map
        (fun p : IndependentSample N × OneSample =>
          operationProduct ε N p.1 * conjugatedStep ε p.2) =
        walkLaw (averagedLaw μ) ε N ∗ₘ stepLaw (averagedLaw μ) ε
      rw [← ih, ← singleStep_pushforward μ ε, Measure.mconv,
        Measure.map_prod_map (independentLaw μ N) (oneSampleLaw μ)
          (operationProduct_measurable ε N) (conjugatedStep_measurable ε),
        Measure.map_map measurable_mul
          ((operationProduct_measurable ε N).prodMap (conjugatedStep_measurable ε))]
      rfl

def experiment (μ : Measure Direction) [IsProbabilityMeasure μ] (ε : ℝ) (N : ℕ) :
    ProbabilityMeasure SU2 :=
  ⟨(independentLaw μ N).map (operationProduct ε N), inferInstance⟩

theorem experiment_eq_walk (μ : Measure Direction) [IsProbabilityMeasure μ]
    (ε : ℝ) (N : ℕ) : experiment μ ε N = walkProbability (averagedLaw μ) ε N :=
  ProbabilityMeasure.toMeasure_injective (operationProduct_pushforward μ ε N)

/-- The step budget depends on the total input second moment. -/
theorem calibrated_stepCount (μ : Measure Direction) (t ε : ℝ) :
    stepCount (covariance μ) t ε =
      ⌊24 * t / ((∫ ξ : Direction, sizeSq ξ ∂μ) * ε ^ 2)⌋₊ := by
  rw [stepCount_eq_floor]
  congr 1
  unfold covariance
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

variable {μ : Measure Direction} [IsProbabilityMeasure μ]
  (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ)
  (hpos : 0 < ∫ ξ : Direction, sizeSq ξ ∂μ)

def limitLaw (t : ℝ) (ht : 0 ≤ t) : ProbabilityMeasure SU2 :=
  heatLaw (centeredIsotropic h2 hpos) t ht

theorem experiment_tendsto (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun ε : ℝ => experiment μ ε (stepCount (covariance μ) t ε))
      (𝓝[≠] 0) (𝓝 (limitLaw h2 hpos t ht)) := by
  simpa only [experiment_eq_walk, limitLaw] using
    operation_walk_tendsto_heat (centeredIsotropic h2 hpos) t ht

theorem limitLaw_entries (t : ℝ) (ht : 0 ≤ t) :
    HasEntryIntegrals (limitLaw h2 hpos t ht) (heatCoefficient t) :=
  heatLaw_entries (centeredIsotropic h2 hpos) t ht

theorem limitLaw_unique (t : ℝ) (ht : 0 ≤ t) (ρ : ProbabilityMeasure SU2)
    (hρ : HasEntryIntegrals ρ (heatCoefficient t)) : ρ = limitLaw h2 hpos t ht :=
  hasEntryIntegrals_unique hρ (limitLaw_entries h2 hpos t ht)

/-- Different fixed input laws give the same covariance-calibrated limit. -/
theorem limitLaw_independent {ν : Measure Direction} [IsProbabilityMeasure ν]
    (k2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 ν)
    (kpos : 0 < ∫ ξ : Direction, sizeSq ξ ∂ν) (t : ℝ) (ht : 0 ≤ t) :
    limitLaw h2 hpos t ht = limitLaw k2 kpos t ht :=
  heatLaw_independent (centeredIsotropic h2 hpos) (centeredIsotropic k2 kpos) t ht

theorem limitLaw_convolution (t : ℝ≥0) :
    action (limitLaw h2 hpos t t.property) = heat t :=
  action_heatLaw_eq_heat (centeredIsotropic h2 hpos) t

theorem limitLaw_rightGenerator_iff (f g : SourceL2) :
    Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ : ℂ) •
      (action (limitLaw h2 hpos t t.property) f - f)) (𝓝[>] 0) (𝓝 g) ↔
      ∃ hf : f ∈ SourceCasimirClosure.operator.domain,
        g = -(SourceCasimirClosure.operator ⟨f, hf⟩) :=
  action_heatLaw_rightGenerator_iff (centeredIsotropic h2 hpos) f g

theorem limitLaw_density (t : ℝ) (ht : 0 < t) :
    (limitLaw h2 hpos t ht.le : Measure SU2) =
      sourceHaar.withDensity (fun U => ENNReal.ofReal (heatKernel t U).re) :=
  heatLaw_eq_withDensity (centeredIsotropic h2 hpos) t ht

/-- Finite positive total second moment suffices for the independently
controlled experiment to converge to the uniquely determined heat law. -/
theorem finiteVariance_operationWalk_tendsto_heat
    (hi : Integrable sizeSq μ) (hp : 0 < ∫ ξ : Direction, sizeSq ξ ∂μ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃! ρ : ProbabilityMeasure SU2,
      HasEntryIntegrals ρ (heatCoefficient t) ∧
        Tendsto (fun ε : ℝ => experiment μ ε
          ⌊24 * t / ((∫ ξ : Direction, sizeSq ξ ∂μ) * ε ^ 2)⌋₊)
          (𝓝[≠] 0) (𝓝 ρ) := by
  let hcoords := coordinate_memLp_of_integrable_sizeSq hi
  refine ⟨limitLaw hcoords hp t ht, ⟨limitLaw_entries hcoords hp t ht, ?_⟩, ?_⟩
  · simpa only [calibrated_stepCount] using experiment_tendsto hcoords hp t ht
  · intro ρ hρ
    exact limitLaw_unique hcoords hp t ht ρ hρ.1

end GeneratedFoundations.Geometry.SourceFiniteControlDiffusion
