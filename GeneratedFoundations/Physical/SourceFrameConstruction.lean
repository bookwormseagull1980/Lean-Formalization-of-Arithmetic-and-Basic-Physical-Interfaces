module

public import GeneratedFoundations.Physical.SourceLocalizedMatter
public import GeneratedFoundations.Physical.SourceGaugeCocycle
public import GeneratedFoundations.Physical.SourceColourPhase

/-!
# Frames and relative transitions on the generated matter carrier

The colour, phase and pseudoreal frame classifications concern the actual
source Hilbert spaces. Their conclusions are collected without assuming a
physical bundle. The effective group acts faithfully on the same full matter
carrier.

An arbitrary unitary colour frame is factored pointwise into its determinant
phase and a determinant-one frame, with the cube-root ambiguity recorded.
This does not choose a global determinant-line reduction or identify that
phase with the independently constructed matter phase action.

A family of effective source frames determines its relative transitions by
composition. The cocycle, action and uniqueness follow from this construction.
The index and base sets label the chosen local instance; no topology or
spacetime interpretation is imposed on them. A separately supplied bundle is
handled by the chart-compatibility theorems in `SourceLocalizedMatter`.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Physical.SourceFrameConstruction

open SourceJointResponse (W L S)
open SourceChiralCarrier (FullMatter colourBasis)
open SourceLocalizedFrames (frameMatrix colourFrameMatrix)
open SourceGlobalGaugeGroup (EffectiveGroup)
open SourceGaugeUnitary (effectiveUnitaryRepresentation)
open SourceGaugeCocycle (MatterUnitary CocycleOn)

/-- Classifications and faithfulness on the already constructed source spaces. -/
structure FrameConclusions : Prop where
  colour_unitary : ∀ g : W ≃ₗᵢ[ℂ] W,
    colourFrameMatrix g ∈ Matrix.unitaryGroup (Fin 3) ℂ
  colour_specialUnitary : ∀ g : W ≃ₗᵢ[ℂ] W,
    colourFrameMatrix g ∈ Matrix.specialUnitaryGroup (Fin 3) ℂ ↔
      (colourFrameMatrix g).det = 1
  colour_realization : ∀ M : Matrix (Fin 3) (Fin 3) ℂ,
    M ∈ Matrix.unitaryGroup (Fin 3) ℂ →
      ∃! g : W ≃ₗᵢ[ℂ] W, colourFrameMatrix g = M
  colour_phase_decomposition : ∀ g : W ≃ₗᵢ[ℂ] W,
    ∃ (z : Circle) (U : SourceColourPhase.ColourSpecialUnitary),
      colourFrameMatrix g = (z : ℂ) • (U : SourceColourPhase.ColourMatrix) ∧
        (z : ℂ) ^ 3 = (colourFrameMatrix g).det
  colour_phase_ambiguity : ∀ (M : SourceColourPhase.ColourMatrix) (z w : Circle)
    (U V : SourceColourPhase.ColourSpecialUnitary),
    M = (z : ℂ) • (U : SourceColourPhase.ColourMatrix) →
    M = (w : ℂ) • (V : SourceColourPhase.ColourMatrix) →
      (w / z) ^ 3 = 1 ∧
        (V : SourceColourPhase.ColourMatrix) =
          (((w / z)⁻¹ : Circle) : ℂ) • (U : SourceColourPhase.ColourMatrix)
  phase_classification : ∀ g : L ≃ₗᵢ[ℂ] L,
    ∃! z : Circle, ∀ v : L, g v = (z : ℂ) • v
  pseudoreal_classification : ∀ g : S ≃ₗᵢ[ℂ] S,
    SourceReversalIsometry.PseudorealFrameChange g ↔
      SourceScalarConnector.sourceMatrix g.toLinearEquiv.toLinearMap ∈
        Operations.SourceSpinCornerGroup.SU2
  effective_faithful : Function.Injective effectiveUnitaryRepresentation

theorem generated_frames : FrameConclusions where
  colour_unitary := SourceLocalizedFrames.frameMatrix_unitary colourBasis
  colour_specialUnitary := SourceLocalizedFrames.colourFrameMatrix_specialUnitary_iff
  colour_realization := SourceLocalizedFrames.frameMatrix_existsUnique colourBasis
  colour_phase_decomposition := SourceColourPhase.colourFrame_exists_phase_specialUnitary
  colour_phase_ambiguity := SourceColourPhase.decomposition_ambiguity
  phase_classification := SourcePhaseFrames.unitary_existsUnique_phase
  pseudoreal_classification :=
    SourceReversalIsometry.pseudorealFrameChange_iff_specialUnitary
  effective_faithful := SourceGaugeUnitary.effectiveUnitaryRepresentation_injective

variable {ι X : Type*}

/-- Every selected frame acts on the same source matter Hilbert space. -/
def unitaryFrames (f : ι → X → EffectiveGroup) (i : ι) (x : X) : MatterUnitary :=
  effectiveUnitaryRepresentation (f i x)

/-- The relative transition sends frame-j components to frame-i components. -/
def relativeTransition (f : ι → X → EffectiveGroup) (i j : ι) (x : X) :
    EffectiveGroup :=
  (f i x)⁻¹ * f j x

@[simp] theorem relativeTransition_self (f : ι → X → EffectiveGroup)
    (i : ι) (x : X) : relativeTransition f i i x = 1 := by
  simp [relativeTransition]

theorem relativeTransition_inverse (f : ι → X → EffectiveGroup)
    (i j : ι) (x : X) :
    (relativeTransition f i j x)⁻¹ = relativeTransition f j i x := by
  simp [relativeTransition]

theorem relativeTransition_comp (f : ι → X → EffectiveGroup)
    (i j k : ι) (x : X) :
    relativeTransition f i j x * relativeTransition f j k x =
      relativeTransition f i k x := by
  simp [relativeTransition, mul_assoc]

/-- The overlap cocycle is a conclusion for every choice of chart domains. -/
theorem relativeTransition_cocycle (f : ι → X → EffectiveGroup) (U : ι → Set X) :
    CocycleOn U (relativeTransition f) := by
  intro i j k x _ _ _
  exact relativeTransition_comp f i j k x

theorem relativeTransition_representation (f : ι → X → EffectiveGroup)
    (i j : ι) (x : X) :
    effectiveUnitaryRepresentation (relativeTransition f i j x) =
      (unitaryFrames f i x)⁻¹ * unitaryFrames f j x := by
  simp only [relativeTransition, unitaryFrames, map_mul, map_inv]

/-- Applying the relative transition and then the old frame gives the new frame. -/
theorem relativeTransition_action (f : ι → X → EffectiveGroup)
    (i j : ι) (x : X) (v : FullMatter) :
    unitaryFrames f i x
        (effectiveUnitaryRepresentation (relativeTransition f i j x) v) =
      unitaryFrames f j x v := by
  rw [relativeTransition_representation]
  exact (unitaryFrames f i x).apply_symm_apply _

theorem relativeTransition_unitary_cocycle (f : ι → X → EffectiveGroup)
    (U : ι → Set X) :
    CocycleOn U (fun i j x =>
      effectiveUnitaryRepresentation (relativeTransition f i j x)) :=
  (SourceGaugeCocycle.effectiveCocycle_iff_unitaryCocycle U
    (relativeTransition f)).mp (relativeTransition_cocycle f U)

/-- Faithfulness gives uniqueness against every proposed effective transition. -/
theorem relativeTransition_unique (f : ι → X → EffectiveGroup)
    (i j : ι) (x : X) (q : EffectiveGroup)
    (hq : ∀ v : FullMatter,
      unitaryFrames f i x (effectiveUnitaryRepresentation q v) =
        unitaryFrames f j x v) :
    q = relativeTransition f i j x := by
  apply SourceGaugeUnitary.effectiveUnitaryRepresentation_injective
  apply LinearIsometryEquiv.ext
  intro v
  apply (unitaryFrames f i x).injective
  exact (hq v).trans (relativeTransition_action f i j x v).symm

/-- Coordinates of a source matter vector in the selected local frame. -/
def components (f : ι → X → EffectiveGroup) (i : ι) (x : X) (v : FullMatter) :
    FullMatter :=
  (unitaryFrames f i x).symm v

theorem relativeTransition_components (f : ι → X → EffectiveGroup)
    (i j : ι) (x : X) (v : FullMatter) :
    components f i x v =
      effectiveUnitaryRepresentation (relativeTransition f i j x)
        (components f j x v) := by
  apply (unitaryFrames f i x).injective
  rw [relativeTransition_action]
  simp only [components, LinearIsometryEquiv.apply_symm_apply]

/-- New components use the inverse of the transition acting on frames. -/
theorem relativeTransition_passive (f : ι → X → EffectiveGroup)
    (i j : ι) (x : X) (v : FullMatter) :
    components f j x v =
      (effectiveUnitaryRepresentation (relativeTransition f i j x)).symm
        (components f i x v) := by
  apply (effectiveUnitaryRepresentation (relativeTransition f i j x)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (relativeTransition_components f i j x v).symm

end GeneratedFoundations.Physical.SourceFrameConstruction
