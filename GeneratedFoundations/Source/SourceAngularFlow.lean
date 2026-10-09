module

public import GeneratedFoundations.Source.GeneratedSpectralCircle
public import GeneratedFoundations.Spectral.AngularFlow
public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The original source action and its full strong generator

The original change group acts by measure-preserving translation through its
previously constructed spectral coordinate. Positive pullback is used:
`f z` is sent to `f (z + coordinate g)`. Along the original oriented integral
curve this action agrees, on the whole Haar Hilbert space, with the Fourier
flow. Consequently its strong generator is `I` times the normalized angular
operator, with exactly the original periodic H1 domain.

The action is defined from actual translation, not from its Fourier values.
Fourier completeness proves the equality of the two bounded operators before
the strong-domain theorem is transferred.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter InnerProductSpace
open scoped Topology LinearPMap

namespace GeneratedFoundations.Source.SourceAngularFlow

open CarrierOrientation GeneratedSpectralCircle
open GeneratedFoundations.Spectral

variable (d : MinimalCarrier.OrthogonalChangeDatum) (h : MinimalCarrier.IsMinimal d)
variable (L : ℝ) [hL : Fact (0 < L)] (o : OrientationOnCarrier d)

/-- Translation by the coordinate of an actual original-group element. -/
def sourceTranslation (g : d.Changes) (z : AddCircle (2 * L)) : AddCircle (2 * L) :=
  z + spectralCoordinate d h L o g

theorem sourceTranslation_measurePreserving (g : d.Changes) :
    MeasurePreserving (sourceTranslation d h L o g)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  measurePreserving_add_right AddCircle.haarAddCircle (spectralCoordinate d h L o g)

theorem sourceTranslation_one : sourceTranslation d h L o 1 = id := by
  have hz : spectralCoordinate d h L o 1 = 0 :=
    congrArg Multiplicative.toAdd ((carrierCircle d h L o).map_one)
  funext z
  simp only [sourceTranslation, hz, add_zero, id_eq]

theorem sourceTranslation_mul (g k : d.Changes) :
    sourceTranslation d h L o (g * k) =
      sourceTranslation d h L o k ∘ sourceTranslation d h L o g := by
  funext z
  simp only [sourceTranslation, spectralCoordinate_mul, Function.comp_apply, add_assoc]

/-- The original action is actual pullback on probability-Haar L2. -/
def actualSourceAction (g : d.Changes) : HaarCircleL2 L →ₗᵢ[ℂ] HaarCircleL2 L :=
  Lp.compMeasurePreservingₗᵢ ℂ (sourceTranslation d h L o g)
    (sourceTranslation_measurePreserving d h L o g)

theorem actualSourceAction_coe (g : d.Changes) (f : HaarCircleL2 L) :
    actualSourceAction d h L o g f =ᵐ[AddCircle.haarAddCircle]
      fun z => f (z + spectralCoordinate d h L o g) :=
  Lp.coeFn_compMeasurePreserving f (sourceTranslation_measurePreserving d h L o g)

@[simp] theorem actualSourceAction_one (f : HaarCircleL2 L) :
    actualSourceAction d h L o 1 f = f := by
  change Lp.compMeasurePreserving (sourceTranslation d h L o 1) _ f = f
  simpa only [sourceTranslation_one] using Lp.compMeasurePreserving_id_apply f

theorem actualSourceAction_mul (g k : d.Changes) (f : HaarCircleL2 L) :
    actualSourceAction d h L o (g * k) f =
      actualSourceAction d h L o g (actualSourceAction d h L o k f) := by
  change Lp.compMeasurePreserving (sourceTranslation d h L o (g * k)) _ f =
    Lp.compMeasurePreserving (sourceTranslation d h L o g) _
      (Lp.compMeasurePreserving (sourceTranslation d h L o k) _ f)
  simpa only [sourceTranslation_mul] using
    Lp.compMeasurePreserving_comp_apply f
      (sourceTranslation_measurePreserving d h L o k)
      (sourceTranslation_measurePreserving d h L o g)

theorem actualSourceAction_norm (g : d.Changes) (f : HaarCircleL2 L) :
    ‖actualSourceAction d h L o g f‖ = ‖f‖ :=
  (actualSourceAction d h L o g).norm_map f

theorem actualSourceAction_inv (g : d.Changes) (f : HaarCircleL2 L) :
    actualSourceAction d h L o g⁻¹ (actualSourceAction d h L o g f) = f := by
  rw [← actualSourceAction_mul, inv_mul_cancel, actualSourceAction_one]

omit hL in
private theorem fourier_translation (n : ℤ) (z w : AddCircle (2 * L)) :
    fourier n (z + w) = fourier n z * fourier n w := by
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem actualSourceAction_fourier (g : d.Changes) (n : ℤ) :
    actualSourceAction d h L o g (fourierLp 2 n) =
      fourier n (spectralCoordinate d h L o g) • fourierLp 2 n := by
  apply Lp.ext
  have htranslate := (sourceTranslation_measurePreserving d h L o g).quasiMeasurePreserving.ae
    (coeFn_fourierLp (T := 2 * L) 2 n)
  filter_upwards [actualSourceAction_coe d h L o g (fourierLp 2 n), htranslate,
    coeFn_fourierLp (T := 2 * L) 2 n,
    Lp.coeFn_smul (fourier n (spectralCoordinate d h L o g))
      (fourierLp (T := 2 * L) 2 n)] with z hz ht hf hs
  change actualSourceAction d h L o g (fourierLp 2 n) z =
    (fourier n (spectralCoordinate d h L o g) • fourierLp 2 n) z
  change fourierLp 2 n (z + spectralCoordinate d h L o g) =
    fourier n (z + spectralCoordinate d h L o g) at ht
  rw [hz, ht, hs]
  simp only [Pi.smul_apply, smul_eq_mul, hf, fourier_translation, mul_comm]

theorem source_flow_phase (t : ℝ) (n : ℤ) :
    fourier n (spectralCoordinate d h L o (orientedFlow d h o t)) =
      AngularFlow.phase t n := by
  rw [spectral_fourier_flow, Circle.coe_exp, ← Complex.exp_int_mul]
  unfold AngularFlow.phase
  congr 1
  simp only [Complex.ofReal_mul, Complex.ofReal_intCast]
  ring

/-- The scaling is the one already forced by the original group phase. -/
theorem actualSourceAction_orientedFlow_coe (t : ℝ) (f : HaarCircleL2 L) :
    actualSourceAction d h L o (orientedFlow d h o t) f =ᵐ[AddCircle.haarAddCircle]
      fun z => f (z + ((L / Real.pi * t : ℝ) : AddCircle (2 * L))) := by
  simpa only [spectralCoordinate_flow] using
    actualSourceAction_coe d h L o (orientedFlow d h o t) f

/-- Agreement on every Fourier mode extends to every L2 vector by completeness. -/
theorem actualSourceAction_orientedFlow (t : ℝ) :
    (actualSourceAction d h L o (orientedFlow d h o t)).toContinuousLinearMap =
      AngularFlow.flow L t := by
  apply ContinuousLinearMap.ext
  intro f
  have hmode (n : ℤ) :
      (actualSourceAction d h L o (orientedFlow d h o t)).toContinuousLinearMap (fourierLp 2 n) =
        AngularFlow.flow L t (fourierLp 2 n) := by
    change actualSourceAction d h L o (orientedFlow d h o t) (fourierLp 2 n) = _
    rw [actualSourceAction_fourier, source_flow_phase, AngularFlow.flow_fourier]
  have ha := (actualSourceAction d h L o (orientedFlow d h o t)).toContinuousLinearMap.hasSum
    (AngularGenerator.eigenfunctions_complete L f)
  have hb := (AngularFlow.flow L t).hasSum (AngularGenerator.eigenfunctions_complete L f)
  apply ha.unique
  simpa only [map_smul, hmode] using hb

theorem originalFlow_stronglyContinuous (f : HaarCircleL2 L) :
    Continuous (fun t : ℝ => actualSourceAction d h L o (orientedFlow d h o t) f) := by
  have heq : (fun t : ℝ => actualSourceAction d h L o (orientedFlow d h o t) f) =
      fun t => AngularFlow.flow L t f := by
    funext t
    exact congrArg (fun T : HaarCircleL2 L →L[ℂ] HaarCircleL2 L => T f)
      (actualSourceAction_orientedFlow d h L o t)
  rw [heq]
  exact AngularFlow.flow_stronglyContinuous L f

/-- Continuity is on the original group's topology, by its actual quotient
covering flow; no new topology on the source is imposed. -/
theorem actualSourceAction_stronglyContinuous (f : HaarCircleL2 L) :
    Continuous (fun g : d.Changes => actualSourceAction d h L o g f) := by
  apply (orientedFlow_isQuotientCoveringMap d h o).toIsQuotientMap.continuous_iff.mpr
  exact originalFlow_stronglyContinuous d h L o f

/-- Strong differentiation is tested on the actual original-group action. -/
def HasSourceGenerator (f g : HaarCircleL2 L) : Prop :=
  Tendsto (fun t : ℝ => (t⁻¹ : ℂ) •
    (actualSourceAction d h L o (orientedFlow d h o t) f - f)) (𝓝[≠] 0) (𝓝 g)

theorem hasSourceGenerator_iff (f g : HaarCircleL2 L) :
    HasSourceGenerator d h L o f g ↔ AngularFlow.HasGenerator L f g := by
  unfold HasSourceGenerator AngularFlow.HasGenerator
  have heq : (fun t : ℝ => actualSourceAction d h L o (orientedFlow d h o t) f) =
      fun t => AngularFlow.flow L t f := by
    funext t
    exact congrArg (fun T : HaarCircleL2 L →L[ℂ] HaarCircleL2 L => T f)
      (actualSourceAction_orientedFlow d h L o t)
  simp only [funext_iff] at heq
  simp only [heq]

/-- Both directions use the original weak-Sobolev domain, not a prescribed
spectral domain. Positive pullback fixes the sign of the generator. -/
theorem sourceGenerator_iff (f g : HaarCircleL2 L) :
    HasSourceGenerator d h L o f g ↔
      ∃ hf : f ∈ (AngularGenerator.operator L).domain,
        g = Complex.I • AngularGenerator.operator L ⟨f, hf⟩ := by
  rw [hasSourceGenerator_iff, AngularFlow.generator_iff]

theorem sourceGenerator_domain_iff (f : HaarCircleL2 L) :
    (∃ g, HasSourceGenerator d h L o f g) ↔ f ∈ periodicH1Domain L := by
  change (∃ g, HasSourceGenerator d h L o f g) ↔
    f ∈ (AngularGenerator.operator L).domain
  simpa only [hasSourceGenerator_iff] using AngularFlow.generator_domain_iff L f

end GeneratedFoundations.Source.SourceAngularFlow
