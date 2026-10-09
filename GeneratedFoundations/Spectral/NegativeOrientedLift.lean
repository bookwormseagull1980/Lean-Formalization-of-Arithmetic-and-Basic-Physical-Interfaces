module

public import GeneratedFoundations.Spectral.AngularSquareDomain

/-!
# The analytic lift for the reversed angular orientation

The reflection of the original circle transports the nonnegative spectral
channel to the nonpositive channel by a surjective complex-linear isometry.
Composing this reflection with the Neumann lift gives the reversed lift,
including its constant mode, heat family, and full squared-operator domain.

Negative Fourier powers are scalar representatives in the original circle
coordinate. A nonnegative character in the reversed coordinate pulls back to
the same representative. No composition semiring on negative powers is used.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set InnerProductSpace
open scoped Topology NNReal LinearPMap
open GeneratedFoundations.Operations
open GeneratedFoundations.Arithmetic
open GeneratedFoundations.Spectral.AngularSpectralChannels

namespace GeneratedFoundations.Spectral.NegativeOrientedLift

variable (L : ℝ) [hL : Fact (0 < L)]

theorem reflection_negative_iff (f : HaarCircleL2 L) :
    haarCircleReflection L f ∈ negativeChannel L ↔ f ∈ positiveChannel L := by
  have h := (reflection_positive_iff L (haarCircleReflection L f)).symm
  simpa only [reflection_involution] using h

/-- This is coordinate reflection, complex-linear on the values. -/
def channelReflection : positiveChannel L ≃ₗᵢ[ℂ] negativeChannel L where
  toFun f := ⟨haarCircleReflection L f, (reflection_negative_iff L f).mpr f.property⟩
  invFun f := ⟨haarCircleReflection L f, (reflection_positive_iff L f).mpr f.property⟩
  left_inv f := by
    apply Subtype.ext
    exact reflection_involution L f
  right_inv f := by
    apply Subtype.ext
    exact reflection_involution L f
  map_add' f g := by
    apply Subtype.ext
    exact map_add (haarCircleReflection L) (f : HaarCircleL2 L) (g : HaarCircleL2 L)
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (haarCircleReflection L) c (f : HaarCircleL2 L)
  norm_map' f := (haarCircleReflection L).norm_map f

@[simp] theorem channelReflection_coe (f : positiveChannel L) :
    (channelReflection L f : HaarCircleL2 L) = haarCircleReflection L f := rfl

@[simp] theorem channelReflection_symm_coe (f : negativeChannel L) :
    ((channelReflection L).symm f : HaarCircleL2 L) = haarCircleReflection L f := rfl

def negativeMode (n : ℕ) : negativeChannel L :=
  ⟨fourierLp 2 (-(n : ℤ)), fourier_mem_spectralSubspace L (Iic 0) (by
    simp only [mem_Iic, Int.cast_neg, Int.cast_natCast]
    exact neg_nonpos.mpr (Nat.cast_nonneg n))⟩

@[simp] theorem negativeMode_coe (n : ℕ) :
    (negativeMode L n : HaarCircleL2 L) = fourierLp 2 (-(n : ℤ)) := rfl

theorem channelReflection_positiveMode (n : ℕ) :
    channelReflection L (OrientedLift.positiveMode L n) = negativeMode L n := by
  apply Subtype.ext
  exact haarCircleReflection_fourier L (n : ℤ)

/-- The reversed lift is onto the full nonpositive channel. -/
def unitary : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] negativeChannel L :=
  (OrientedLift.unitary L).trans (channelReflection L)

theorem unitary_cosine (n : ℕ) :
    unitary L (neumannCosineMode L n) = negativeMode L n := by
  change channelReflection L (OrientedLift.unitary L (neumannCosineMode L n)) = _
  rw [OrientedLift.unitary_cosine, channelReflection_positiveMode]

theorem unitary_coefficient (f : ComplexIntervalL2 0 L) (n : ℕ) :
    inner ℂ (negativeMode L n) (unitary L f) =
      inner ℂ (neumannCosineMode L n) f := by
  rw [← unitary_cosine L n]
  exact (unitary L).inner_map_map _ _

def lift : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L :=
  (negativeChannel L).subtypeL.comp
    (unitary L).toContinuousLinearEquiv.toContinuousLinearMap

theorem lift_apply (f : ComplexIntervalL2 0 L) :
    lift L f = (unitary L f : HaarCircleL2 L) := rfl

theorem lift_reflection (f : ComplexIntervalL2 0 L) :
    lift L f = haarCircleReflection L (OrientedLift.lift L f) := rfl

theorem lift_cosine (n : ℕ) :
    lift L (neumannCosineMode L n) = fourierLp 2 (-(n : ℤ)) := by
  rw [lift_apply, unitary_cosine]
  rfl

theorem lift_constant_mode :
    lift L (neumannCosineMode L 0) = OrientedLift.lift L (neumannCosineMode L 0) := by
  simp only [lift_cosine, OrientedLift.lift_cosine, Nat.cast_zero, neg_zero]

theorem lift_norm (f : ComplexIntervalL2 0 L) : ‖lift L f‖ = ‖f‖ :=
  (unitary L).norm_map f

theorem lift_range : (lift L).range = negativeChannel L := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact (unitary L g).property
  · intro hf
    refine ⟨(unitary L).symm ⟨f, hf⟩, ?_⟩
    exact congrArg Subtype.val ((unitary L).apply_symm_apply ⟨f, hf⟩)

theorem lift_unique (F : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L)
    (hF : ∀ n : ℕ, F (neumannCosineMode L n) = fourierLp 2 (-(n : ℤ))) :
    F = lift L := by
  apply ContinuousLinearMap.ext
  intro f
  have h₁ := F.hasSum (neumannCosineBasis_hasSum L f)
  have h₂ := (lift L).hasSum (neumannCosineBasis_hasSum L f)
  simp only [map_smul, hF, lift_cosine] at h₁ h₂
  exact h₁.unique h₂

theorem unitary_existsUnique :
    ∃! U : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] negativeChannel L,
      ∀ n : ℕ, U (neumannCosineMode L n) = negativeMode L n := by
  refine ⟨unitary L, unitary_cosine L, ?_⟩
  intro U hU
  have h := lift_unique L ((negativeChannel L).subtypeL.comp
      U.toContinuousLinearEquiv.toContinuousLinearMap) (by
    intro n
    change (U (neumannCosineMode L n) : HaarCircleL2 L) = fourierLp 2 (-(n : ℤ))
    rw [hU]
    rfl)
  apply DFunLike.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun F : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L => F f) h

theorem lift_cosine_coe (n : ℕ) :
    lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
      fourier (T := 2 * L) (-(n : ℤ)) := by
  rw [lift_cosine]
  exact coeFn_fourierLp 2 (-(n : ℤ))

theorem continuousRepresentative_unique (n : ℕ) (g : C(AddCircle (2 * L), ℂ))
    (hg : lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle] g) :
    g = fourier (-(n : ℤ)) := by
  apply ContinuousMap.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq (hg.symm.trans (lift_cosine_coe L n))
    g.continuous (fourier (-(n : ℤ))).continuous

theorem continuousRepresentative_existsUnique (n : ℕ) :
    ∃! g : C(AddCircle (2 * L), ℂ),
      lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle] g :=
  ⟨fourier (-(n : ℤ)), lift_cosine_coe L n, continuousRepresentative_unique L n⟩

/-- A character is evaluated in the reversed normalized circle coordinate. -/
def reversedRepresentative (u : Circle →ₜ* Circle) : C(AddCircle (2 * L), ℂ) where
  toFun z := (u (AddCircle.toCircle (-z)) : ℂ)
  continuous_toFun := continuous_subtype_val.comp
    (u.continuous.comp (AddCircle.continuous_toCircle.comp continuous_neg))

omit hL in
theorem reversedRepresentative_power (n : ℕ) :
    reversedRepresentative L (CircleEndomorphisms.powerEndomorphism (n : ℤ)) =
      fourier (-(n : ℤ)) := by
  ext z
  calc
    _ = fourier (n : ℤ) (-z) :=
      congrArg (fun g : C(AddCircle (2 * L), ℂ) => g (-z))
        (OrientedLift.endomorphismRepresentative_power L (n : ℤ))
    _ = _ := by simp only [fourier_apply, smul_neg, neg_smul]

theorem lift_cosine_reversed_native (n : ℕ) :
    lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
      reversedRepresentative L (NativeModes.powerMode n).val := by
  change lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
    reversedRepresentative L (CircleEndomorphisms.powerEndomorphism (n : ℤ))
  rw [reversedRepresentative_power]
  exact lift_cosine_coe L n

/-- Reflection transports the already constructed heat multipliers to the other channel. -/
def heat (t : ℝ≥0) : negativeChannel L →L[ℂ] negativeChannel L :=
  (channelReflection L).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((OrientedLift.positiveHeat L t).comp
      (channelReflection L).symm.toContinuousLinearEquiv.toContinuousLinearMap)

theorem heat_channelReflection (t : ℝ≥0) (f : positiveChannel L) :
    heat L t (channelReflection L f) =
      channelReflection L (OrientedLift.positiveHeat L t f) := by
  change channelReflection L
    (OrientedLift.positiveHeat L t ((channelReflection L).symm (channelReflection L f))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem heat_reflection (t : ℝ≥0) (f : positiveChannel L) :
    (heat L t (channelReflection L f) : HaarCircleL2 L) =
      haarCircleReflection L (OrientedLift.positiveHeat L t f : HaarCircleL2 L) := by
  rw [heat_channelReflection]
  rfl

theorem unitary_heat (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    unitary L (NeumannHeatSemigroup.heat L t f) = heat L t (unitary L f) := by
  change channelReflection L (OrientedLift.unitary L (NeumannHeatSemigroup.heat L t f)) =
    heat L t (channelReflection L (OrientedLift.unitary L f))
  rw [OrientedLift.unitary_heat, heat_channelReflection]

theorem lift_heat (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    lift L (NeumannHeatSemigroup.heat L t f) =
      (heat L t (unitary L f) : HaarCircleL2 L) :=
  congrArg Subtype.val (unitary_heat L t f)

theorem heat_mode (t : ℝ≥0) (n : ℕ) :
    heat L t (negativeMode L n) =
      (NeumannHeatSemigroup.decay L t n : ℂ) • negativeMode L n := by
  rw [← unitary_cosine, ← unitary_heat, NeumannHeatSemigroup.heat_cosine, map_smul,
    unitary_cosine]

theorem heat_coefficient (t : ℝ≥0) (f : negativeChannel L) (n : ℕ) :
    inner ℂ (negativeMode L n) (heat L t f) =
      (NeumannHeatSemigroup.decay L t n : ℂ) * inner ℂ (negativeMode L n) f := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, unitary_coefficient, unitary_coefficient]
  exact NeumannHeatSemigroup.heat_coefficient L t g n

theorem heat_zero (f : negativeChannel L) : heat L 0 f = f := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, NeumannHeatSemigroup.heat_zero]

theorem heat_add (s t : ℝ≥0) (f : negativeChannel L) :
    heat L (s + t) f = heat L s (heat L t f) := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, ← unitary_heat, ← unitary_heat, NeumannHeatSemigroup.heat_add]

theorem heat_norm_le (t : ℝ≥0) (f : negativeChannel L) : ‖heat L t f‖ ≤ ‖f‖ := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, (unitary L).norm_map, (unitary L).norm_map]
  exact NeumannHeatSemigroup.heat_norm_le L t g

/-- The equivalence concerns the complete original domains. -/
theorem lift_mem_square_domain_iff (f : ComplexIntervalL2 0 L) :
    lift L f ∈ (AngularSquareDomain.square L).domain ↔
      f ∈ (complexNeumannOperator hL.out).domain := by
  rw [lift_reflection, AngularSquareDomain.reflection_mem_square_domain_iff,
    AngularSquareDomain.lift_mem_square_domain_iff]

def negativeSquareDomain : Submodule ℂ (negativeChannel L) :=
  (AngularSquareDomain.square L).domain.comap (negativeChannel L).subtype

theorem unitary_mem_negativeSquareDomain_iff (f : ComplexIntervalL2 0 L) :
    unitary L f ∈ negativeSquareDomain L ↔
      f ∈ (complexNeumannOperator hL.out).domain :=
  lift_mem_square_domain_iff L f

def domainEquiv :
    (complexNeumannOperator hL.out).domain ≃ₗ[ℂ] negativeSquareDomain L where
  toFun f := ⟨unitary L f, (unitary_mem_negativeSquareDomain_iff L f).mpr f.property⟩
  invFun f := ⟨(unitary L).symm (f : negativeChannel L),
    (unitary_mem_negativeSquareDomain_iff L _).mp (by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using f.property)⟩
  left_inv f := by
    apply Subtype.ext
    exact (unitary L).symm_apply_apply f
  right_inv f := by
    apply Subtype.ext
    exact (unitary L).apply_symm_apply f
  map_add' f g := by
    apply Subtype.ext
    exact map_add (unitary L) (f : ComplexIntervalL2 0 L) (g : ComplexIntervalL2 0 L)
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (unitary L) c (f : ComplexIntervalL2 0 L)

def liftedDomainVector (f : (complexNeumannOperator hL.out).domain) :
    (AngularSquareDomain.square L).domain :=
  ⟨lift L f, (lift_mem_square_domain_iff L f).mpr f.property⟩

theorem liftedDomainVector_reflection (f : (complexNeumannOperator hL.out).domain) :
    liftedDomainVector L f =
      AngularSquareDomain.reflectionDomain L (AngularSquareDomain.liftedDomainVector L f) := by
  apply Subtype.ext
  exact lift_reflection L f

theorem operator_intertwining (f : (complexNeumannOperator hL.out).domain) :
    AngularSquareDomain.square L (liftedDomainVector L f) =
      lift L ((NeumannScaleTransport.energyUnit L : ℂ)⁻¹ •
        complexNeumannOperator hL.out f) := by
  rw [liftedDomainVector_reflection, AngularSquareDomain.reflection_square,
    AngularSquareDomain.operator_intertwining, ← lift_reflection]

end GeneratedFoundations.Spectral.NegativeOrientedLift
