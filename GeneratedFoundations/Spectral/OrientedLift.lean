module

public import GeneratedFoundations.Spectral.AngularSpectralChannels
public import GeneratedFoundations.Spectral.NeumannCanonicalModes
public import GeneratedFoundations.Spectral.NeumannHeatSemigroup
public import GeneratedFoundations.Arithmetic.NativeModes
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# The oriented analytic lift of the Neumann spectrum

The nonnegative spectral channel of the periodic angular derivative has a
complete orthonormal family indexed by its nonnegative eigenvalues. Its
basis correspondence with the canonical Neumann modes constructs a unitary
from the original interval space. The same map is identified with the
reflection followed by spectral selection, with separate normalizations
for the constant mode and the nonconstant pairs.

The lifted eigenvectors have unique continuous representatives. Under the
normalized circle coordinate these are precisely the nonnegative power
endomorphisms. The lift also transports the entire Neumann heat family to
the corresponding multipliers on the positive channel.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ComplexConjugate NNReal Classical
open GeneratedFoundations.Operations
open GeneratedFoundations.Arithmetic
open GeneratedFoundations.Spectral.AngularSpectralChannels

namespace GeneratedFoundations.Spectral.OrientedLift

variable (L : ℝ) [hL : Fact (0 < L)]

/-- A vector of the actual nonnegative angular spectral channel. -/
def positiveMode (n : ℕ) : positiveChannel L :=
  ⟨fourierLp 2 (n : ℤ), fourier_mem_spectralSubspace L (Ici 0)
    (by simpa only [mem_Ici, Int.cast_natCast] using (Nat.cast_nonneg n : (0 : ℝ) ≤ n))⟩

@[simp] theorem positiveMode_coe (n : ℕ) :
    (positiveMode L n : HaarCircleL2 L) = fourierLp 2 (n : ℤ) := rfl

theorem positiveMode_orthonormal : Orthonormal ℂ (positiveMode L) := by
  apply orthonormal_iff_ite.mpr
  intro m n
  change inner ℂ (fourierLp (T := 2 * L) 2 (m : ℤ)) (fourierLp 2 (n : ℤ)) = _
  simpa only [Int.natCast_inj] using haarFourier_inner L (m : ℤ) (n : ℤ)

theorem positiveMode_orthogonal_eq_bot :
    (Submodule.span ℂ (Set.range (positiveMode L)))ᗮ = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro f hf
  have hpos (n : ℕ) : inner ℂ (fourierLp (T := 2 * L) 2 (n : ℤ))
      (f : HaarCircleL2 L) = 0 :=
    (Submodule.mem_orthogonal _ _).mp hf _ (Submodule.subset_span ⟨n, rfl⟩)
  apply Subtype.ext
  apply EigenbasisClosure.eq_of_coefficients (fourierBasis (T := 2 * L))
  intro n
  simp only [coe_fourierBasis, Submodule.coe_zero, inner_zero_right]
  cases n with
  | ofNat n => exact hpos n
  | negSucc n =>
      exact (positiveChannel_mem_iff L (f : HaarCircleL2 L)).mp f.property
        (Int.negSucc n) (by omega)

/-- Completeness is proved inside the channel selected by the angular operator. -/
def positiveBasis : HilbertBasis ℕ ℂ (positiveChannel L) :=
  HilbertBasis.mkOfOrthogonalEqBot (positiveMode_orthonormal L)
    (positiveMode_orthogonal_eq_bot L)

theorem coe_positiveBasis : ⇑(positiveBasis L) = positiveMode L :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- The basis correspondence extends to an actual surjective linear isometry. -/
def unitary : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] positiveChannel L :=
  (neumannCosineBasis L).repr.trans (positiveBasis L).repr.symm

theorem unitary_cosine (n : ℕ) :
    unitary L (neumannCosineMode L n) = positiveMode L n := by
  change (positiveBasis L).repr.symm
    ((neumannCosineBasis L).repr (neumannCosineMode L n)) = positiveMode L n
  rw [← coe_neumannCosineBasis L, HilbertBasis.repr_self,
    HilbertBasis.repr_symm_single]
  exact congrFun (coe_positiveBasis L) n

theorem unitary_coefficient (f : ComplexIntervalL2 0 L) (n : ℕ) :
    inner ℂ (positiveMode L n) (unitary L f) =
      inner ℂ (neumannCosineMode L n) f := by
  rw [← unitary_cosine L n]
  exact (unitary L).inner_map_map _ _

/-- The same lift with its values in the full circle Hilbert space. -/
def lift : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L :=
  (positiveChannel L).subtypeL.comp
    (unitary L).toContinuousLinearEquiv.toContinuousLinearMap

theorem lift_apply (f : ComplexIntervalL2 0 L) :
    lift L f = (unitary L f : HaarCircleL2 L) := rfl

theorem lift_cosine (n : ℕ) :
    lift L (neumannCosineMode L n) = fourierLp 2 (n : ℤ) := by
  rw [lift_apply, unitary_cosine]
  rfl

theorem lift_norm (f : ComplexIntervalL2 0 L) : ‖lift L f‖ = ‖f‖ :=
  (unitary L).norm_map f

theorem lift_range : (lift L).range = positiveChannel L := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    exact (unitary L g).property
  · intro hf
    refine ⟨(unitary L).symm ⟨f, hf⟩, ?_⟩
    exact congrArg Subtype.val ((unitary L).apply_symm_apply ⟨f, hf⟩)

theorem lift_unique (F : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L)
    (hF : ∀ n : ℕ, F (neumannCosineMode L n) = fourierLp 2 (n : ℤ)) :
    F = lift L := by
  apply ContinuousLinearMap.ext
  intro f
  have h₁ := F.hasSum (neumannCosineBasis_hasSum L f)
  have h₂ := (lift L).hasSum (neumannCosineBasis_hasSum L f)
  simp only [map_smul, hF, lift_cosine] at h₁ h₂
  exact h₁.unique h₂

theorem unitary_existsUnique :
    ∃! U : ComplexIntervalL2 0 L ≃ₗᵢ[ℂ] positiveChannel L,
      ∀ n : ℕ, U (neumannCosineMode L n) = positiveMode L n := by
  refine ⟨unitary L, unitary_cosine L, ?_⟩
  intro U hU
  have h := lift_unique L ((positiveChannel L).subtypeL.comp
      U.toContinuousLinearEquiv.toContinuousLinearMap) (by
    intro n
    change (U (neumannCosineMode L n) : HaarCircleL2 L) = fourierLp 2 (n : ℤ)
    rw [hU]
    rfl)
  apply DFunLike.ext
  intro f
  apply Subtype.ext
  exact congrArg (fun F : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L => F f) h

/-- The zero mode is retained; a strict positive component of an even pair is rescaled. -/
def spectralFormula : ComplexIntervalL2 0 L →L[ℂ] HaarCircleL2 L :=
  (spectralProjection L {0} +
    (Real.sqrt 2 : ℂ) • spectralProjection L (Ioi 0)).comp
      (reflectingHaarIsometry L).toContinuousLinearMap

theorem spectralFormula_apply (f : ComplexIntervalL2 0 L) :
    spectralFormula L f = spectralProjection L {0} (reflectingHaarIsometry L f) +
      (Real.sqrt 2 : ℂ) •
        spectralProjection L (Ioi 0) (reflectingHaarIsometry L f) := rfl

theorem spectralFormula_cosine (n : ℕ) :
    spectralFormula L (neumannCosineMode L n) = fourierLp 2 (n : ℤ) := by
  rw [spectralFormula_apply, reflectingHaar_neumannCosineMode]
  cases n with
  | zero =>
      simp only [Nat.cast_zero, haarCosineMode, spectralProjection_fourier, Int.cast_zero,
        mem_singleton_iff, mem_Ioi, lt_self_iff_false, ite_true, ite_false,
        smul_zero, add_zero]
  | succ n =>
      have hp : (0 : ℝ) < ((n + 1 : ℕ) : ℤ) := by positivity
      have hm : (0 : ℝ) > (-(n + 1 : ℕ) : ℤ) := by
        simpa only [Int.cast_neg] using neg_neg_of_pos hp
      have h₀p : spectralProjection L {0} (fourierLp 2 ((n + 1 : ℕ) : ℤ)) = 0 := by
        rw [spectralProjection_fourier, ite_eq_right]
        exact ne_of_gt hp
      have h₀m : spectralProjection L {0} (fourierLp 2 (-(n + 1 : ℕ) : ℤ)) = 0 := by
        rw [spectralProjection_fourier, ite_eq_right]
        exact ne_of_lt hm
      have hpp : spectralProjection L (Ioi 0) (fourierLp 2 ((n + 1 : ℕ) : ℤ)) =
          fourierLp 2 ((n + 1 : ℕ) : ℤ) := by
        rw [spectralProjection_fourier, mem_Ioi, ite_eq_left hp]
      have hpm : spectralProjection L (Ioi 0) (fourierLp 2 (-(n + 1 : ℕ) : ℤ)) = 0 := by
        rw [spectralProjection_fourier, mem_Ioi, ite_eq_right (not_lt.mpr hm.le)]
      have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
      simp only [haarCosineMode, map_smul, map_add, h₀p, h₀m, hpp, hpm,
        add_zero, smul_zero, zero_add, smul_smul, mul_inv_cancel₀ hs, one_smul]

theorem spectralFormula_eq_lift : spectralFormula L = lift L :=
  lift_unique L (spectralFormula L) (spectralFormula_cosine L)

theorem lift_spectral_formula (f : ComplexIntervalL2 0 L) :
    lift L f = spectralProjection L {0} (reflectingHaarIsometry L f) +
      (Real.sqrt 2 : ℂ) •
        spectralProjection L (Ioi 0) (reflectingHaarIsometry L f) := by
  rw [← spectralFormula_eq_lift]
  exact spectralFormula_apply L f

theorem lift_cosine_coe (n : ℕ) :
    lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
      fourier (T := 2 * L) (n : ℤ) := by
  rw [lift_cosine]
  exact coeFn_fourierLp 2 (n : ℤ)

/-- Uniqueness follows from continuity and the full support of Haar measure. -/
theorem continuousRepresentative_unique (n : ℕ) (g : C(AddCircle (2 * L), ℂ))
    (hg : lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle] g) :
    g = fourier (n : ℤ) := by
  apply ContinuousMap.coe_injective
  exact MeasureTheory.Measure.eq_of_ae_eq (hg.symm.trans (lift_cosine_coe L n))
    g.continuous (fourier (n : ℤ)).continuous

theorem continuousRepresentative_existsUnique (n : ℕ) :
    ∃! g : C(AddCircle (2 * L), ℂ),
      lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle] g :=
  ⟨fourier (n : ℤ), lift_cosine_coe L n, continuousRepresentative_unique L n⟩

/-- Pull back a genuine circle endomorphism through the normalized circle coordinate. -/
def endomorphismRepresentative (u : Circle →ₜ* Circle) : C(AddCircle (2 * L), ℂ) where
  toFun z := (u (AddCircle.toCircle z) : ℂ)
  continuous_toFun := continuous_subtype_val.comp
    (u.continuous.comp AddCircle.continuous_toCircle)

omit hL in
theorem endomorphismRepresentative_power (n : ℤ) :
    endomorphismRepresentative L (CircleEndomorphisms.powerEndomorphism n) = fourier n := by
  ext z
  simp [endomorphismRepresentative, fourier_apply, AddCircle.toCircle_zsmul]

theorem endomorphismRepresentative_injective :
    Function.Injective (endomorphismRepresentative L) := by
  intro u v huv
  ext z
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle
    (T := 2 * L) (mul_ne_zero two_ne_zero hL.out.ne')).surjective z
  rw [AddCircle.homeomorphCircle_apply] at hx
  have h := congrArg (fun f : C(AddCircle (2 * L), ℂ) => f x) huv
  change (u (AddCircle.toCircle x) : ℂ) = (v (AddCircle.toCircle x) : ℂ) at h
  rw [hx] at h
  exact h

theorem liftedMode_endomorphism_iff (n : ℕ) (u : Circle →ₜ* Circle) :
    lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
      endomorphismRepresentative L u ↔
        u = CircleEndomorphisms.powerEndomorphism (n : ℤ) := by
  constructor
  · intro hu
    apply endomorphismRepresentative_injective L
    exact (continuousRepresentative_unique L n _ hu).trans
      (endomorphismRepresentative_power L (n : ℤ)).symm
  · rintro rfl
    rw [endomorphismRepresentative_power]
    exact lift_cosine_coe L n

theorem liftedMode_native_coe (n : ℕ) :
    lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
      fun z => (NativeModes.powerMode n (AddCircle.toCircle z) : ℂ) :=
  (liftedMode_endomorphism_iff L n (NativeModes.powerMode n).val).mpr rfl

theorem liftedEndomorphism_existsUnique (n : ℕ) :
    ∃! u : Circle →ₜ* Circle,
      lift L (neumannCosineMode L n) =ᵐ[AddCircle.haarAddCircle]
        endomorphismRepresentative L u :=
  ⟨CircleEndomorphisms.powerEndomorphism (n : ℤ),
    (liftedMode_endomorphism_iff L n _).mpr rfl,
    fun u hu => (liftedMode_endomorphism_iff L n u).mp hu⟩

/-- This source family is specified by the actual differential operator,
unit norm, and the positive endpoint trace, without a natural-number label. -/
def IsLiftedSourceMode (u : Circle →ₜ* Circle) : Prop :=
  ∃ f : (complexNeumannOperator hL.out).domain, ∃ z : ℂ,
    complexNeumannOperator hL.out f = z • (f : ComplexIntervalL2 0 L) ∧
      ‖(f : ComplexIntervalL2 0 L)‖ = 1 ∧
      (∃ r : ℝ, 0 < r ∧ neumannLeftTrace L f = (r : ℂ)) ∧
      lift L (f : ComplexIntervalL2 0 L) =ᵐ[AddCircle.haarAddCircle]
        endomorphismRepresentative L u

theorem isLiftedSourceMode_iff (u : Circle →ₜ* Circle) :
    IsLiftedSourceMode L u ↔
      ∃ n : ℕ, u = CircleEndomorphisms.powerEndomorphism (n : ℤ) := by
  constructor
  · rintro ⟨f, z, heig, hnorm, htrace, hrep⟩
    have hf : (f : ComplexIntervalL2 0 L) ≠ 0 := by
      intro hf
      rw [hf, norm_zero] at hnorm
      exact zero_ne_one hnorm
    obtain ⟨n, hn⟩ := (complexNeumann_eigenvalue_iff L z).mp ⟨f, hf, heig⟩
    rw [hn] at heig
    have hcanonical := neumannCanonicalMode_unique L n f heig hnorm htrace
    rw [hcanonical] at hrep
    exact ⟨n, (liftedMode_endomorphism_iff L n u).mp hrep⟩
  · rintro ⟨n, hn⟩
    refine ⟨neumannCosineDomainVector L n, (neumannEigenvalue L n : ℂ),
      complexNeumannOperator_cosine L n, (neumannCosineMode_orthonormal L).norm_eq_one n,
      ⟨neumannModeEndpoint L n, neumannModeEndpoint_pos L n, neumannLeftTrace_cosine L n⟩, ?_⟩
    exact (liftedMode_endomorphism_iff L n u).mpr hn

theorem nativeMode_has_source (u : NativeModes.Mode) : IsLiftedSourceMode L u.val :=
  (isLiftedSourceMode_iff L u.val).mpr u.property

theorem sourceMode_has_native_iff (u : Circle →ₜ* Circle) :
    IsLiftedSourceMode L u ↔ ∃ v : NativeModes.Mode, v.val = u := by
  constructor
  · intro hu
    exact ⟨⟨u, (isLiftedSourceMode_iff L u).mp hu⟩, rfl⟩
  · rintro ⟨v, rfl⟩
    exact nativeMode_has_source L v

def positiveCoefficients : positiveChannel L ≃ₗᵢ[ℂ] NeumannHeatSemigroup.Sequence :=
  (positiveBasis L).repr

theorem positiveCoefficients_apply (f : positiveChannel L) (n : ℕ) :
    positiveCoefficients L f n = inner ℂ (positiveMode L n) f := by
  simpa only [positiveCoefficients, coe_positiveBasis] using
    (positiveBasis L).repr_apply_apply f n

/-- Heat multipliers on the selected angular channel, defined independently of the lift. -/
def positiveHeat (t : ℝ≥0) : positiveChannel L →L[ℂ] positiveChannel L :=
  (positiveCoefficients L).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((NeumannHeatSemigroup.sequenceOperator L t).comp
      (positiveCoefficients L).toContinuousLinearEquiv.toContinuousLinearMap)

theorem positiveCoefficients_heat (t : ℝ≥0) (f : positiveChannel L) :
    positiveCoefficients L (positiveHeat L t f) =
      NeumannHeatSemigroup.sequenceOperator L t (positiveCoefficients L f) := by
  simp [positiveHeat]

theorem positiveHeat_coefficient (t : ℝ≥0) (f : positiveChannel L) (n : ℕ) :
    inner ℂ (positiveMode L n) (positiveHeat L t f) =
      (NeumannHeatSemigroup.decay L t n : ℂ) * inner ℂ (positiveMode L n) f := by
  simp only [← positiveCoefficients_apply, positiveCoefficients_heat]
  rfl

theorem unitary_heat (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    unitary L (NeumannHeatSemigroup.heat L t f) = positiveHeat L t (unitary L f) := by
  apply (positiveCoefficients L).injective
  apply lp.ext
  funext n
  simp only [positiveCoefficients_apply, positiveHeat_coefficient,
    unitary_coefficient, NeumannHeatSemigroup.heat_coefficient]

theorem lift_heat (t : ℝ≥0) (f : ComplexIntervalL2 0 L) :
    lift L (NeumannHeatSemigroup.heat L t f) =
      (positiveHeat L t (unitary L f) : HaarCircleL2 L) :=
  congrArg Subtype.val (unitary_heat L t f)

theorem positiveHeat_mode (t : ℝ≥0) (n : ℕ) :
    positiveHeat L t (positiveMode L n) =
      (NeumannHeatSemigroup.decay L t n : ℂ) • positiveMode L n := by
  rw [← unitary_cosine, ← unitary_heat, NeumannHeatSemigroup.heat_cosine, map_smul,
    unitary_cosine]

omit hL in
theorem decay_angular_square (t : ℝ) (n : ℕ) :
    NeumannHeatSemigroup.decay L t n =
      Real.exp (-t * neumannEigenvalue L 1 * (n : ℝ) ^ 2 / 2) := by
  unfold NeumannHeatSemigroup.decay neumannEigenvalue
  congr 1
  push_cast
  ring

theorem positiveHeat_zero (f : positiveChannel L) : positiveHeat L 0 f = f := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, NeumannHeatSemigroup.heat_zero]

theorem positiveHeat_add (s t : ℝ≥0) (f : positiveChannel L) :
    positiveHeat L (s + t) f = positiveHeat L s (positiveHeat L t f) := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, ← unitary_heat, ← unitary_heat, NeumannHeatSemigroup.heat_add]

theorem positiveHeat_norm_le (t : ℝ≥0) (f : positiveChannel L) :
    ‖positiveHeat L t f‖ ≤ ‖f‖ := by
  obtain ⟨g, rfl⟩ := (unitary L).surjective f
  rw [← unitary_heat, (unitary L).norm_map, (unitary L).norm_map]
  exact NeumannHeatSemigroup.heat_norm_le L t g

end GeneratedFoundations.Spectral.OrientedLift
