module

public import GeneratedFoundations.Source.GeneratedSpectralCircle
public import GeneratedFoundations.Source.LocalSmoothInverse
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Smoothness of the generated carrier comparison

The phase character and its inverse are smooth in the original source
atlas and the standard sphere atlas of the unit complex circle. Injectivity
of the original differential propagates by left translation; the already
proved source dimension then gives invertibility. The original integral
curve is consequently smooth, without changing its defining differential
equation or transporting a new atlas to the source group.
-/

@[expose] public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace GeneratedFoundations.Source.GeneratedCarrierSmooth

open MinimalCarrier CharacterDifferential GeneratedSpectralCircle CarrierOrientation

attribute [local instance] finrank_real_complex_fact'

variable (d : OrthogonalChangeDatum) (h : IsMinimal d)

theorem character_contMDiff (χ : d.Changes →* Circle) (hχ : Continuous χ) :
    ContMDiff (𝓡 d.groupDimension) (𝓡 1) ∞ χ := by
  borelize d.Changes
  have hc := SmoothCharacter.contMDiff_coe_character
    (E := EuclideanSpace ℝ (Fin d.groupDimension)) χ hχ
  exact hc.codRestrict_sphere (fun g => (χ g).property)

theorem invariantField_surjective (g : d.Changes) :
    Surjective (fun X : GroupLieAlgebra (𝓡 d.groupDimension) d.Changes =>
      mulInvariantVectorField (I := 𝓡 d.groupDimension) X g) := by
  let : IsTopologicalGroup d.Changes := topologicalGroup_of_lieGroup (𝓡 d.groupDimension) ∞
  let e := (Homeomorph.mulLeft g).toOpenPartialHomeomorph
  have he : e.MDifferentiable (𝓡 d.groupDimension) (𝓡 d.groupDimension) := by
    constructor
    · intro x _
      exact (contMDiff_mul_left (I := 𝓡 d.groupDimension) (n := ∞)).contMDiffAt
        |>.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
    · intro x _
      exact (contMDiff_mul_left (a := g⁻¹) (I := 𝓡 d.groupDimension) (n := ∞)).contMDiffAt
        |>.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
  exact he.mfderiv_surjective (x := (1 : d.Changes)) (by trivial)

theorem character_complex_mfderiv_injective (χ : d.Changes →* Circle)
    (hχ : Continuous χ) (hfaithful : Injective χ) (g : d.Changes) :
    Injective (mfderiv (𝓡 d.groupDimension) 𝓘(ℝ, ℂ) (fun x => (χ x : ℂ)) g) := by
  intro v w hvw
  obtain ⟨X, hX⟩ := invariantField_surjective d g v
  obtain ⟨Y, hY⟩ := invariantField_surjective d g w
  rw [← hX, ← hY, mfderiv_mulInvariant χ hχ, mfderiv_mulInvariant χ hχ] at hvw
  have hXY := differential_injective χ hχ hfaithful
    (mul_left_cancel₀ (χ g).coe_ne_zero hvw)
  rw [hXY] at hX
  exact hX.symm.trans hY

theorem character_mfderiv_injective (χ : d.Changes →* Circle)
    (hχ : Continuous χ) (hfaithful : Injective χ) (g : d.Changes) :
    Injective (mfderiv (𝓡 d.groupDimension) (𝓡 1) χ g) := by
  intro v w hvw
  apply character_complex_mfderiv_injective d χ hχ hfaithful g
  have hs := (character_contMDiff d χ hχ g).mdifferentiableAt (by simp)
  have hi := (contMDiff_coe_sphere (m := ∞) (n := 1) (χ g)).mdifferentiableAt (by simp)
  have he := mfderiv_comp g hi hs
  change mfderiv (𝓡 d.groupDimension) 𝓘(ℝ, ℂ)
    (((↑) : Circle → ℂ) ∘ χ) g v =
      mfderiv (𝓡 d.groupDimension) 𝓘(ℝ, ℂ) (((↑) : Circle → ℂ) ∘ χ) g w
  have hv := DFunLike.congr_fun he v
  have hw := DFunLike.congr_fun he w
  refine hv.trans (Eq.trans ?_ hw.symm)
  simp only [ContinuousLinearMap.comp_apply]
  exact congrArg _ hvw

include h in
theorem character_mfderiv_bijective (χ : d.Changes →* Circle)
    (hχ : Continuous χ) (hfaithful : Injective χ) (g : d.Changes) :
    Bijective (mfderiv (𝓡 d.groupDimension) (𝓡 1) χ g) := by
  have hd : Module.finrank ℝ (TangentSpace (𝓡 d.groupDimension) g) =
      Module.finrank ℝ (TangentSpace (𝓡 1) (χ g)) := by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin d.groupDimension)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 1))
    simp only [finrank_euclideanSpace_fin, minimalCarrier_groupDimension_eq_one d h]
  exact (LinearEquiv.ofInjectiveOfFinrankEq
    (mfderiv (𝓡 d.groupDimension) (𝓡 1) χ g).toLinearMap
    (character_mfderiv_injective d χ hχ hfaithful g) hd).bijective

include h in
theorem character_inverse_contMDiff (χ : d.Changes ≃ₜ* Circle) :
    ContMDiff (𝓡 1) (𝓡 d.groupDimension) ∞ χ.symm :=
  LocalSmoothInverse.contMDiff_symm_of_bijective_mfderiv χ.toHomeomorph
    (character_contMDiff d χ.toMonoidHom χ.continuous)
    (character_mfderiv_bijective d h χ.toMonoidHom χ.continuous χ.injective)

theorem phaseCharacter_contMDiff (o : OrientationOnCarrier d) :
    ContMDiff (𝓡 d.groupDimension) (𝓡 1) ∞ (phaseCharacter d h o) :=
  character_contMDiff d (phaseCharacter d h o).toMonoidHom
    (phaseCharacter d h o).continuous

theorem phaseCharacter_inverse_contMDiff (o : OrientationOnCarrier d) :
    ContMDiff (𝓡 1) (𝓡 d.groupDimension) ∞ (phaseCharacter d h o).symm :=
  character_inverse_contMDiff d h (phaseCharacter d h o)

theorem orientedFlow_contMDiff (o : OrientationOnCarrier d) :
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 d.groupDimension) ∞ (orientedFlow d h o) := by
  have he : orientedFlow d h o = (phaseCharacter d h o).symm ∘ Circle.exp := by
    funext t
    apply (phaseCharacter d h o).injective
    simp only [phaseCharacter_flow, Function.comp_apply,
      ContinuousMulEquiv.apply_symm_apply]
  rw [he]
  exact (phaseCharacter_inverse_contMDiff d h o).comp contMDiff_circleExp

end GeneratedFoundations.Source.GeneratedCarrierSmooth
