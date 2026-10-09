module

public import GeneratedFoundations.Arithmetic.CircleCharacters
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Endomorphisms of the unit circle

The Fourier classification gives a classification of actual continuous circle
endomorphisms. The power index is unique; no quotient by homotopy is used.
-/

@[expose] public section

open scoped Topology

namespace GeneratedFoundations.Arithmetic.CircleEndomorphisms

open CircleCharacters

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

noncomputable def powerEndomorphism (n : ℤ) : Circle →ₜ* Circle where
  toFun z := z ^ n
  map_one' := one_zpow n
  map_mul' z w := mul_zpow z w n
  continuous_toFun := continuous_zpow n

@[simp] theorem powerEndomorphism_apply (n : ℤ) (z : Circle) :
    powerEndomorphism n z = z ^ n := rfl

noncomputable def additiveCharacter (u : Circle →ₜ* Circle) :
    C(AddCircle (1 : ℝ), ℂ) where
  toFun x := (u (AddCircle.toCircle x) : ℂ)
  continuous_toFun := continuous_subtype_val.comp
    (u.continuous.comp AddCircle.continuous_toCircle)

@[simp] theorem additiveCharacter_zero (u : Circle →ₜ* Circle) :
    additiveCharacter u 0 = 1 := by
  simp [additiveCharacter]

theorem additiveCharacter_add (u : Circle →ₜ* Circle)
    (x y : AddCircle (1 : ℝ)) :
    additiveCharacter u (x + y) = additiveCharacter u x * additiveCharacter u y := by
  simp [additiveCharacter, AddCircle.toCircle_add]

theorem additiveCharacter_power (n : ℤ) :
    additiveCharacter (powerEndomorphism n) = fourier n := by
  ext x
  simp [additiveCharacter, fourier_apply, AddCircle.toCircle_zsmul]

theorem additiveCharacter_injective : Function.Injective additiveCharacter := by
  intro u v h
  ext z
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective z
  rw [AddCircle.homeomorphCircle_apply] at hx
  have hval := congrArg (fun f : C(AddCircle (1 : ℝ), ℂ) => f x) h
  change (u (AddCircle.toCircle x) : ℂ) = (v (AddCircle.toCircle x) : ℂ) at hval
  rw [hx] at hval
  exact hval

theorem powerEndomorphism_injective : Function.Injective powerEndomorphism := by
  intro m n h
  apply fourier_index_injective
  simpa only [additiveCharacter_power] using congrArg additiveCharacter h

theorem circleEndomorphism_classification (u : Circle →ₜ* Circle) :
    ∃! n : ℤ, u = powerEndomorphism n := by
  obtain ⟨n, hn, _⟩ := character_existsUnique_fourier
    (additiveCharacter u) (additiveCharacter_zero u) (additiveCharacter_add u)
  have hu : u = powerEndomorphism n := additiveCharacter_injective
    (hn.trans (additiveCharacter_power n).symm)
  refine ⟨n, hu, ?_⟩
  intro m hm
  exact powerEndomorphism_injective (hm.symm.trans hu)

end GeneratedFoundations.Arithmetic.CircleEndomorphisms
