module

public import GeneratedFoundations.Source.DimensionLowerBound
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Tactic.Ring

/-!
# A two-dimensional irreducible rotation action

Multiplication by the unit circle is a faithful real orthogonal action. Its
only invariant real subspaces are zero and the whole plane.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Source.RotationWitness

def rotation (z : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun w := (z : ℂ) * w
  invFun w := (z : ℂ)⁻¹ * w
  left_inv w := by simp
  right_inv w := by simp
  map_add' w u := mul_add _ _ _
  map_smul' r w := by simp [Complex.real_smul]; ring
  norm_map' w := by simp

@[simp] theorem rotation_apply (z : Circle) (w : ℂ) :
    rotation z w = (z : ℂ) * w := rfl

def action : Circle →* (ℂ ≃ₗᵢ[ℝ] ℂ) where
  toFun := rotation
  map_one' := by ext w; simp
  map_mul' z w := by ext u; simp [mul_assoc]

@[simp] theorem action_apply (z : Circle) (w : ℂ) : action z w = (z : ℂ) * w := rfl

theorem action_faithful : Function.Injective action := by
  intro z w h
  have hv := congrArg (fun f : ℂ ≃ₗᵢ[ℝ] ℂ => f 1) h
  apply Circle.coe_injective
  simpa using hv

theorem action_continuous (w : ℂ) : Continuous (fun z : Circle => action z w) :=
  continuous_subtype_val.mul_const w

def quarterTurn : Circle := ⟨Complex.I, by
  change Complex.I ∈ Metric.sphere (0 : ℂ) 1
  simp⟩

@[simp] theorem quarterTurn_coe : (quarterTurn : ℂ) = Complex.I := rfl

theorem real_irreducible (P : Submodule ℝ ℂ)
    (hinvariant : ∀ z : Circle, ∀ v ∈ P, action z v ∈ P) : P = ⊥ ∨ P = ⊤ := by
  by_cases hP : P = ⊥
  · exact Or.inl hP
  right
  obtain ⟨v, hv, hv0⟩ := P.ne_bot_iff.mp hP
  have hiv : Complex.I * v ∈ P := by simpa using hinvariant quarterTurn v hv
  apply top_unique
  intro w _
  have hw : w = (w / v).re • v + (w / v).im • (Complex.I * v) := by
    rw [Complex.real_smul, Complex.real_smul]
    calc
      w = (w / v) * v := (div_mul_cancel₀ w hv0).symm
      _ = ((w / v).re : ℂ) * v + ((w / v).im : ℂ) * (Complex.I * v) := by
        conv_lhs => rw [← Complex.re_add_im (w / v)]
        ring
  rw [hw]
  exact P.add_mem (P.smul_mem _ hv) (P.smul_mem _ hiv)

theorem carrier_dimension : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

end GeneratedFoundations.Source.RotationWitness
