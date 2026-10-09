module

public import GeneratedFoundations.Geometry.SourceCoefficientDifferentiation
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Bounded generators of arbitrary source directions

The operators act on the existing Haar Hilbert carriers. Their skew-adjoint
property follows by differentiating the actual unitary source orbits.
Arbitrary real directions retain all mixed terms in their squared generator.
The quadratic norm estimate uses only the Euclidean square of that direction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators ComplexConjugate
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourcePolynomialCasimir
open GeneratedFoundations.Geometry.SourceAxisDifferentiation
open GeneratedFoundations.Geometry.SourceCoefficientDifferentiation

namespace GeneratedFoundations.Geometry.SourceDirectionalGenerator

abbrev Direction := Fin 3 → ℝ
abbrev End (m : ℕ) := HilbertCarrier m →L[ℂ] HilbertCarrier m

local instance (m : ℕ) : CompleteSpace (HilbertCarrier m) :=
  FiniteDimensional.complete ℂ (HilbertCarrier m)

private theorem direction_sum_real {E : Type*} [AddCommGroup E]
    [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
    (T : Fin 3 → E) (ξ : Direction) :
    (∑ a : Fin 3, (ξ a : ℂ) • T a) = ∑ a : Fin 3, ξ a • T a := by
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

private theorem constant_inner_derivative {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {f g : ℝ → H} {v w v' w' : H}
    (hf : HasDerivAt f v' 0) (hg : HasDerivAt g w' 0)
    (hf0 : f 0 = v) (hg0 : g 0 = w)
    (hinner : ∀ t, inner ℂ (f t) (g t) = inner ℂ v w) :
    inner ℂ v' w + inner ℂ v w' = 0 := by
  have hd := hf.inner ℂ hg
  have heq : (fun t => inner ℂ (f t) (g t)) = fun _ => inner ℂ v w := funext hinner
  rw [heq] at hd
  have hz := hd.unique (hasDerivAt_const (0 : ℝ) (inner ℂ v w))
  simpa only [hf0, hg0, add_comm] using hz

private theorem star_of_inner_zero {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H)
    (hT : ∀ v w, inner ℂ (T v) w + inner ℂ v (T w) = 0) :
    star T = -T := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (T w) v = inner ℂ w (-(T v))
  rw [inner_neg_right]
  exact eq_neg_of_add_eq_zero_left (hT w v)

private theorem direction_sum_star {A : Type*} [Ring A] [StarRing A]
    [Algebra ℂ A] [StarModule ℂ A] (T : Fin 3 → A)
    (hT : ∀ a, star (T a) = -T a) (ξ : Direction) :
    star (∑ a : Fin 3, (ξ a : ℂ) • T a) = -(∑ a : Fin 3, (ξ a : ℂ) • T a) := by
  simp only [star_sum, star_smul, Complex.star_def, Complex.conj_ofReal, hT,
    smul_neg, Finset.sum_neg_distrib]

private theorem direction_sum_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : Fin 3 → E) :
    Continuous (fun ξ : Direction => ∑ a : Fin 3, (ξ a : ℂ) • T a) := by
  fun_prop

private theorem direction_sum_square {A : Type*} [Ring A] [Algebra ℂ A]
    (T : Fin 3 → A) (ξ : Direction) :
    (∑ a : Fin 3, (ξ a : ℂ) • T a) * (∑ a : Fin 3, (ξ a : ℂ) • T a) =
      ∑ a : Fin 3, ∑ b : Fin 3, ((ξ a * ξ b : ℝ) : ℂ) • (T a * T b) := by
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, Complex.ofReal_mul]
  exact Finset.sum_comm

private theorem direction_sum_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : Fin 3 → E) (ξ : Direction) :
    ‖∑ a : Fin 3, (ξ a : ℂ) • T a‖ ≤ ∑ a : Fin 3, |ξ a| * ‖T a‖ := by
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs] using
    norm_sum_le Finset.univ (fun a : Fin 3 => (ξ a : ℂ) • T a)

private theorem direction_sum_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (T : Fin 3 → E) (ξ : Direction) :
    ‖∑ a : Fin 3, (ξ a : ℂ) • T a‖ ^ 2 ≤
      (∑ a : Fin 3, ‖T a‖ ^ 2) * (∑ a : Fin 3, (ξ a) ^ 2) := by
  have hnonneg : 0 ≤ ∑ a : Fin 3, |ξ a| * ‖T a‖ :=
    Finset.sum_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
  calc
    _ ≤ (∑ a : Fin 3, |ξ a| * ‖T a‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) hnonneg).mpr (direction_sum_norm_le T ξ)
    _ ≤ (∑ a : Fin 3, |ξ a| ^ 2) * ∑ a : Fin 3, ‖T a‖ ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
    _ = _ := by simp only [sq_abs, mul_comm]

/-- Continuity is inherited from the same finite-dimensional source carrier. -/
def axisCLM (m : ℕ) (a : Fin 3) : End m :=
  LinearMap.toContinuousLinearMap (hilbertAxis m a)

@[simp] theorem axisCLM_apply (m : ℕ) (a : Fin 3) (v : HilbertCarrier m) :
    axisCLM m a v = hilbertAxis m a v := rfl

def generator (m : ℕ) (ξ : Direction) : End m :=
  ∑ a : Fin 3, (ξ a : ℂ) • axisCLM m a

theorem generator_apply (m : ℕ) (ξ : Direction) (v : HilbertCarrier m) :
    generator m ξ v = ∑ a : Fin 3, (ξ a : ℂ) • hilbertAxis m a v := by
  simp only [generator, sum_apply, _root_.smul_apply, axisCLM_apply]

theorem generator_real (m : ℕ) (ξ : Direction) :
    generator m ξ = ∑ a : Fin 3, ξ a • axisCLM m a :=
  direction_sum_real (E := End m) (axisCLM m) ξ

theorem axis_inner_derivative (m : ℕ) (a : Fin 3) (v w : HilbertCarrier m) :
    inner ℂ (axisCLM m a v) w + inner ℂ v (axisCLM m a w) = 0 := by
  have hv : HasDerivAt (fun t : ℝ => unitaryAction m (sourceAxis a t) v)
      (axisCLM m a v) 0 := by
    simpa only [sourceAxis_zero, unitaryAction_one_apply, axisCLM_apply] using!
      sourceAxis_hasDerivAt m a v 0
  have hw : HasDerivAt (fun t : ℝ => unitaryAction m (sourceAxis a t) w)
      (axisCLM m a w) 0 := by
    simpa only [sourceAxis_zero, unitaryAction_one_apply, axisCLM_apply] using!
      sourceAxis_hasDerivAt m a w 0
  exact constant_inner_derivative (H := HilbertCarrier m) hv hw
    (by rw [sourceAxis_zero, unitaryAction_one_apply])
    (by rw [sourceAxis_zero, unitaryAction_one_apply])
    (fun t => (unitaryAction m (sourceAxis a t)).inner_map_map v w)

/-- The adjoint relation is derived from the actual source action. -/
theorem axisCLM_star (m : ℕ) (a : Fin 3) : star (axisCLM m a) = -axisCLM m a :=
  star_of_inner_zero (axisCLM m a) (axis_inner_derivative m a)

theorem generator_star (m : ℕ) (ξ : Direction) :
    star (generator m ξ) = -generator m ξ :=
  direction_sum_star (A := End m) (axisCLM m) (axisCLM_star m) ξ

theorem generator_continuous (m : ℕ) : Continuous (generator m) :=
  direction_sum_continuous (E := End m) (axisCLM m)

/-- The products keep their source order; no commutativity of the axes is used. -/
theorem generator_square (m : ℕ) (ξ : Direction) :
    generator m ξ * generator m ξ =
      ∑ a : Fin 3, ∑ b : Fin 3,
        ((ξ a * ξ b : ℝ) : ℂ) • (axisCLM m a * axisCLM m b) :=
  direction_sum_square (A := End m) (axisCLM m) ξ

theorem axisCLM_casimir (m : ℕ) :
    (-4 : ℂ) • (∑ a : Fin 3, axisCLM m a * axisCLM m a) =
      ((m : ℂ) * ((m : ℂ) + 2)) • (1 : End m) := by
  apply ContinuousLinearMap.ext
  intro v
  simpa only [_root_.smul_apply, sum_apply, mul_apply_eq_comp,
    one_apply_eq_self, axisCLM_apply] using hilbertAxis_casimir_apply m v

theorem axisCLM_square_sum (m : ℕ) :
    (∑ a : Fin 3, axisCLM m a * axisCLM m a) =
      (-((m : ℂ) * ((m : ℂ) + 2)) / 4) • (1 : End m) := by
  have h := congrArg (fun T : End m => (-1 / 4 : ℂ) • T) (axisCLM_casimir m)
  simpa only [smul_smul, show (-1 / 4 : ℂ) * (-4) = 1 by norm_num, one_smul,
    show (-1 / 4 : ℂ) * ((m : ℂ) * ((m : ℂ) + 2)) =
      -((m : ℂ) * ((m : ℂ) + 2)) / 4 by ring] using h

def sizeSq (ξ : Direction) : ℝ := ∑ a : Fin 3, (ξ a) ^ 2

theorem sizeSq_nonneg (ξ : Direction) : 0 ≤ sizeSq ξ :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- A fixed representation-dependent constant, independent of the sampled direction. -/
def normSquareBound (m : ℕ) : ℝ := ∑ a : Fin 3, ‖axisCLM m a‖ ^ 2

theorem normSquareBound_nonneg (m : ℕ) : 0 ≤ normSquareBound m :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem norm_generator_le (m : ℕ) (ξ : Direction) :
    ‖generator m ξ‖ ≤ ∑ a : Fin 3, |ξ a| * ‖axisCLM m a‖ :=
  direction_sum_norm_le (E := End m) (axisCLM m) ξ

/-- This is the bound needed for a finite-second-moment source law. -/
theorem norm_generator_sq_le (m : ℕ) (ξ : Direction) :
    ‖generator m ξ‖ ^ 2 ≤ normSquareBound m * sizeSq ξ :=
  direction_sum_norm_sq_le (E := End m) (axisCLM m) ξ

end GeneratedFoundations.Geometry.SourceDirectionalGenerator
