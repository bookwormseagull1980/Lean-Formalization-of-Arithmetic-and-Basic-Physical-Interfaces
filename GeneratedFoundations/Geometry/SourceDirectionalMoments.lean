module

public import GeneratedFoundations.Geometry.SourceDirectionalGenerator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Moments of the actual directional source generators

A fixed probability law on real source directions is used throughout.
Finite second moments imply the integrability of the linear generator and
every ordered quadratic term. Centering and isotropic covariance are applied
only after the full mixed-term expansion. The resulting scalar is the
Casimir of the same Haar representation.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal
open GeneratedFoundations.Geometry.SourceSymmetricUnitary
open GeneratedFoundations.Geometry.SourceDirectionalGenerator

namespace GeneratedFoundations.Geometry.SourceDirectionalMoments

local instance (m : ℕ) : CompleteSpace (HilbertCarrier m) :=
  FiniteDimensional.complete ℂ (HilbertCarrier m)

local instance (m : ℕ) : NormedAddCommGroup (End m) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance (m : ℕ) : NormedSpace ℂ (End m) :=
  ContinuousLinearMap.toNormedSpace

local instance (m : ℕ) : NormedSpace ℝ (End m) :=
  ContinuousLinearMap.toNormedSpace

private theorem integrable_complex_weight {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {ν : Measure Direction} {f : Direction → ℝ}
    (hf : Integrable f ν) (v : E) :
    Integrable (fun ξ => (f ξ : ℂ) • v) ν :=
  hf.ofReal.smul_const v

private theorem diagonal_covariance_sum {E : Type*} [AddCommGroup E] [Module ℂ E]
    (T : Fin 3 → Fin 3 → E) (c : ℝ) :
    (∑ a : Fin 3, ∑ b : Fin 3, ((if a = b then c else 0 : ℝ) : ℂ) • T a b) =
      (c : ℂ) • ∑ a : Fin 3, T a a := by
  simp [Finset.smul_sum]

variable (μ : Measure Direction) [IsProbabilityMeasure μ] (c : ℝ)

/-- These are conditions on one fixed law, independent of the step parameter. -/
structure CenteredIsotropic : Prop where
  positive_covariance : 0 < c
  finite_second_moment : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ
  mean_zero : ∀ a : Fin 3, ∫ ξ : Direction, ξ a ∂μ = 0
  covariance : ∀ a b : Fin 3,
    ∫ ξ : Direction, ξ a * ξ b ∂μ = if a = b then c else 0

variable {μ c} (h : CenteredIsotropic μ c)

include h

theorem coordinate_integrable (a : Fin 3) : Integrable (fun ξ : Direction => ξ a) μ :=
  (h.finite_second_moment a).integrable (by norm_num)

omit [IsProbabilityMeasure μ] in
theorem product_integrable (a b : Fin 3) :
    Integrable (fun ξ : Direction => ξ a * ξ b) μ :=
  (h.finite_second_moment a).integrable_mul (h.finite_second_moment b)

omit [IsProbabilityMeasure μ] in
theorem sizeSq_integrable : Integrable sizeSq μ := by
  apply integrable_finsetSum Finset.univ
  intro a ha
  exact (h.finite_second_moment a).integrable_sq

omit [IsProbabilityMeasure μ] in
theorem integral_sizeSq : ∫ ξ : Direction, sizeSq ξ ∂μ = 3 * c := by
  unfold sizeSq
  rw [integral_finsetSum Finset.univ (fun a _ => (h.finite_second_moment a).integrable_sq)]
  simp only [pow_two, h.covariance, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

theorem generator_integrable (m : ℕ) : Integrable (generator m) μ := by
  unfold generator
  apply integrable_finsetSum Finset.univ
  intro a ha
  exact integrable_complex_weight (E := End m) (coordinate_integrable h a) (axisCLM m a)

theorem integral_generator (m : ℕ) : ∫ ξ : Direction, generator m ξ ∂μ = 0 := by
  unfold generator
  rw [integral_finsetSum Finset.univ
    (fun a _ => integrable_complex_weight (E := End m)
      (coordinate_integrable h a) (axisCLM m a))]
  simp only [integral_smul_const, integral_complex_ofReal, h.mean_zero,
    Complex.ofReal_zero, zero_smul, Finset.sum_const_zero]

omit [IsProbabilityMeasure μ] in
theorem quadraticTerm_integrable (m : ℕ) (a b : Fin 3) :
    Integrable (fun ξ : Direction =>
      ((ξ a * ξ b : ℝ) : ℂ) • (axisCLM m a * axisCLM m b)) μ :=
  integrable_complex_weight (E := End m) (product_integrable h a b) _

omit [IsProbabilityMeasure μ] in
theorem generator_square_integrable (m : ℕ) :
    Integrable (fun ξ : Direction => generator m ξ * generator m ξ) μ := by
  simp_rw [generator_square]
  apply integrable_finsetSum Finset.univ
  intro a ha
  apply integrable_finsetSum Finset.univ
  intro b hb
  exact quadraticTerm_integrable h m a b

omit [IsProbabilityMeasure μ] in
/-- The ordered cross terms disappear by covariance, rather than by an
assumed commutativity or independent variation of the three axes. -/
theorem integral_generator_square_axes (m : ℕ) :
    (∫ ξ : Direction, generator m ξ * generator m ξ ∂μ) =
      (c : ℂ) • (∑ a : Fin 3, axisCLM m a * axisCLM m a) := by
  simp_rw [generator_square]
  rw [integral_finsetSum Finset.univ (fun a _ =>
    integrable_finsetSum Finset.univ (fun b _ => quadraticTerm_integrable h m a b))]
  calc
    _ = ∑ a : Fin 3, ∑ b : Fin 3,
        (∫ ξ : Direction, ((ξ a * ξ b : ℝ) : ℂ) ∂μ) •
          (axisCLM m a * axisCLM m b) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [integral_finsetSum Finset.univ (fun b _ => quadraticTerm_integrable h m a b)]
      simp only [integral_smul_const]
    _ = _ := by
      simp only [integral_complex_ofReal, h.covariance]
      exact diagonal_covariance_sum (E := End m) (fun a b => axisCLM m a * axisCLM m b) c

omit [IsProbabilityMeasure μ] in
theorem integral_generator_square (m : ℕ) :
    (∫ ξ : Direction, generator m ξ * generator m ξ ∂μ) =
      (-((c : ℂ) * (m : ℂ) * ((m : ℂ) + 2)) / 4) • (1 : End m) := by
  rw [integral_generator_square_axes h, axisCLM_square_sum, smul_smul]
  congr 1
  ring

omit [IsProbabilityMeasure μ] in
/-- The bound is integrable using exactly the second moments of this law. -/
theorem generator_norm_sq_integrable (m : ℕ) :
    Integrable (fun ξ : Direction => ‖generator m ξ‖ ^ 2) μ := by
  apply ((sizeSq_integrable h).const_mul (normSquareBound m)).mono'
    (((generator_continuous m).norm.pow 2).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun ξ => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_generator_sq_le m ξ)

omit [IsProbabilityMeasure μ] in
theorem integral_generator_norm_sq_le (m : ℕ) :
    (∫ ξ : Direction, ‖generator m ξ‖ ^ 2 ∂μ) ≤ normSquareBound m * (3 * c) := by
  calc
    _ ≤ ∫ ξ : Direction, normSquareBound m * sizeSq ξ ∂μ :=
      integral_mono (generator_norm_sq_integrable h m)
        ((sizeSq_integrable h).const_mul (normSquareBound m)) (norm_generator_sq_le m)
    _ = _ := by rw [integral_const_mul, integral_sizeSq h]

end GeneratedFoundations.Geometry.SourceDirectionalMoments
