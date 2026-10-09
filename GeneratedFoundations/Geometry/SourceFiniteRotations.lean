module

public import GeneratedFoundations.Geometry.SourceDirectionalGenerator
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-!
# Finite rotations and isotropic second moments

The controls consist of four diagonal sign rotations, a quarter turn, and
three cyclic permutations. Their equal average annihilates first moments
and sends every bilinear response to its scalar trace part. The coordinate
formulas also preserve finite second moments of any direction law.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix
open GeneratedFoundations.Geometry.SourceDirectionalGenerator

namespace GeneratedFoundations.Geometry.SourceFiniteRotations

abbrev Control := Fin 3 × Fin 2 × Fin 4

@[simp] theorem card_control : Fintype.card Control = 24 := by
  norm_num [Control]

def signFlip (d : Fin 4) (ξ : Direction) : Direction :=
  ![![ξ 0, ξ 1, ξ 2], ![ξ 0, -ξ 1, -ξ 2],
    ![-ξ 0, ξ 1, -ξ 2], ![-ξ 0, -ξ 1, ξ 2]] d

def quarter (q : Fin 2) (ξ : Direction) : Direction :=
  ![ξ, ![-ξ 1, ξ 0, ξ 2]] q

def cycle (c : Fin 3) (ξ : Direction) : Direction :=
  ![ξ, ![ξ 2, ξ 0, ξ 1], ![ξ 1, ξ 2, ξ 0]] c

def rotate (r : Control) (ξ : Direction) : Direction :=
  cycle r.1 (quarter r.2.1 (signFlip r.2.2 ξ))

def signFlipLinear (d : Fin 4) : Direction →ₗ[ℝ] Direction where
  toFun := signFlip d
  map_add' x y := by
    ext a
    fin_cases d <;> fin_cases a <;> simp [signFlip, add_comm]
  map_smul' s x := by
    ext a
    fin_cases d <;> fin_cases a <;> simp [signFlip]

def quarterLinear (q : Fin 2) : Direction →ₗ[ℝ] Direction where
  toFun := quarter q
  map_add' x y := by
    ext a
    fin_cases q <;> fin_cases a <;> simp [quarter, add_comm]
  map_smul' s x := by
    ext a
    fin_cases q <;> fin_cases a <;> simp [quarter]

def cycleLinear (c : Fin 3) : Direction →ₗ[ℝ] Direction where
  toFun := cycle c
  map_add' x y := by
    ext a
    fin_cases c <;> fin_cases a <;> simp [cycle]
  map_smul' s x := by
    ext a
    fin_cases c <;> fin_cases a <;> simp [cycle]

def rotateLinear (r : Control) : Direction →ₗ[ℝ] Direction :=
  (cycleLinear r.1).comp ((quarterLinear r.2.1).comp (signFlipLinear r.2.2))

@[simp] theorem rotateLinear_apply (r : Control) (ξ : Direction) :
    rotateLinear r ξ = rotate r ξ := rfl

theorem continuous_rotate (r : Control) : Continuous (rotate r) :=
  (rotateLinear r).continuous_of_finiteDimensional

def rotationMatrix (r : Control) : Matrix (Fin 3) (Fin 3) ℝ :=
  LinearMap.toMatrix' (rotateLinear r)

@[simp] theorem rotationMatrix_apply (r : Control) (a b : Fin 3) :
    rotationMatrix r a b = rotate r (Pi.single b 1) a := rfl

theorem det_rotationMatrix (r : Control) : Matrix.det (rotationMatrix r) = 1 := by
  rcases r with ⟨c, q, d⟩
  fin_cases c <;> fin_cases q <;> fin_cases d <;>
    norm_num [Matrix.det_fin_three, rotationMatrix_apply, rotate, cycle, quarter,
      signFlip, Pi.single_apply]

theorem det_rotateLinear (r : Control) : LinearMap.det (rotateLinear r) = 1 := by
  rw [← LinearMap.det_toMatrix']
  exact det_rotationMatrix r

private theorem fingerprint_cycle_zero (q : Fin 2) (d : Fin 4) (s : Control)
    (h : rotate (0, q, d) (![1, 2, 3] : Direction) = rotate s ![1, 2, 3]) :
    (0, q, d) = s := by
  rcases s with ⟨c', q', d'⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases q <;> fin_cases d <;>
    fin_cases c' <;> fin_cases q' <;> fin_cases d'
  all_goals
    solve
    | rfl
    | norm_num [rotate, cycle, quarter, signFlip] at h0
    | norm_num [rotate, cycle, quarter, signFlip] at h1

private theorem fingerprint_cycle_one (q : Fin 2) (d : Fin 4) (s : Control)
    (h : rotate (1, q, d) (![1, 2, 3] : Direction) = rotate s ![1, 2, 3]) :
    (1, q, d) = s := by
  rcases s with ⟨c', q', d'⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases q <;> fin_cases d <;>
    fin_cases c' <;> fin_cases q' <;> fin_cases d'
  all_goals
    solve
    | rfl
    | norm_num [rotate, cycle, quarter, signFlip] at h0
    | norm_num [rotate, cycle, quarter, signFlip] at h1

private theorem fingerprint_cycle_two (q : Fin 2) (d : Fin 4) (s : Control)
    (h : rotate (2, q, d) (![1, 2, 3] : Direction) = rotate s ![1, 2, 3]) :
    (2, q, d) = s := by
  rcases s with ⟨c', q', d'⟩
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  fin_cases q <;> fin_cases d <;>
    fin_cases c' <;> fin_cases q' <;> fin_cases d'
  all_goals
    solve
    | rfl
    | norm_num [rotate, cycle, quarter, signFlip] at h0
    | norm_num [rotate, cycle, quarter, signFlip] at h1

/-- One vector with distinct positive coordinates distinguishes all controls. -/
theorem rotate_fingerprint_injective :
    Function.Injective (fun r : Control => rotate r (![1, 2, 3] : Direction)) := by
  rintro ⟨c, q, d⟩ s h
  fin_cases c
  · exact fingerprint_cycle_zero q d s h
  · exact fingerprint_cycle_one q d s h
  · exact fingerprint_cycle_two q d s h

theorem rotate_injective : Function.Injective (rotate : Control → Direction → Direction) := by
  intro r s h
  exact rotate_fingerprint_injective (congrFun h (![1, 2, 3] : Direction))

theorem sizeSq_signFlip (d : Fin 4) (ξ : Direction) : sizeSq (signFlip d ξ) = sizeSq ξ := by
  fin_cases d <;> simp [sizeSq, signFlip, Fin.sum_univ_succ]

theorem sizeSq_quarter (q : Fin 2) (ξ : Direction) : sizeSq (quarter q ξ) = sizeSq ξ := by
  fin_cases q <;> simp [sizeSq, quarter, Fin.sum_univ_succ]
  ring

theorem sizeSq_cycle (c : Fin 3) (ξ : Direction) : sizeSq (cycle c ξ) = sizeSq ξ := by
  fin_cases c <;> simp [sizeSq, cycle, Fin.sum_univ_succ] <;> ring

@[simp] theorem sizeSq_rotate (r : Control) (ξ : Direction) : sizeSq (rotate r ξ) = sizeSq ξ := by
  simp only [rotate, sizeSq_cycle, sizeSq_quarter, sizeSq_signFlip]

def dot (x y : Direction) : ℝ := ∑ a : Fin 3, x a * y a

@[simp] theorem dot_self (ξ : Direction) : dot ξ ξ = sizeSq ξ := by
  simp only [dot, sizeSq, pow_two]

theorem sum_rotate (ξ : Direction) (a : Fin 3) :
    (∑ r : Control, rotate r ξ a) = 0 := by
  fin_cases a <;>
    simp [Control, rotate, cycle, quarter, signFlip, Fintype.sum_prod_type,
      Fin.sum_univ_succ]

theorem sum_rotate_pair (x y : Direction) (a b : Fin 3) :
    (∑ r : Control, rotate r x a * rotate r y b) =
      if a = b then 8 * dot x y else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [Control, rotate, cycle, quarter, signFlip, dot, Fintype.sum_prod_type,
      Fin.sum_univ_succ] <;> ring

theorem sum_rotate_mul (ξ : Direction) (a b : Fin 3) :
    (∑ r : Control, rotate r ξ a * rotate r ξ b) =
      if a = b then 8 * sizeSq ξ else 0 := by
  simpa only [dot_self] using sum_rotate_pair ξ ξ a b

theorem mean_rotate (ξ : Direction) (a : Fin 3) :
    (1 / 24 : ℝ) * (∑ r : Control, rotate r ξ a) = 0 := by
  rw [sum_rotate, mul_zero]

theorem mean_rotate_mul (ξ : Direction) (a b : Fin 3) :
    (1 / 24 : ℝ) * (∑ r : Control, rotate r ξ a * rotate r ξ b) =
      if a = b then sizeSq ξ / 3 else 0 := by
  rw [sum_rotate_mul]
  split_ifs <;> ring

/-- A matrix represents a bilinear response in the chosen orthonormal triple. -/
def response (B : Matrix (Fin 3) (Fin 3) ℝ) (x y : Direction) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, B a b * (x a * y b)

theorem sum_response (B : Matrix (Fin 3) (Fin 3) ℝ) (x y : Direction) :
    (∑ r : Control, response B (rotate r x) (rotate r y)) =
      8 * (∑ a : Fin 3, B a a) * dot x y := by
  classical
  unfold response
  calc
    _ = ∑ a : Fin 3, ∑ b : Fin 3,
        B a b * (∑ r : Control, rotate r x a * rotate r y b) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [sum_rotate_pair]
      simp [mul_ite, Finset.mul_sum, mul_assoc, mul_comm]

/-- The average is the scalar trace response; symmetry of `B` is not needed. -/
theorem mean_response (B : Matrix (Fin 3) (Fin 3) ℝ) (x y : Direction) :
    (1 / 24 : ℝ) * (∑ r : Control, response B (rotate r x) (rotate r y)) =
      (Matrix.trace B / 3) * dot x y := by
  rw [sum_response]
  change (1 / 24 : ℝ) * (8 * (∑ a : Fin 3, B a a) * dot x y) =
    ((∑ a : Fin 3, B a a) / 3) * dot x y
  ring

/-- Each transformed coordinate is one signed input coordinate. -/
theorem coordinate_signed (r : Control) (a : Fin 3) :
    ∃ b : Fin 3, (∀ ξ : Direction, rotate r ξ a = ξ b) ∨
      (∀ ξ : Direction, rotate r ξ a = -ξ b) := by
  rcases r with ⟨c, q, d⟩
  fin_cases c <;> fin_cases q <;> fin_cases d <;> fin_cases a <;>
    solve
    | refine ⟨0, Or.inl ?_⟩; intro ξ; simp [rotate, cycle, quarter, signFlip]
    | refine ⟨0, Or.inr ?_⟩; intro ξ; simp [rotate, cycle, quarter, signFlip]
    | refine ⟨1, Or.inl ?_⟩; intro ξ; simp [rotate, cycle, quarter, signFlip]
    | refine ⟨1, Or.inr ?_⟩; intro ξ; simp [rotate, cycle, quarter, signFlip]
    | refine ⟨2, Or.inl ?_⟩; intro ξ; simp [rotate, cycle, quarter, signFlip]
    | refine ⟨2, Or.inr ?_⟩; intro ξ; simp [rotate, cycle, quarter, signFlip]

theorem coordinate_memLp {μ : Measure Direction} [IsProbabilityMeasure μ]
    (h2 : ∀ a : Fin 3, MemLp (fun ξ : Direction => ξ a) 2 μ)
    (r : Control) (a : Fin 3) : MemLp (fun ξ : Direction => rotate r ξ a) 2 μ := by
  obtain ⟨b, hb | hb⟩ := coordinate_signed r a
  · simpa only [hb] using h2 b
  · simpa only [hb, Pi.neg_apply] using! (h2 b).neg

end GeneratedFoundations.Geometry.SourceFiniteRotations
