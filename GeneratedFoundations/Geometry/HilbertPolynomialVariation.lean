module

public import GeneratedFoundations.Geometry.HilbertTraceVariation

/-!
# Quadratic Hilbert paths and their complete variations

The quadratic coefficient in a covariant derivative is retained before the
norm is squared. Consequently the Hessian contains its pairing with the
background, in addition to the norm of the linearized response.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.HilbertPolynomialVariation

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def energy (x : H) : ℝ := ‖x‖ ^ 2 / 2

theorem energy_quadratic_path (x y z : H) (t : ℝ) :
    energy (x + t • y + t ^ 2 • z) =
      energy x + t * inner ℝ x y +
        t ^ 2 * (energy y + inner ℝ x z) +
        t ^ 3 * inner ℝ y z + t ^ 4 * energy z := by
  simp only [energy, norm_add_sq_real, inner_add_left,
    real_inner_smul_left, real_inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem energy_quadratic_path_hasDerivAt (x y z : H) (t : ℝ) :
    HasDerivAt (fun s : ℝ => energy (x + s • y + s ^ 2 • z))
      (inner ℝ x y + 2 * t * (energy y + inner ℝ x z) +
        3 * t ^ 2 * inner ℝ y z + 4 * t ^ 3 * energy z) t := by
  convert HilbertTraceVariation.quartic_hasDerivAt (energy x) (inner ℝ x y)
    (energy y + inner ℝ x z) (inner ℝ y z) (energy z) t using 1
  · funext s
    rw [energy_quadratic_path]

theorem inner_quadratic_linear (x y z a b : H) (t : ℝ) :
    inner ℝ (x + t • y + t ^ 2 • z) (a + t • b) =
      inner ℝ x a + t * (inner ℝ y a + inner ℝ x b) +
        t ^ 2 * (inner ℝ z a + inner ℝ y b) + t ^ 3 * inner ℝ z b := by
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right]
  ring

theorem inner_quadratic_linear_hasDerivAt_zero (x y z a b : H) :
    HasDerivAt (fun t : ℝ =>
      inner ℝ (x + t • y + t ^ 2 • z) (a + t • b))
      (inner ℝ y a + inner ℝ x b) 0 := by
  convert HilbertTraceVariation.quartic_hasDerivAt (inner ℝ x a)
    (inner ℝ y a + inner ℝ x b) (inner ℝ z a + inner ℝ y b)
    (inner ℝ z b) 0 0 using 1
  · funext t
    rw [inner_quadratic_linear]
    ring
  · simp

end GeneratedFoundations.Geometry.HilbertPolynomialVariation
