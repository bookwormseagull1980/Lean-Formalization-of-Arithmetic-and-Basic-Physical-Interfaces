module

public import GeneratedFoundations.Geometry.HilbertTraceQuadratic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

/-!
# Complete trace pairings and quadratic-path variations

The real trace pairing retains every coefficient of both operators. Its
polarization gives the exact quartic expansion of the energy along a
quadratic operator path. The two derivatives are derivatives of that same
path, including its background--quadratic term.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.HilbertTraceVariation

open HilbertTraceQuadratic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

def pair (X Y : Module.End ℂ H) : ℝ :=
  (LinearMap.trace ℂ H (X.adjoint * Y)).re

theorem pair_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    (X Y : Module.End ℂ H) :
    pair X Y = ∑ i, (inner ℂ (X (b i)) (Y (b i))).re := by
  rw [pair, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right]

theorem pair_symm (X Y : Module.End ℂ H) : pair X Y = pair Y X := by
  simp only [pair_basis (stdOrthonormalBasis ℂ H)]
  apply Finset.sum_congr rfl
  intro i _
  exact inner_re_symm (𝕜 := ℂ) _ _

theorem pair_add_left (X Y Z : Module.End ℂ H) :
    pair (X + Y) Z = pair X Z + pair Y Z := by
  simp [pair_basis (stdOrthonormalBasis ℂ H), inner_add_left, Finset.sum_add_distrib]

theorem pair_add_right (X Y Z : Module.End ℂ H) :
    pair X (Y + Z) = pair X Y + pair X Z := by
  simp [pair_basis (stdOrthonormalBasis ℂ H), inner_add_right, Finset.sum_add_distrib]

theorem pair_smul_left (t : ℝ) (X Y : Module.End ℂ H) :
    pair ((t : ℂ) • X) Y = t * pair X Y := by
  rw [pair_basis (stdOrthonormalBasis ℂ H), pair_basis (stdOrthonormalBasis ℂ H),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (inner ℂ ((t : ℂ) • X ((stdOrthonormalBasis ℂ H) i))
    (Y ((stdOrthonormalBasis ℂ H) i))).re = _
  rw [inner_smul_left (𝕜 := ℂ)]
  simp

theorem pair_smul_right (t : ℝ) (X Y : Module.End ℂ H) :
    pair X ((t : ℂ) • Y) = t * pair X Y := by
  rw [pair_symm, pair_smul_left, pair_symm Y X]

theorem energy_eq_pair (X : Module.End ℂ H) : energy X = pair X X := rfl

theorem energy_quadratic_path (X Y Z : Module.End ℂ H) (t : ℝ) :
    energy (X + (t : ℂ) • Y + ((t ^ 2 : ℝ) : ℂ) • Z) =
      energy X + 2 * t * pair X Y +
        t ^ 2 * (energy Y + 2 * pair X Z) +
        2 * t ^ 3 * pair Y Z + t ^ 4 * energy Z := by
  simp only [energy_eq_pair, pair_add_left, pair_add_right,
    pair_smul_left, pair_smul_right, pair_symm Y X, pair_symm Z X, pair_symm Z Y]
  ring

theorem quartic_hasDerivAt (a₀ a₁ a₂ a₃ a₄ t : ℝ) :
    HasDerivAt (fun s : ℝ => a₀ + s * a₁ + s ^ 2 * a₂ + s ^ 3 * a₃ + s ^ 4 * a₄)
      (a₁ + 2 * t * a₂ + 3 * t ^ 2 * a₃ + 4 * t ^ 3 * a₄) t := by
  convert ((((hasDerivAt_const t a₀).add ((hasDerivAt_id t).mul_const a₁)).add
    (((hasDerivAt_id t).pow 2).mul_const a₂)).add
    (((hasDerivAt_id t).pow 3).mul_const a₃)).add
    (((hasDerivAt_id t).pow 4).mul_const a₄) using 1
  · funext s
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

theorem energy_quadratic_path_hasDerivAt (X Y Z : Module.End ℂ H) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => energy (X + (s : ℂ) • Y + ((s ^ 2 : ℝ) : ℂ) • Z))
      (2 * pair X Y + 2 * t * (energy Y + 2 * pair X Z) +
        6 * t ^ 2 * pair Y Z + 4 * t ^ 3 * energy Z) t := by
  convert quartic_hasDerivAt (energy X) (2 * pair X Y)
    (energy Y + 2 * pair X Z) (2 * pair Y Z) (energy Z) t using 1
  · funext s
    rw [energy_quadratic_path]
    ring
  · ring

theorem pair_quadratic_linear (X Y Z U V : Module.End ℂ H) (t : ℝ) :
    pair (X + (t : ℂ) • Y + ((t ^ 2 : ℝ) : ℂ) • Z) (U + (t : ℂ) • V) =
      pair X U + t * (pair Y U + pair X V) +
        t ^ 2 * (pair Z U + pair Y V) + t ^ 3 * pair Z V := by
  simp only [pair_add_left, pair_add_right, pair_smul_left, pair_smul_right]
  ring

theorem pair_quadratic_linear_hasDerivAt_zero (X Y Z U V : Module.End ℂ H) :
    HasDerivAt (fun t : ℝ =>
      pair (X + (t : ℂ) • Y + ((t ^ 2 : ℝ) : ℂ) • Z) (U + (t : ℂ) • V))
      (pair Y U + pair X V) 0 := by
  convert quartic_hasDerivAt (pair X U) (pair Y U + pair X V)
    (pair Z U + pair Y V) (pair Z V) 0 0 using 1
  · funext t
    rw [pair_quadratic_linear]
    simp
  · simp

end GeneratedFoundations.Geometry.HilbertTraceVariation
