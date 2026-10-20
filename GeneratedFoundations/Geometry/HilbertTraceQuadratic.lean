module

public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The complete finite Hilbert trace quadratic form

The form is the trace of `X* X`, not a selected diagonal contribution of `X`.
Its expression in every orthonormal basis proves nonnegativity and
definiteness. The trace definition makes it independent of that basis.
-/

@[expose] public section

noncomputable section

namespace GeneratedFoundations.Geometry.HilbertTraceQuadratic

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [FiniteDimensional ℂ H]

def energy (X : Module.End ℂ H) : ℝ := (LinearMap.trace ℂ H (X.adjoint * X)).re

theorem energy_basis {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ H)
    (X : Module.End ℂ H) : energy X = ∑ i, ‖X (b i)‖ ^ 2 := by
  rw [energy, LinearMap.trace_eq_sum_inner _ b, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.End.mul_apply, LinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  change (Complex.ofReal ‖X (b i)‖ ^ 2).re = ‖X (b i)‖ ^ 2
  rw [← Complex.ofReal_pow, Complex.ofReal_re]

theorem energy_nonneg (X : Module.End ℂ H) : 0 ≤ energy X := by
  rw [energy_basis (stdOrthonormalBasis ℂ H)]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

@[simp] theorem energy_zero : energy (0 : Module.End ℂ H) = 0 := by
  simp [energy]

theorem energy_eq_zero_iff (X : Module.End ℂ H) : energy X = 0 ↔ X = 0 := by
  constructor
  · intro h
    let b := stdOrthonormalBasis ℂ H
    rw [energy_basis b] at h
    apply b.toBasis.ext
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => sq_nonneg ‖X (b j)‖)).mp h i (Finset.mem_univ i)
    change X (b i) = 0
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hi)
  · rintro rfl
    exact energy_zero

def conjugate (u : (Module.End ℂ H)ˣ) (X : Module.End ℂ H) : Module.End ℂ H :=
  (↑u⁻¹ : Module.End ℂ H) * X * (↑u : Module.End ℂ H)

theorem conjugate_energy (u : (Module.End ℂ H)ˣ)
    (hu : (↑u : Module.End ℂ H).adjoint = ↑u⁻¹) (X : Module.End ℂ H) :
    energy (conjugate u X) = energy X := by
  have hui : (↑u⁻¹ : Module.End ℂ H).adjoint = ↑u := by
    rw [← hu, LinearMap.adjoint_adjoint]
  have hs : (conjugate u X).adjoint * conjugate u X =
      (↑u⁻¹ : Module.End ℂ H) * (X.adjoint * X) * (↑u : Module.End ℂ H) := by
    simp only [conjugate, ← LinearMap.star_eq_adjoint, star_mul]
    simp only [LinearMap.star_eq_adjoint, hu, hui]
    simp [mul_assoc]
  have ht : LinearMap.trace ℂ H
      ((↑u⁻¹ : Module.End ℂ H) * (X.adjoint * X) * (↑u : Module.End ℂ H)) =
      LinearMap.trace ℂ H (X.adjoint * X) := by
    simpa only [inv_inv] using LinearMap.trace_conj ℂ (X.adjoint * X) u⁻¹
  rw [energy, hs, ht]
  rfl

end GeneratedFoundations.Geometry.HilbertTraceQuadratic
