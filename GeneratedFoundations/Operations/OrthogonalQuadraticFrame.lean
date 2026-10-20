module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Complex.Basic

/-!
# Orthogonal changes of a finite quadratic frame

The result applies to actual algebra elements before any trace or scalar
evaluation. No commutativity between those elements is used. Consequently
all cross products are retained while the orthogonal coefficient contraction
is performed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Operations.OrthogonalQuadraticFrame

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]
  [Ring A] [Algebra ℂ A]

def OrthogonalChange (O : Matrix ι ι ℝ) : Prop :=
  ∀ b c, ∑ a, O a b * O a c = if b = c then 1 else 0

def rotated (O : Matrix ι ι ℝ) (g : ι → A) (a : ι) : A :=
  ∑ b, (O a b : ℂ) • g b

/-- The complete quadratic sum is unchanged. The proof contracts the two
frame coefficients only after expanding all ordered algebra products. -/
theorem quadratic_invariant (O : Matrix ι ι ℝ)
    (hO : OrthogonalChange O) (g : ι → A) :
    (∑ a, rotated O g a * rotated O g a) = ∑ a, g a * g a := by
  have ho (b c : ι) :
      (∑ a, (O a b : ℂ) * (O a c : ℂ)) = if b = c then 1 else 0 := by
    simpa only [Complex.ofReal_sum, Complex.ofReal_mul, apply_ite,
      Complex.ofReal_one, Complex.ofReal_zero] using
      congrArg (fun x : ℝ => (x : ℂ)) (hO b c)
  calc
    (∑ a, rotated O g a * rotated O g a) =
        ∑ a, ∑ b, ∑ c, ((O a b : ℂ) * (O a c : ℂ)) • (g b * g c) := by
      simp only [rotated]
      simp only [Finset.sum_mul]
      simp only [Finset.mul_sum]
      simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      rw [mul_comm (O a c : ℂ) (O a b : ℂ)]
    _ = ∑ b, ∑ c, ∑ a,
        ((O a b : ℂ) * (O a c : ℂ)) • (g b * g c) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ b, ∑ c,
        (∑ a, (O a b : ℂ) * (O a c : ℂ)) • (g b * g c) := by
      simp only [Finset.sum_smul]
    _ = ∑ a, g a * g a := by
      simp_rw [ho]
      simp

end GeneratedFoundations.Operations.OrthogonalQuadraticFrame
