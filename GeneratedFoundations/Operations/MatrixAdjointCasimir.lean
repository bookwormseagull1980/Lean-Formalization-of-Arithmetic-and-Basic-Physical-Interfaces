module

public import Mathlib.Data.Matrix.Basis
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Ring

/-!
# The complete matrix adjoint Casimir

The matrix units and their trace-dual partners give a canonical completeness
sum. Its half-normalization is evaluated on every matrix, including the scalar
direction. The traceless eigenvalue is the actual carrier dimension; no fixed
colour multiplicity is supplied.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix

namespace GeneratedFoundations.Operations.MatrixAdjointCasimir

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Algebra (ι : Type*) := Matrix ι ι ℂ

def matrixUnit (i j : ι) : Algebra ι := Matrix.single i j 1

def commutator (X Y : Algebra ι) : Algebra ι := X * Y - Y * X

def sandwich (X : Algebra ι) : Algebra ι :=
  ∑ i, ∑ j, matrixUnit i j * X * matrixUnit j i

theorem sandwich_eq (X : Algebra ι) :
    sandwich X = Matrix.trace X • (1 : Algebra ι) := by
  simp only [sandwich, matrixUnit, Matrix.single_mul_mul_single, one_mul, mul_one]
  ext a b
  by_cases hab : a = b
  · subst b
    simp [Matrix.sum_apply, Matrix.single, Matrix.trace, eq_comm]
  · have h : ∀ x, ¬ (a = x ∧ b = x) := fun x hx => hab (hx.1.trans hx.2.symm)
    simp [Matrix.sum_apply, Matrix.single, Matrix.trace, eq_comm, hab, h]

def pairedSquareSum : Algebra ι := ∑ i, ∑ j, matrixUnit i j * matrixUnit j i

theorem pairedSquareSum_eq :
    pairedSquareSum (ι := ι) = (Fintype.card ι : ℂ) • (1 : Algebra ι) := by
  simpa [sandwich, pairedSquareSum, Matrix.trace_one] using sandwich_eq (1 : Algebra ι)

def adjointSum (X : Algebra ι) : Algebra ι :=
  ∑ i, ∑ j, commutator (matrixUnit i j) (commutator (matrixUnit j i) X)

theorem adjointSum_expansion (X : Algebra ι) :
    adjointSum X = pairedSquareSum * X - 2 • sandwich X + X * pairedSquareSum := by
  calc
    adjointSum X = ∑ i, ∑ j,
        (matrixUnit i j * matrixUnit j i * X -
          matrixUnit i j * X * matrixUnit j i -
          matrixUnit j i * X * matrixUnit i j +
          X * (matrixUnit j i * matrixUnit i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      unfold commutator
      noncomm_ring
    _ = _ := by
      have hs : (∑ i, ∑ j, matrixUnit j i * X * matrixUnit i j) = sandwich X := by
        rw [Finset.sum_comm]
        rfl
      have hp : (∑ i, ∑ j, matrixUnit j i * matrixUnit i j) = pairedSquareSum (ι := ι) := by
        rw [Finset.sum_comm]
        rfl
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.sum_mul, ← Finset.mul_sum]
      rw [hs, hp]
      change pairedSquareSum * X - sandwich X - sandwich X + X * pairedSquareSum = _
      module

/-- The half-trace normalization retains the full scalar kernel. -/
def casimir (X : Algebra ι) : Algebra ι := (1 / 2 : ℂ) • adjointSum X

theorem casimir_eq (X : Algebra ι) :
    casimir X = (Fintype.card ι : ℂ) • X - Matrix.trace X • (1 : Algebra ι) := by
  rw [casimir, adjointSum_expansion, pairedSquareSum_eq, sandwich_eq]
  simp only [smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem casimir_traceless (X : Algebra ι) (hX : Matrix.trace X = 0) :
    casimir X = (Fintype.card ι : ℂ) • X := by
  simp [casimir_eq, hX]

@[simp] theorem trace_casimir (X : Algebra ι) : Matrix.trace (casimir X) = 0 := by
  simp [casimir_eq, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
    mul_comm]

@[simp] theorem casimir_scalar (c : ℂ) : casimir (c • (1 : Algebra ι)) = 0 := by
  simp [casimir_eq, Matrix.trace_smul, Matrix.trace_one, smul_smul, mul_comm]

theorem casimir_kernel [Nonempty ι] (X : Algebra ι) :
    casimir X = 0 ↔ ∃ c : ℂ, X = c • (1 : Algebra ι) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  constructor
  · intro hX
    refine ⟨Matrix.trace X / Fintype.card ι, ?_⟩
    have he := (sub_eq_zero.mp ((casimir_eq X).symm.trans hX))
    have ht := congrArg (fun Y : Algebra ι => (Fintype.card ι : ℂ)⁻¹ • Y) he
    simpa [smul_smul, hd, div_eq_inv_mul] using ht
  · rintro ⟨c, rfl⟩
    exact casimir_scalar c

theorem casimir_conjugate (u : (Algebra ι)ˣ) (X : Algebra ι) :
    casimir ((↑u : Algebra ι) * X * (↑(u⁻¹) : Algebra ι)) =
      (↑u : Algebra ι) * casimir X * (↑(u⁻¹) : Algebra ι) := by
  have ht : Matrix.trace ((↑u : Algebra ι) * X * (↑(u⁻¹) : Algebra ι)) = Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, Units.inv_mul, one_mul]
  rw [casimir_eq, ht, casimir_eq]
  simp [mul_sub, sub_mul, mul_assoc]

end GeneratedFoundations.Operations.MatrixAdjointCasimir
