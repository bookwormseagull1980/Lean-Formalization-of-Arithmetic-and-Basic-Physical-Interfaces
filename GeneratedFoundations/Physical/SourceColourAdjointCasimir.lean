module

public import GeneratedFoundations.Physical.SourceColourCasimir
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Ring

/-!
# The adjoint colour Casimir in the generated normalization

The eight trace-normalized source colour generators are already explicit.
Their double commutator is evaluated here without importing a structure-
constant table.  The result is the adjoint Casimir `3` in precisely the same
normalization that gives the defining Casimir `4/3`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Matrix
open GeneratedFoundations.Physical.SourceColourCasimir

namespace GeneratedFoundations.Physical.SourceColourAdjointCasimir

abbrev ColourMatrix := SourceColourCasimir.Mat3

def commutator (A B : ColourMatrix) : ColourMatrix := A * B - B * A

/-- Quadratic adjoint action computed from the same normalized generators. -/
def adjointCasimirOperator (X : ColourMatrix) : ColourMatrix :=
  ∑ a, commutator (generator a) (commutator (generator a) X)

/-- The matrix sandwich appearing in the completeness relation. -/
def generatorSandwich (X : ColourMatrix) : ColourMatrix :=
  ∑ a, generator a * X * generator a

@[simp] private theorem source_rootThree_sq : SourceColourCasimir.rootThree ^ 2 = 3 := by
  dsimp [SourceColourCasimir.rootThree]
  exact_mod_cast (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3))

/-- Completeness of the eight generated trace-normalized colour matrices. -/
theorem generatorSandwich_eq (X : ColourMatrix) :
    generatorSandwich X =
      (Matrix.trace X / 2) • (1 : ColourMatrix) - (1 / 6 : ℂ) • X := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [generatorSandwich, generator, Matrix.mul_apply, Matrix.trace,
      Matrix.vecMul, dotProduct,
      Fin.sum_univ_succ] <;>
    ring_nf <;> simp only [source_rootThree_sq, Complex.I_sq] <;>
    ring

theorem adjointCasimir_expansion (X : ColourMatrix) :
    adjointCasimirOperator X =
      matrixCasimir * X - 2 • generatorSandwich X + X * matrixCasimir := by
  calc
    adjointCasimirOperator X =
        ∑ a, ((generator a * generator a) * X -
          2 • (generator a * X * generator a) +
          X * (generator a * generator a)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      unfold commutator
      noncomm_ring
    _ = matrixCasimir * X - 2 • generatorSandwich X + X * matrixCasimir := by
      simp only [matrixCasimir, generatorSandwich]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.smul_sum,
        Finset.sum_mul, Finset.mul_sum]

/-- The adjoint Casimir is three on every traceless colour matrix. -/
theorem adjointCasimir_of_trace_zero (X : ColourMatrix)
    (hX : Matrix.trace X = 0) :
    adjointCasimirOperator X = (3 : ℂ) • X := by
  rw [adjointCasimir_expansion, matrixCasimir_eq, generatorSandwich_eq, hX]
  simp
  norm_num [two_mul]
  module

/-- Direct consequence for every generated colour basis vector. -/
theorem adjointCasimir_generator (b : Fin 8) :
    adjointCasimirOperator (generator b) = (3 : ℂ) • generator b :=
  adjointCasimir_of_trace_zero _ (generator_trace b)

def adjointCasimirIndex : ℝ := 3

theorem adjointCasimirIndex_eq : adjointCasimirIndex = 3 := rfl

theorem adjointCasimir_generator_real (b : Fin 8) :
    adjointCasimirOperator (generator b) =
      (adjointCasimirIndex : ℂ) • generator b := by
  simpa [adjointCasimirIndex] using adjointCasimir_generator b

structure Properties : Prop where
  generator_action : ∀ b,
    adjointCasimirOperator (generator b) = (3 : ℂ) • generator b
  index : adjointCasimirIndex = 3

theorem properties : Properties where
  generator_action := adjointCasimir_generator
  index := adjointCasimirIndex_eq

end GeneratedFoundations.Physical.SourceColourAdjointCasimir
