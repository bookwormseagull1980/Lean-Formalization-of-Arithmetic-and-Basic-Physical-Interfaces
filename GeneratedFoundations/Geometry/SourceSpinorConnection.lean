module

public import GeneratedFoundations.Geometry.SourceAxisMetric

/-!
# The spin connection computed from the generated source frame

Clifford multiplication uses the original unit source velocities. The metric
Koszul formula applied to their commutators determines the connection and
its contracted constant. No eigenvalue or connection coefficient is given
as an input.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open GeneratedFoundations.Operations.SourceSpinCorner
open GeneratedFoundations.Operations.SourceSpinCornerGroup
open GeneratedFoundations.Geometry.SourceAxisMetric

namespace GeneratedFoundations.Geometry.SourceSpinorConnection

def clifford (i : Fin 3) : Mat2 := -unitAxis i

theorem clifford_anticommutator (i j : Fin 3) :
    clifford i * clifford j + clifford j * clifford i =
      if i = j then (-2 : ℂ) • (1 : Mat2) else 0 := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [clifford, unitAxis, axisVelocity, spinMatrix, spinMatrix1,
      spinMatrix2, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_two] <;>
      ring_nf <;> norm_num

def koszul (i j k : Fin 3) : ℝ :=
  (tracePair (unitAxis i * unitAxis j - unitAxis j * unitAxis i) (unitAxis k) -
    tracePair (unitAxis j * unitAxis k - unitAxis k * unitAxis j) (unitAxis i) +
    tracePair (unitAxis k * unitAxis i - unitAxis i * unitAxis k) (unitAxis j)) / 2

def spinConnection (i : Fin 3) : Mat2 :=
  (1 / 4 : ℂ) • ∑ j : Fin 3, ∑ k : Fin 3,
    (koszul i j k : ℂ) • (clifford j * clifford k)

set_option maxHeartbeats 1600000 in
/-- The coefficients follow from the actual trace-metric frame. -/
theorem spinConnection_eq (i : Fin 3) :
    spinConnection i = (-1 / 2 : ℂ) • clifford i := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    norm_num [spinConnection, koszul, clifford, tracePair, unitAxis, axisVelocity,
      spinMatrix, spinMatrix1, spinMatrix2, spinMatrix3, Matrix.mul_apply,
      Matrix.trace, Fin.sum_univ_three, Fin.sum_univ_two,
      Matrix.conjTranspose_apply] <;> ring_nf <;> norm_num

theorem contracted_connection :
    (∑ i : Fin 3, clifford i * spinConnection i) = (3 / 2 : ℂ) • (1 : Mat2) := by
  simp_rw [spinConnection_eq]
  ext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [clifford, unitAxis, axisVelocity, spinMatrix, spinMatrix1,
      spinMatrix2, spinMatrix3, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.sum_univ_two] <;> ring_nf <;> norm_num

end GeneratedFoundations.Geometry.SourceSpinorConnection
