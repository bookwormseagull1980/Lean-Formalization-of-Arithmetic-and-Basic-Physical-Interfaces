module

public import GeneratedFoundations.Physical.SourceInternalYangMillsResponse
public import GeneratedFoundations.Geometry.SourceConformalVariation
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The full real adjoint comparison trace

The connection covariance distributes a fixed total intensity among eight
colour directions. The comparison trace sums over the eight components of
the real adjoint field. This module keeps that trace multiplicity separate
from the 120 source coefficients and from the Casimir feedback coefficient.
The conformal response exported by the geometry branch remains scalar.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace GeneratedFoundations.Physical.SourceAdjointComparison

open SourceInternalYangMillsResponse SourceConformalResponse

/-- Rank of the real adjoint comparison fibre. -/
def adjointTraceMultiplicity : ℝ := Fintype.card (Fin colourDirectionCount)

@[simp] theorem adjointTraceMultiplicity_eq : adjointTraceMultiplicity = 8 := by
  norm_num [adjointTraceMultiplicity, colourDirectionCount]

theorem adjointTraceMultiplicity_pos : 0 < adjointTraceMultiplicity := by
  rw [adjointTraceMultiplicity_eq]
  norm_num

theorem sum_adjoint_components {ι : Type*} [Fintype ι] (e : ι → ℝ) :
    (∑ p : ι × Fin colourDirectionCount, e p.1) =
      adjointTraceMultiplicity * ∑ j : ι, e j := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  simpa only [adjointTraceMultiplicity, Fintype.card_fin] using
    (Finset.mul_sum (Finset.univ : Finset ι) e (colourDirectionCount : ℝ)).symm

/-- The ordinary trace on the scalar eigenspaces tensored with the real
adjoint fibre counts every colour component. -/
theorem trace_diagonal_adjoint {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℝ) :
    Matrix.trace (Matrix.diagonal (fun p : ι × Fin colourDirectionCount => e p.1)) =
      adjointTraceMultiplicity * Matrix.trace (Matrix.diagonal e) := by
  rw [Matrix.trace_diagonal, Matrix.trace_diagonal]
  exact sum_adjoint_components e

/-- The compensated Gaussian comparison spectral cost is additive over
the real adjoint components, with the same scalar precision ratio. -/
theorem finite_adjoint_comparison {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (g q : ℝ) :
    (∑ p : ι × Fin colourDirectionCount,
      (g * q / a p.1 - Real.log (1 + g * q / a p.1))) =
      adjointTraceMultiplicity *
        ∑ j : ι, (g * q / a j - Real.log (1 + g * q / a j)) := by
  exact sum_adjoint_components (fun j => g * q / a j - Real.log (1 + g * q / a j))

/-- Complete restoring slope of the full real adjoint comparison. -/
def adjointResponse (z : ℝ) : ℝ := adjointTraceMultiplicity * completeResponse z

/-- Complete curvature of the same comparison cost. -/
def adjointCurvature (z : ℝ) : ℝ := adjointTraceMultiplicity * completeCurvature z

theorem adjointCurvature_pos {z : ℝ} (hz : 0 < z) : 0 < adjointCurvature z :=
  mul_pos adjointTraceMultiplicity_pos (completeCurvature_pos hz.le)

theorem adjointResponse_hasDerivAt {z : ℝ} (hz : 0 < z) :
    HasDerivAt adjointResponse (adjointCurvature z) z :=
  (Geometry.SourceConformalVariation.completeResponse_hasDerivAt hz).const_mul
    adjointTraceMultiplicity

end GeneratedFoundations.Physical.SourceAdjointComparison
