module

public import GeneratedFoundations.Physical.SourceHaarYangMillsAction

/-!
# The original colour trace of the nonlinear Haar curvature

The continuous curvature representatives use the same source differential
and the actual commutator matrices. Their coefficient norm is the integral
of the normalized source trace. This identifies the Haar action with its
matrix curvature expression before a Hessian or spectral bound is taken.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ComplexConjugate
open GeneratedFoundations.Geometry.SourceSpinCentre
open GeneratedFoundations.Geometry.SourceCentralObservations
open GeneratedFoundations.Geometry.SourceQuotientHilbert
open GeneratedFoundations.Geometry.SourceOneFormContinuousCore
open GeneratedFoundations.Geometry.SourceOneFormHodgeLaplacian
open GeneratedFoundations.Physical.SourceHaarYangMillsAction

namespace GeneratedFoundations.Physical.SourceHaarCurvatureTrace

def firstAxis : Fin 3 → Fin 3 := ![1, 2, 0]
def secondAxis : Fin 3 → Fin 3 := ![2, 0, 1]

def connectionMatrix (A : ColourCore) (j : Fin 3) (x : CentralQuotient) :=
  SourceComplexColourCoordinates.lieMatrix (fun a => representative (A a) j x)

theorem vertex_matrix (A : ColourCore) (j : Fin 3) (x : CentralQuotient) :
    SourceComplexColourCoordinates.lieMatrix
        (fun a => vertexRepresentative A a j x) =
      connectionMatrix A (firstAxis j) x * connectionMatrix A (secondAxis j) x -
        connectionMatrix A (secondAxis j) x * connectionMatrix A (firstAxis j) x := by
  fin_cases j <;>
    exact SourceComplexColourCoordinates.lieMatrix_bracket _ _

def curvatureRepresentative (L : ℝ) (A : ColourCore) (a : Fin 8) : ContinuousField :=
  ((1 / L : ℝ) : ℂ) • representative (coreCurl (A a)) + vertexRepresentative A a

def synthesize (f : Fin 8 → ContinuousField) : ColourFields :=
  WithLp.toLp 2 (fun a => toHaar (f a))

theorem synthesize_curvature (L : ℝ) (A : ColourCore) :
    synthesize (curvatureRepresentative L A) = curvature L A := by
  apply (WithLp.equiv 2 (Fin 8 →
    GeneratedFoundations.Geometry.SourceOneFormHaarBlock.OneFormL2)).injective
  funext a
  change toHaar (((1 / L : ℝ) : ℂ) • representative (coreCurl (A a)) +
    vertexRepresentative A a) = _
  rw [map_add, map_smul, representative_toHaar]
  rfl

/-- Pointwise matrix curvature in the existing oriented source frame. -/
def matrixCurvature (L : ℝ) (A : ColourCore) (j : Fin 3) (x : CentralQuotient) :=
  ((1 / L : ℝ) : ℂ) • SourceComplexColourCoordinates.lieMatrix
      (fun a => representative (coreCurl (A a)) j x) +
    (connectionMatrix A (firstAxis j) x * connectionMatrix A (secondAxis j) x -
      connectionMatrix A (secondAxis j) x * connectionMatrix A (firstAxis j) x)

theorem curvature_matrix (L : ℝ) (A : ColourCore) (j : Fin 3)
    (x : CentralQuotient) :
    SourceComplexColourCoordinates.lieMatrix
        (fun a => curvatureRepresentative L A a j x) = matrixCurvature L A j x := by
  have hadd (c d : SourceComplexColourCoordinates.Coordinates) :
      SourceComplexColourCoordinates.lieMatrix (c + d) =
        SourceComplexColourCoordinates.lieMatrix c + SourceComplexColourCoordinates.lieMatrix d := by
    simp [SourceComplexColourCoordinates.lieMatrix,
      SourceComplexColourCoordinates.hermitianMatrix, add_smul, Finset.sum_add_distrib, smul_add]
  change SourceComplexColourCoordinates.lieMatrix
    ((((1 / L : ℝ) : ℂ) • (fun a => representative (coreCurl (A a)) j x)) +
      (fun a => vertexRepresentative A a j x)) = _
  rw [hadd, SourceComplexColourCoordinates.lieMatrix_smul, vertex_matrix]
  rfl

theorem scalar_normSq (f : C(CentralQuotient, ℂ)) :
    ‖ContinuousMap.toLp 2 quotientHaar ℂ f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂quotientHaar := by
  have hinner := ContinuousMap.inner_toLp (μ := quotientHaar) f f
  have hreal := congrArg Complex.re hinner
  have hnorm : (inner ℂ (ContinuousMap.toLp 2 quotientHaar ℂ f)
      (ContinuousMap.toLp 2 quotientHaar ℂ f)).re =
        ‖ContinuousMap.toLp 2 quotientHaar ℂ f‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have hc : (fun x => f x * conj (f x)) =
      fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    simpa only [← Complex.ofReal_pow] using Complex.mul_conj' (f x)
  rw [hnorm, hc, integral_complex_ofReal] at hreal
  exact hreal

theorem synthesize_normSq (f : Fin 8 → ContinuousField) :
    ‖synthesize f‖ ^ 2 = ∫ x, ∑ a, ∑ j, ‖f a j x‖ ^ 2 ∂quotientHaar := by
  have hi (a : Fin 8) (j : Fin 3) : Integrable (fun x => ‖f a j x‖ ^ 2) quotientHaar :=
    ((f a j).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hfield (g : ContinuousField) :
      ‖toHaar g‖ ^ 2 = ∑ j, ‖ContinuousMap.toLp 2 quotientHaar ℂ (g j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ a, ‖toHaar (f a)‖ ^ 2) = _
  simp_rw [hfield, scalar_normSq]
  simp_rw [← integral_finsetSum Finset.univ (fun j _ => hi _ j)]
  exact (integral_finsetSum Finset.univ
    (fun a _ => integrable_finsetSum Finset.univ (fun j _ => hi a j))).symm

/-- Exact source-metric identity, including the nonlinear commutators.
The factor two is forced by `trace(T_a T_b) = delta_ab / 2`. -/
theorem curvature_normSq_eq_trace (L : ℝ) (A : ColourCore) :
    ‖curvature L A‖ ^ 2 =
      ∫ x, ∑ j : Fin 3,
        2 * SourceGeneratedYangMillsFrameResponse.frameQuadratic
          (matrixCurvature L A j x) ∂quotientHaar := by
  rw [← synthesize_curvature, synthesize_normSq]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [← curvature_matrix]
  exact (SourceComplexColourCoordinates.normalized_trace_norm _).symm

/-- The original nonlinear action is the integrated matrix-curvature action
with the normalization fixed by the same source colour metric. -/
theorem action_eq_trace (L z radial : ℝ) (A : ColourCore) :
    action L z radial A =
      SourceGeneratedRadialVariation.sourceRadialPotential z radial +
        (1 / 2 : ℝ) * (∫ x, ∑ j : Fin 3,
          2 * SourceGeneratedYangMillsFrameResponse.frameQuadratic
            (matrixCurvature L A j x) ∂quotientHaar) +
        (1 / 2 : ℝ) * SourceGeneratedYangMillsGap.coclosedResponseShift L
          (z + SourceGeneratedYangMillsResponseHessian.sourceRadialIncrement z radial) *
            ‖field A‖ ^ 2 := by
  rw [action, curvature_normSq_eq_trace]

end GeneratedFoundations.Physical.SourceHaarCurvatureTrace
