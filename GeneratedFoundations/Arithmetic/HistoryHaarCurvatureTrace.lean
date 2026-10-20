module

public import GeneratedFoundations.Arithmetic.HistoryHaarMatrixCurvature
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The original matrix trace of the arithmetic Haar curvature

The coefficient metric of the complete arithmetic matrix algebra is its
Hilbert--Schmidt trace. This metric is identified pointwise and after Haar
integration with the already defined nonlinear curvature action. Both
off-diagonal entries and the full matrix commutator remain in the formula.
The identity holds for every complex connection coefficient; skew-adjoint
coefficients give the equivalent negative-trace convention.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GeneratedFoundations.Arithmetic.HistoryHaarCurvatureTrace

open HistoryHaarMatrixCurvature
open Geometry.SourceSpinCentre Geometry.SourceQuotientHilbert
open Geometry.SourceOneFormContinuousCore Geometry.SourceOneFormHodgeLaplacian
open Geometry.SourceOneFormHaarBlock

def firstAxis : Fin 3 → Fin 3 := ![1, 2, 0]
def secondAxis : Fin 3 → Fin 3 := ![2, 0, 1]

def connectionMatrix (N : ℕ) (A : Coefficients N) (j : Fin 3)
    (x : CentralQuotient) : HistoryCliffordAction.Algebra N :=
  fun a b => matrixRepresentative N A j a b x

theorem vertex_matrix (N : ℕ) (A : Coefficients N) (j : Fin 3)
    (x : CentralQuotient) :
    ((fun a b => vertexRepresentative N A a b j x) : HistoryCliffordAction.Algebra N) =
      connectionMatrix N A (firstAxis j) x * connectionMatrix N A (secondAxis j) x -
        connectionMatrix N A (secondAxis j) x * connectionMatrix N A (firstAxis j) x := by
  fin_cases j <;>
    ext a b <;> simp [vertexRepresentative, HistoryHaarMatrixCurvature.commutator, connectionMatrix,
      firstAxis, secondAxis, Matrix.mul_apply]

def curvatureRepresentative (N : ℕ) (A : Coefficients N)
    (a b : Index N) : ContinuousField :=
  representative (coreCurl (A a b)) + vertexRepresentative N A a b

def synthesize (N : ℕ) (f : Index N → Index N → ContinuousField) : Fields N :=
  WithLp.toLp 2 (fun i => toHaar (f i.1 i.2))

theorem synthesize_curvature (N : ℕ) (A : Coefficients N) :
    synthesize N (curvatureRepresentative N A) = curvature N A := by
  apply (WithLp.equiv 2 _).injective
  funext i
  change toHaar (representative (coreCurl (A i.1 i.2)) +
    vertexRepresentative N A i.1 i.2) = _
  rw [map_add, representative_toHaar]
  rfl

def matrixCurvature (N : ℕ) (A : Coefficients N) (j : Fin 3)
    (x : CentralQuotient) : HistoryCliffordAction.Algebra N :=
  Matrix.of (fun a b => representative (coreCurl (A a b)) j x) +
    (connectionMatrix N A (firstAxis j) x * connectionMatrix N A (secondAxis j) x -
      connectionMatrix N A (secondAxis j) x * connectionMatrix N A (firstAxis j) x)

theorem curvature_matrix (N : ℕ) (A : Coefficients N) (j : Fin 3)
    (x : CentralQuotient) :
    ((fun a b => curvatureRepresentative N A a b j x) : HistoryCliffordAction.Algebra N) =
      matrixCurvature N A j x := by
  unfold curvatureRepresentative matrixCurvature
  rw [← vertex_matrix]
  rfl

theorem trace_normSq (N : ℕ) (K : HistoryCliffordAction.Algebra N) :
    (Matrix.trace (K.conjTranspose * K)).re =
      ∑ a, ∑ b, ‖K a b‖ ^ 2 := by
  change (∑ a, ∑ b, conj (K b a) * K b a).re = _
  rw [Complex.re_sum]
  simp_rw [Complex.re_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [mul_comm, Complex.mul_conj']
  simp [← Complex.ofReal_pow]

theorem trace_skew (N : ℕ) (K : HistoryCliffordAction.Algebra N)
    (hK : K.conjTranspose = -K) :
    -(Matrix.trace (K * K)).re = ∑ a, ∑ b, ‖K a b‖ ^ 2 := by
  have h := trace_normSq N K
  simpa only [hK, neg_mul, Matrix.trace_neg, Complex.neg_re] using h

theorem scalar_normSq (f : C(CentralQuotient, ℂ)) :
    ‖ContinuousMap.toLp 2 quotientHaar ℂ f‖ ^ 2 =
      ∫ x, ‖f x‖ ^ 2 ∂quotientHaar := by
  have h := congrArg Complex.re (ContinuousMap.inner_toLp (μ := quotientHaar) f f)
  have hc : (fun x => f x * conj (f x)) = fun x => ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    funext x
    simpa only [← Complex.ofReal_pow] using Complex.mul_conj' (f x)
  rw [hc, integral_complex_ofReal] at h
  exact (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans h

theorem synthesize_normSq (N : ℕ) (f : Index N → Index N → ContinuousField) :
    ‖synthesize N f‖ ^ 2 =
      ∫ x, ∑ a, ∑ b, ∑ j, ‖f a b j x‖ ^ 2 ∂quotientHaar := by
  have hi (a b : Index N) (j : Fin 3) :
      Integrable (fun x => ‖f a b j x‖ ^ 2) quotientHaar :=
    ((f a b j).continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf (g : ContinuousField) :
      ‖toHaar g‖ ^ 2 = ∑ j, ‖ContinuousMap.toLp 2 quotientHaar ℂ (g j)‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  rw [PiLp.norm_sq_eq_of_L2]
  change (∑ i : Index N × Index N, ‖toHaar (f i.1 i.2)‖ ^ 2) = _
  rw [Fintype.sum_prod_type]
  simp_rw [hf, scalar_normSq]
  simp_rw [← integral_finsetSum Finset.univ (fun j _ => hi _ _ j)]
  simp_rw [← integral_finsetSum Finset.univ
    (fun b _ => integrable_finsetSum Finset.univ (fun j _ => hi _ b j))]
  exact (integral_finsetSum Finset.univ
    (fun a _ => integrable_finsetSum Finset.univ
      (fun b _ => integrable_finsetSum Finset.univ (fun j _ => hi a b j)))).symm

theorem curvature_normSq_eq_trace (N : ℕ) (A : Coefficients N) :
    ‖curvature N A‖ ^ 2 = ∫ x, ∑ j : Fin 3,
      (Matrix.trace ((matrixCurvature N A j x).conjTranspose *
        matrixCurvature N A j x)).re ∂quotientHaar := by
  rw [← synthesize_curvature, synthesize_normSq]
  apply integral_congr_ae
  filter_upwards [] with x
  calc
    _ = ∑ a, ∑ j : Fin 3, ∑ b, ‖curvatureRepresentative N A a b j x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm
    _ = ∑ j : Fin 3, ∑ a, ∑ b, ‖curvatureRepresentative N A a b j x‖ ^ 2 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [trace_normSq, ← curvature_matrix]

theorem action_eq_trace (N : ℕ) (A : Coefficients N) :
    action N A = (∫ x, ∑ j : Fin 3,
      (Matrix.trace ((matrixCurvature N A j x).conjTranspose *
        matrixCurvature N A j x)).re ∂quotientHaar) / 2 := by
  rw [action, curvature_normSq_eq_trace]

end GeneratedFoundations.Arithmetic.HistoryHaarCurvatureTrace
