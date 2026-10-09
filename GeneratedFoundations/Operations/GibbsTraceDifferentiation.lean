module

public import GeneratedFoundations.Operations.GibbsFiniteResponse
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Normed.Operator.Mul

/-!
# Differentiation of the Hermitian exponential trace

Unitary diagonalization transports the exponential derivative from a real
diagonal matrix to every Hermitian base point. Taking the trace yields the
gradient on the whole real space of Hermitian perturbations. The gradient is
expressed through a continuous bilinear trace pairing, so it can be
differentiated once more without restricting the perturbations to commute.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.GibbsTraceDifferentiation

open PreparedTraceForm (Mat Hermitian realTrace)
open GibbsExponentialDifferentiation

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

def conjugation (U : Matrix.unitaryGroup ι ℂ) : Mat ι →L[ℝ] Mat ι :=
  (Unitary.conjStarAlgAut ℝ (Mat ι) U).toAlgEquiv.toLinearEquiv.toLinearMap.toContinuousLinearMap

omit [Nonempty ι] in
@[simp] theorem conjugation_apply (U : Matrix.unitaryGroup ι ℂ) (B : Mat ι) :
    conjugation ι U B = (U : Mat ι) * B * (U : Mat ι).conjTranspose := rfl

omit [Nonempty ι] in
theorem conjugation_surjective (U : Matrix.unitaryGroup ι ℂ) :
    Function.Surjective (conjugation ι U) :=
  EquivLike.surjective (Unitary.conjStarAlgAut ℝ (Mat ι) U)

omit [Nonempty ι] in
theorem conjugation_mul (U : Matrix.unitaryGroup ι ℂ) (B K : Mat ι) :
    conjugation ι U (B * K) = conjugation ι U B * conjugation ι U K :=
  (Unitary.conjStarAlgAut ℝ (Mat ι) U).map_mul B K

omit [Nonempty ι] in
theorem conjugation_exp (U : Matrix.unitaryGroup ι ℂ) (B : Mat ι) :
    conjugation ι U (NormedSpace.exp B) = NormedSpace.exp (conjugation ι U B) :=
  NormedSpace.map_exp (Unitary.conjStarAlgAut ℝ (Mat ι) U)
    (conjugation ι U).continuous B

omit [Nonempty ι] in
theorem realTrace_conjugation (U : Matrix.unitaryGroup ι ℂ) (B : Mat ι) :
    realTrace ι (conjugation ι U B) = realTrace ι B :=
  PreparedTraceForm.realTrace_unitary_conj ι U B

omit [Nonempty ι] in
theorem expDerivative_conjugation (U : Matrix.unitaryGroup ι ℂ) (B K : Mat ι) :
    expDerivative (conjugation ι U B) (conjugation ι U K) =
      conjugation ι U (expDerivative B K) := by
  have hleft := (exp_hasFDerivAt (conjugation ι U B)).comp B
    (conjugation ι U).hasFDerivAt
  have hright := (conjugation ι U).hasFDerivAt.comp B (exp_hasFDerivAt B)
  have heq := (hleft.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun X => conjugation_exp ι U X)).unique hright
  exact congrArg (fun f : Mat ι →L[ℝ] Mat ι => f K) heq

omit [Nonempty ι] in
theorem realTrace_diagonalDerivative (a : ι → ℝ) (K : Mat ι) :
    realTrace ι (diagonalDerivative a K) =
      realTrace ι (NormedSpace.exp (realDiagonal a) * K) := by
  apply congrArg Complex.re
  change (∑ i : ι, diagonalDerivative a K i i) =
    ∑ i : ι, (NormedSpace.exp (realDiagonal a) * K) i i
  apply Finset.sum_congr rfl
  intro i _
  rw [exp_realDiagonal]
  simp only [diagonalDerivative_apply, expDividedDifference_self,
    realDiagonal, Matrix.diagonal_mul, Complex.real_smul]

omit [Nonempty ι] in
/-- At a Hermitian base point the trace derivative has the usual cyclic form,
even when the matrix direction does not commute with that base point. -/
theorem realTrace_expDerivative {B : Mat ι} (hB : B.IsHermitian) (K : Mat ι) :
    realTrace ι (expDerivative B K) = realTrace ι (NormedSpace.exp B * K) := by
  let U := hB.eigenvectorUnitary
  let a := hB.eigenvalues
  have hspec : B = conjugation ι U (realDiagonal a) := by
    exact hB.spectral_theorem
  obtain ⟨L, rfl⟩ := conjugation_surjective ι U K
  rw [hspec, expDerivative_conjugation, realTrace_conjugation,
    expDerivative_realDiagonal, realTrace_diagonalDerivative]
  rw [← conjugation_exp, ← conjugation_mul, realTrace_conjugation]

def ambientTracePair : Mat ι →L[ℝ] (Mat ι →L[ℝ] ℝ) :=
  ((ContinuousLinearMap.compL ℝ (Mat ι) (Mat ι) ℝ)
    (realTrace ι).toContinuousLinearMap).comp (ContinuousLinearMap.mul ℝ (Mat ι))

omit [Nonempty ι] in
@[simp] theorem ambientTracePair_apply (B K : Mat ι) :
    ambientTracePair ι B K = realTrace ι (B * K) := rfl

def tracePair : Mat ι →L[ℝ] (Hermitian ι →L[ℝ] ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun B := (ambientTracePair ι B).comp (GibbsFiniteResponse.inclusion ι)
      map_add' B C := by
        apply ContinuousLinearMap.ext
        intro K
        simp only [ContinuousLinearMap.comp_apply, map_add, add_apply]
      map_smul' r B := by
        apply ContinuousLinearMap.ext
        intro K
        simp only [ContinuousLinearMap.comp_apply, map_smul, smul_apply, RingHom.id_apply] }

omit [Nonempty ι] in
@[simp] theorem tracePair_apply (B : Mat ι) (K : Hermitian ι) :
    tracePair ι B K = realTrace ι (B * (K : Mat ι)) := rfl

def traceExp (B : Mat ι) : ℝ := realTrace ι (NormedSpace.exp B)

omit [Nonempty ι] in
theorem traceExp_eq_complexTrace {B : Mat ι} (hB : B.IsHermitian) :
    (traceExp ι B : ℂ) = Matrix.trace (NormedSpace.exp B) :=
  PreparedTraceForm.trace_real ι hB.exp

omit [Nonempty ι] in
theorem traceExp_im_zero {B : Mat ι} (hB : B.IsHermitian) :
    (Matrix.trace (NormedSpace.exp B)).im = 0 := by
  have h := congrArg Complex.im (traceExp_eq_complexTrace ι hB)
  simpa only [Complex.ofReal_im] using h.symm

theorem traceExp_pos {B : Mat ι} (hB : B.IsHermitian) : 0 < traceExp ι B := by
  let U := hB.eigenvectorUnitary
  let a := hB.eigenvalues
  have hspec : B = conjugation ι U (realDiagonal a) := by
    exact hB.spectral_theorem
  change 0 < realTrace ι (NormedSpace.exp B)
  rw [hspec, ← conjugation_exp, realTrace_conjugation, exp_realDiagonal,
    PreparedTraceForm.realTrace_apply, realDiagonal, Matrix.trace_diagonal]
  change 0 < Complex.reAddGroupHom (∑ i : ι, (Real.exp (a i) : ℂ))
  rw [map_sum]
  exact Finset.sum_pos (fun i _ => Real.exp_pos (a i)) Finset.univ_nonempty

omit [Nonempty ι] in
theorem traceExp_hasFDerivAt {B : Mat ι} (hB : B.IsHermitian) :
    HasFDerivAt (traceExp ι) (ambientTracePair ι (NormedSpace.exp B)) B := by
  have h := (realTrace ι).toContinuousLinearMap.hasFDerivAt.comp B (exp_hasFDerivAt B)
  have heq : (realTrace ι).toContinuousLinearMap.comp (expDerivative B) =
      ambientTracePair ι (NormedSpace.exp B) := by
    apply ContinuousLinearMap.ext
    intro K
    exact realTrace_expDerivative ι hB K
  convert! h using 1
  exact heq.symm

omit [Fintype ι] [Nonempty ι] in
theorem realDiagonal_isHermitian (a : ι → ℝ) : (realDiagonal a).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  simp [isSelfAdjoint_iff]

/-- The unnormalized partition function on all Hermitian perturbations. -/
def partition (a : ι → ℝ) (K : Hermitian ι) : ℝ :=
  traceExp ι (realDiagonal a + (K : Mat ι))

omit [Nonempty ι] in
@[simp] theorem partition_apply (a : ι → ℝ) (K : Hermitian ι) :
    partition ι a K = realTrace ι (NormedSpace.exp (realDiagonal a + (K : Mat ι))) := rfl

theorem partition_pos (a : ι → ℝ) (K : Hermitian ι) : 0 < partition ι a K :=
  traceExp_pos ι
    ((realDiagonal_isHermitian ι a).add (PreparedTraceForm.hermitian_isHermitian ι K))

omit [Nonempty ι] in
theorem partition_eq_complexTrace (a : ι → ℝ) (K : Hermitian ι) :
    (partition ι a K : ℂ) =
      Matrix.trace (NormedSpace.exp (realDiagonal a + (K : Mat ι))) :=
  traceExp_eq_complexTrace ι
    ((realDiagonal_isHermitian ι a).add (PreparedTraceForm.hermitian_isHermitian ι K))

omit [Nonempty ι] in
theorem partition_im_zero (a : ι → ℝ) (K : Hermitian ι) :
    (Matrix.trace (NormedSpace.exp (realDiagonal a + (K : Mat ι)))).im = 0 :=
  traceExp_im_zero ι
    ((realDiagonal_isHermitian ι a).add (PreparedTraceForm.hermitian_isHermitian ι K))

omit [Nonempty ι] in
theorem partition_hasFDerivAt (a : ι → ℝ) (K : Hermitian ι) :
    HasFDerivAt (partition ι a)
      (tracePair ι (NormedSpace.exp (realDiagonal a + (K : Mat ι)))) K := by
  have hinput : HasFDerivAt
      (fun L : Hermitian ι => realDiagonal a + (L : Mat ι))
      (GibbsFiniteResponse.inclusion ι) K :=
    (GibbsFiniteResponse.inclusion ι).hasFDerivAt.const_add (realDiagonal a)
  exact (traceExp_hasFDerivAt ι
    ((realDiagonal_isHermitian ι a).add (PreparedTraceForm.hermitian_isHermitian ι K))).comp
      K hinput

omit [Nonempty ι] in
theorem partition_fderiv (a : ι → ℝ) (K : Hermitian ι) :
    fderiv ℝ (partition ι a) K =
      tracePair ι (NormedSpace.exp (realDiagonal a + (K : Mat ι))) :=
  (partition_hasFDerivAt ι a K).fderiv

end GeneratedFoundations.Operations.GibbsTraceDifferentiation
