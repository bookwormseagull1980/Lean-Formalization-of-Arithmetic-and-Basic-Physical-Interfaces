module

public import GeneratedFoundations.Operations.GibbsExponentialDifferentiation
public import GeneratedFoundations.Operations.SourceFiniteLadder
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# Rank of the finite Gibbs response

The exponential response on Hermitian directions has injective real
derivative at each real diagonal reference. Its range therefore has real
dimension equal to the square of the matrix size. For the Gaussian number
reference this derivative embeds into the same finite Hermite corner.
-/

@[expose] public section

noncomputable section

open scoped Matrix.Norms.Operator
open GeneratedFoundations.Operations.SourceSpinCorner (End)

namespace GeneratedFoundations.Operations.GibbsFiniteResponse

open PreparedTraceForm (Mat Hermitian)
open GibbsExponentialDifferentiation (realDiagonal diagonalDerivative)

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

instance hermitianNormedSpace : NormedSpace ℝ (Hermitian ι) :=
  inferInstanceAs (NormedSpace ℝ (PreparedTraceForm.hermitianSubspace ι))

instance hermitianContinuousSMul : ContinuousSMul ℝ (Hermitian ι) :=
  inferInstanceAs (ContinuousSMul ℝ (PreparedTraceForm.hermitianSubspace ι))

def inclusion : Hermitian ι →L[ℝ] Mat ι :=
  (PreparedTraceForm.hermitianSubspace ι).subtypeL

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
@[simp] theorem inclusion_apply (K : Hermitian ι) : inclusion ι K = (K : Mat ι) := rfl

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem inclusion_injective : Function.Injective (inclusion ι) := Subtype.val_injective

def response (a : ι → ℝ) (K : Hermitian ι) : Mat ι :=
  NormedSpace.exp (realDiagonal a + (K : Mat ι))

def responseDerivative (a : ι → ℝ) : Hermitian ι →L[ℝ] Mat ι :=
  (diagonalDerivative a).comp (inclusion ι)

omit [Nonempty ι] in
theorem response_hasFDerivAt_zero (a : ι → ℝ) :
    HasFDerivAt (response ι a) (responseDerivative ι a) 0 := by
  have hinput : HasFDerivAt (fun K : Hermitian ι => realDiagonal a + (K : Mat ι))
      (inclusion ι) 0 :=
    (inclusion ι).hasFDerivAt.const_add (realDiagonal a)
  have hexp : HasFDerivAt NormedSpace.exp (diagonalDerivative a)
      (realDiagonal a + ((0 : Hermitian ι) : Mat ι)) := by
    change HasFDerivAt NormedSpace.exp (diagonalDerivative a) (realDiagonal a + 0)
    simpa only [add_zero] using
      GibbsExponentialDifferentiation.exp_realDiagonal_hasFDerivAt a
  exact hexp.comp (0 : Hermitian ι) hinput

omit [Nonempty ι] in
@[simp] theorem response_fderiv_zero (a : ι → ℝ) :
    fderiv ℝ (response ι a) 0 = responseDerivative ι a :=
  (response_hasFDerivAt_zero ι a).fderiv

omit [DecidableEq ι] [Nonempty ι] in
theorem responseDerivative_injective (a : ι → ℝ) :
    Function.Injective (responseDerivative ι a) :=
  (GibbsExponentialDifferentiation.diagonalDerivative_injective a).comp
    (inclusion_injective ι)

omit [DecidableEq ι] [Nonempty ι] in
theorem responseDerivative_apply (a : ι → ℝ) (K : Hermitian ι) (i j : ι) :
    responseDerivative ι a K i j =
      GibbsExponentialDifferentiation.expDividedDifference (a i) (a j) • (K : Mat ι) i j :=
  rfl

omit [DecidableEq ι] [Nonempty ι] in
theorem responseDerivative_range_finrank (a : ι → ℝ) :
    Module.finrank ℝ (LinearMap.range (responseDerivative ι a).toLinearMap) =
      (Fintype.card ι) ^ 2 :=
  (LinearMap.finrank_range_of_inj (responseDerivative_injective ι a)).trans
    (PreparedTraceForm.finrank_hermitian ι)

omit [Nonempty ι] in
theorem response_fderiv_range_finrank (a : ι → ℝ) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (response ι a) 0).toLinearMap) =
      (Fintype.card ι) ^ 2 := by
  rw [response_fderiv_zero]
  exact responseDerivative_range_finrank ι a

section GaussianNumber

variable (n : ℕ) (t : ℝ)

def oscillatorWeights : FiniteLadderAlgebra.Index n → ℝ := fun j => -t * (j.val : ℝ)

theorem oscillator_reference_eq :
    realDiagonal (oscillatorWeights n t) = (-t) • FiniteLadderAlgebra.number n := by
  rw [FiniteLadderAlgebra.number_eq_diagonal]
  ext i j
  by_cases h : i = j
  · subst j
    simp [realDiagonal, oscillatorWeights, Matrix.smul_apply, Complex.real_smul]
  · simp [realDiagonal, Matrix.smul_apply, h]

def oscillatorResponse : Hermitian (FiniteLadderAlgebra.Index n) →
    FiniteLadderAlgebra.Mat n :=
  response (FiniteLadderAlgebra.Index n) (oscillatorWeights n t)

theorem oscillatorResponse_apply (K : Hermitian (FiniteLadderAlgebra.Index n)) :
    oscillatorResponse n t K =
      NormedSpace.exp ((-t) • FiniteLadderAlgebra.number n +
        (K : FiniteLadderAlgebra.Mat n)) := by
  rw [oscillatorResponse, response, oscillator_reference_eq]

theorem oscillatorResponse_fderiv_range_finrank :
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (oscillatorResponse n t) 0).toLinearMap) = (n + 1) ^ 2 := by
  convert! response_fderiv_range_finrank (FiniteLadderAlgebra.Index n)
    (oscillatorWeights n t) using 1
  simp only [FiniteLadderAlgebra.Index, Fintype.card_fin]

variable {b : ℝ} (hb : 0 < b)

def sourceCorner : FiniteLadderAlgebra.Mat n →L[ℝ] End :=
  ((SourceFiniteLadder.corner hb n).restrictScalars ℝ).toContinuousLinearMap

@[simp] theorem sourceCorner_apply (K : FiniteLadderAlgebra.Mat n) :
    sourceCorner n hb K = SourceFiniteLadder.corner hb n K := rfl

theorem sourceCorner_injective : Function.Injective (sourceCorner n hb) :=
  FiniteHermiteCorner.corner_injective hb (SourceFiniteLadder.modes n)
    (SourceFiniteLadder.modes_injective n)

theorem source_reference_eq :
    sourceCorner n hb (realDiagonal (oscillatorWeights n t)) =
      (-t) • SourceFiniteLadder.compressedNumber hb n := by
  rw [oscillator_reference_eq, map_smul]
  rfl

def sourceResponse (K : Hermitian (FiniteLadderAlgebra.Index n)) : End :=
  sourceCorner n hb (oscillatorResponse n t K)

theorem sourceResponse_apply (K : Hermitian (FiniteLadderAlgebra.Index n)) :
    sourceResponse n t hb K = SourceFiniteLadder.corner hb n
      (NormedSpace.exp ((-t) • FiniteLadderAlgebra.number n +
        (K : FiniteLadderAlgebra.Mat n))) := by
  rw [sourceResponse, sourceCorner_apply, oscillatorResponse_apply]

def sourceDerivative : Hermitian (FiniteLadderAlgebra.Index n) →L[ℝ] End :=
  (sourceCorner n hb).comp
    (responseDerivative (FiniteLadderAlgebra.Index n) (oscillatorWeights n t))

theorem sourceResponse_hasFDerivAt_zero :
    HasFDerivAt (sourceResponse n t hb) (sourceDerivative n t hb) 0 :=
  (sourceCorner n hb).hasFDerivAt.comp (0 : Hermitian (FiniteLadderAlgebra.Index n))
    (response_hasFDerivAt_zero (FiniteLadderAlgebra.Index n) (oscillatorWeights n t))

@[simp] theorem sourceResponse_fderiv_zero :
    fderiv ℝ (sourceResponse n t hb) 0 = sourceDerivative n t hb :=
  (sourceResponse_hasFDerivAt_zero n t hb).fderiv

theorem sourceDerivative_injective : Function.Injective (sourceDerivative n t hb) :=
  (sourceCorner_injective n hb).comp
    (responseDerivative_injective (FiniteLadderAlgebra.Index n) (oscillatorWeights n t))

theorem sourceResponse_fderiv_range_finrank :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (sourceResponse n t hb) 0).toLinearMap) =
      (n + 1) ^ 2 := by
  rw [sourceResponse_fderiv_zero,
    LinearMap.finrank_range_of_inj (sourceDerivative_injective n t hb),
    PreparedTraceForm.finrank_hermitian]
  simp only [FiniteLadderAlgebra.Index, Fintype.card_fin]

end GaussianNumber

end GeneratedFoundations.Operations.GibbsFiniteResponse
