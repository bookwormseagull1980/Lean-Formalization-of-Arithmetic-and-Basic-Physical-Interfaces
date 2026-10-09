module

public import GeneratedFoundations.Operations.GibbsTraceDifferentiation
public import GeneratedFoundations.Operations.GibbsTraceForm
public import GeneratedFoundations.Operations.SourcePreparedResponse
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The connected finite Gibbs response

Differentiating the trace gradient gives the second derivative of the
partition function on all Hermitian directions. The logarithm chain rule
then identifies the connected Hessian with the finite Gibbs trace form.
Its kernel is the scalar direction and its real rank is `N²-1`. The source
trace transports this response to the original Gaussian Hermite corner.
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology Matrix.Norms.Operator

namespace GeneratedFoundations.Operations.GibbsConnectedResponse

open PreparedTraceForm (Mat Hermitian Traceless realTrace)
open GibbsExponentialDifferentiation (realDiagonal diagonalDerivative)
open GibbsTraceDifferentiation (partition tracePair)

private theorem hasFDerivAt_clm_comp_dual
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : F →L[ℝ] E →L[ℝ] ℝ) {f : E → F} {f' : E →L[ℝ] F} {x : E}
    (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => L (f y)) (L.comp f') x :=
  L.hasFDerivAt.comp x hf

private theorem hasFDerivAt_smul_dual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {c : E → ℝ} {c' : E →L[ℝ] ℝ}
    {f : E → E →L[ℝ] ℝ} {f' : E →L[ℝ] E →L[ℝ] ℝ} {x : E}
    (hc : HasFDerivAt c c' x) (hf : HasFDerivAt f f' x) :
    HasFDerivAt (fun y => c y • f y) (c x • f' + c'.smulRight (f x)) x :=
  hc.smul hf

variable (ι : Type*) [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
theorem partition_zero (a : ι → ℝ) : partition ι a 0 = GibbsTraceForm.Z a := by
  change realTrace ι (NormedSpace.exp (realDiagonal a + 0)) = _
  rw [add_zero, GibbsExponentialDifferentiation.exp_realDiagonal,
    PreparedTraceForm.realTrace_apply, realDiagonal, Matrix.trace_diagonal]
  change Complex.reAddGroupHom (∑ i, (Real.exp (a i) : ℂ)) = ∑ i, Real.exp (a i)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

omit [Nonempty ι] in
theorem partition_fderiv_zero_apply (a : ι → ℝ) (K : Hermitian ι) :
    fderiv ℝ (partition ι a) 0 K = GibbsTraceForm.weightedTrace a (K : Mat ι) := by
  rw [GibbsTraceDifferentiation.partition_fderiv]
  change tracePair ι (NormedSpace.exp (realDiagonal a + 0)) K = _
  rw [add_zero, GibbsExponentialDifferentiation.exp_realDiagonal,
    GibbsTraceDifferentiation.tracePair_apply]
  rfl

def partitionHessian (a : ι → ℝ) : Hermitian ι →L[ℝ] Hermitian ι →L[ℝ] ℝ :=
  (tracePair ι).comp (GibbsFiniteResponse.responseDerivative ι a)

omit [Nonempty ι] in
theorem partition_fderiv_hasFDerivAt_zero (a : ι → ℝ) :
    HasFDerivAt (fderiv ℝ (partition ι a)) (partitionHessian ι a) 0 := by
  have hg : fderiv ℝ (partition ι a) =
      fun K => tracePair ι (GibbsFiniteResponse.response ι a K) := by
    funext K
    exact GibbsTraceDifferentiation.partition_fderiv ι a K
  rw [hg]
  simpa only [partitionHessian] using!
    hasFDerivAt_clm_comp_dual (E := Hermitian ι) (F := Mat ι)
      (L := by exact tracePair ι)
      (f := by exact GibbsFiniteResponse.response ι a)
      (f' := by exact GibbsFiniteResponse.responseDerivative ι a)
      (x := 0) (by exact GibbsFiniteResponse.response_hasFDerivAt_zero ι a)

omit [Nonempty ι] in
theorem partitionHessian_apply (a : ι → ℝ) (K L : Hermitian ι) :
    partitionHessian ι a K L = realTrace ι (diagonalDerivative a (K : Mat ι) *
      (L : Mat ι)) :=
  GibbsTraceDifferentiation.tracePair_apply ι (diagonalDerivative a (K : Mat ι)) L

def response (a : ι → ℝ) (K : Hermitian ι) : ℝ := Real.log (partition ι a K)

theorem response_hasFDerivAt (a : ι → ℝ) (K : Hermitian ι) :
    HasFDerivAt (response ι a)
      ((partition ι a K)⁻¹ • tracePair ι
        (NormedSpace.exp (realDiagonal a + (K : Mat ι)))) K :=
  (GibbsTraceDifferentiation.partition_hasFDerivAt ι a K).log
    (ne_of_gt (GibbsTraceDifferentiation.partition_pos ι a K))

theorem response_fderiv (a : ι → ℝ) (K : Hermitian ι) :
    fderiv ℝ (response ι a) K =
      (partition ι a K)⁻¹ • fderiv ℝ (partition ι a) K := by
  rw [(response_hasFDerivAt ι a K).fderiv,
    GibbsTraceDifferentiation.partition_fderiv]

def responseHessian (a : ι → ℝ) : Hermitian ι →L[ℝ] Hermitian ι →L[ℝ] ℝ :=
  (GibbsTraceForm.Z a)⁻¹ • partitionHessian ι a +
    (-(GibbsTraceForm.Z a ^ 2)⁻¹ • fderiv ℝ (partition ι a) 0).smulRight
      (fderiv ℝ (partition ι a) 0)

omit [Nonempty ι] in
theorem responseHessian_apply (a : ι → ℝ) (K L : Hermitian ι) :
    responseHessian ι a K L = GibbsTraceForm.gibbsForm a (K : Mat ι) (L : Mat ι) := by
  simp only [responseHessian, _root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul, partitionHessian_apply,
    partition_fderiv_zero_apply, GibbsTraceForm.gibbsForm_apply,
    GibbsTraceForm.mean_apply, div_eq_mul_inv]
  ring

/-- The derivative of the gradient is taken before applying the logarithm chain rule. -/
theorem response_fderiv_hasFDerivAt_zero (a : ι → ℝ) :
    HasFDerivAt (fderiv ℝ (response ι a)) (responseHessian ι a) 0 := by
  have hpart : HasFDerivAt (partition ι a) (fderiv ℝ (partition ι a) 0) 0 :=
    (GibbsTraceDifferentiation.partition_hasFDerivAt ι a 0).differentiableAt.hasFDerivAt
  have hne : partition ι a 0 ≠ 0 := by
    rw [partition_zero]
    exact GibbsTraceForm.Z_ne_zero a
  have hi : HasFDerivAt (fun K : Hermitian ι => (partition ι a K)⁻¹)
      (-(GibbsTraceForm.Z a ^ 2)⁻¹ • fderiv ℝ (partition ι a) 0) 0 := by
    simpa only [partition_zero, Function.comp_def] using!
      (hasDerivAt_inv hne).comp_hasFDerivAt 0 hpart
  have h : HasFDerivAt
      (fun K : Hermitian ι => (partition ι a K)⁻¹ • fderiv ℝ (partition ι a) K)
      (responseHessian ι a) 0 := by
    simpa only [partition_zero, responseHessian] using!
      hasFDerivAt_smul_dual hi (partition_fderiv_hasFDerivAt_zero ι a)
  have hg : fderiv ℝ (response ι a) =
      fun K => (partition ι a K)⁻¹ • fderiv ℝ (partition ι a) K := by
    funext K
    exact response_fderiv ι a K
  rw [hg]
  exact h

theorem response_hessian_apply (a : ι → ℝ) (K L : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι a)) 0 K L =
      GibbsTraceForm.gibbsForm a (K : Mat ι) (L : Mat ι) := by
  rw [(response_fderiv_hasFDerivAt_zero ι a).fderiv, responseHessian_apply]

theorem response_hessian_nonneg (a : ι → ℝ) (K : Hermitian ι) :
    0 ≤ fderiv ℝ (fderiv ℝ (response ι a)) 0 K K := by
  rw [response_hessian_apply]
  exact GibbsTraceForm.gibbsForm_nonneg a (PreparedTraceForm.hermitian_isHermitian ι K)

theorem response_hessian_self_eq_zero_iff (a : ι → ℝ) (K : Hermitian ι) :
    fderiv ℝ (fderiv ℝ (response ι a)) 0 K K = 0 ↔
      ∃ r : ℝ, (K : Mat ι) = r • (1 : Mat ι) := by
  rw [response_hessian_apply]
  exact GibbsTraceForm.gibbsForm_self_eq_zero_iff a
    (PreparedTraceForm.hermitian_isHermitian ι K)

theorem response_hessian_kernel_iff (a : ι → ℝ) (K : Hermitian ι) :
    (∀ L : Hermitian ι, fderiv ℝ (fderiv ℝ (response ι a)) 0 K L = 0) ↔
      ∃ r : ℝ, (K : Mat ι) = r • (1 : Mat ι) := by
  simp only [response_hessian_apply, GibbsTraceForm.gibbsForm_kernel_iff]

theorem response_hessian_traceless_pos (a : ι → ℝ) (K : Traceless ι) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (response ι a)) 0 K.val K.val := by
  rw [response_hessian_apply]
  exact GibbsTraceForm.gibbsForm_traceless_pos a K hK

theorem response_hessian_range_finrank (a : ι → ℝ) :
    Module.finrank ℝ (LinearMap.range (fderiv ℝ (fderiv ℝ (response ι a)) 0).toLinearMap) =
      (Fintype.card ι) ^ 2 - 1 := by
  let e : (Hermitian ι →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (Hermitian ι →L[ℝ] ℝ) :=
    LinearMap.toContinuousLinearMap
  have h : (responseHessian ι a).toLinearMap =
      e.toLinearMap.comp (GibbsTraceForm.hermitianForm a) := by
    apply LinearMap.ext
    intro K
    apply ContinuousLinearMap.ext
    intro L
    exact responseHessian_apply ι a K L
  rw [(response_fderiv_hasFDerivAt_zero ι a).fderiv, h, LinearMap.range_comp,
    e.finrank_map_eq]
  exact GibbsTraceForm.finrank_range_hermitianForm a

section GaussianNumber

variable {b : ℝ} (hb : 0 < b) (n : ℕ) (t : ℝ)

def sourceResponse (K : Hermitian (FiniteLadderAlgebra.Index n)) : ℝ :=
  Real.log ((SourceWeylPreparation.sourceTrace hb n
    (GibbsFiniteResponse.sourceResponse n t hb K)).re)

theorem sourceResponse_eq :
    sourceResponse hb n t = response (FiniteLadderAlgebra.Index n)
      (GibbsFiniteResponse.oscillatorWeights n t) := by
  funext K
  change Real.log ((SourceWeylPreparation.sourceTrace hb n
    (SourceWeylPreparation.corner hb n (GibbsFiniteResponse.oscillatorResponse n t K))).re) = _
  exact congrArg (fun z : ℂ => Real.log z.re)
    (SourceWeylPreparation.sourceTrace_corner hb n
      (GibbsFiniteResponse.oscillatorResponse n t K))

theorem sourceResponse_hessian (K L : Hermitian (FiniteLadderAlgebra.Index n)) :
    fderiv ℝ (fderiv ℝ (sourceResponse hb n t)) 0 K L =
      GibbsTraceForm.gibbsForm (GibbsFiniteResponse.oscillatorWeights n t)
        (K : FiniteLadderAlgebra.Mat n) (L : FiniteLadderAlgebra.Mat n) := by
  rw [sourceResponse_eq, response_hessian_apply]

theorem sourceResponse_hessian_nonneg (K : Hermitian (FiniteLadderAlgebra.Index n)) :
    0 ≤ fderiv ℝ (fderiv ℝ (sourceResponse hb n t)) 0 K K := by
  rw [sourceResponse_eq]
  exact response_hessian_nonneg (FiniteLadderAlgebra.Index n)
    (GibbsFiniteResponse.oscillatorWeights n t) K

theorem sourceResponse_hessian_kernel_iff (K : Hermitian (FiniteLadderAlgebra.Index n)) :
    (∀ L : Hermitian (FiniteLadderAlgebra.Index n),
      fderiv ℝ (fderiv ℝ (sourceResponse hb n t)) 0 K L = 0) ↔
      ∃ r : ℝ, SourceFiniteLadder.corner hb n (K : FiniteLadderAlgebra.Mat n) =
        r • SourceFiniteLadder.projection hb n := by
  rw [sourceResponse_eq, response_hessian_kernel_iff]
  exact exists_congr fun r =>
    (SourcePreparedResponse.corner_scalar_iff hb n (K : FiniteLadderAlgebra.Mat n) r).symm

theorem sourceResponse_hessian_traceless_pos
    (K : Traceless (FiniteLadderAlgebra.Index n)) (hK : K ≠ 0) :
    0 < fderiv ℝ (fderiv ℝ (sourceResponse hb n t)) 0 K.val K.val := by
  rw [sourceResponse_eq]
  exact response_hessian_traceless_pos (FiniteLadderAlgebra.Index n)
    (GibbsFiniteResponse.oscillatorWeights n t) K hK

theorem sourceResponse_hessian_range_finrank :
    Module.finrank ℝ
      (LinearMap.range (fderiv ℝ (fderiv ℝ (sourceResponse hb n t)) 0).toLinearMap) =
      (n + 1) ^ 2 - 1 := by
  rw [sourceResponse_eq, response_hessian_range_finrank]
  simp only [FiniteLadderAlgebra.Index, Fintype.card_fin]

end GaussianNumber

end GeneratedFoundations.Operations.GibbsConnectedResponse
